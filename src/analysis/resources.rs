use std::{cell::UnsafeCell, collections::HashMap, iter};
use crate::{analysis::expression::{UnaryOperator, ExpressionData, BinaryOperator}, ast::{self, Literal, GenericParam}};

use super::{ModuleScope, AnalysisError, expression::{Type, Expression, TypeDefinition, TypeKind, CoercionMethod, MaybeTyped}, FunctionScope};

pub(crate) trait Scope: Sized {
    // Required method
    fn get_local_resource(&self, child: &String) -> Option<Vec<&ResourceKind>>;

    fn get_resource(&self, path: &[String]) -> Result<Vec<&ResourceKind>, AnalysisError> {
        if path.len() == 1 {
            if let Some(res) = super::builtins::BUILTINS.get(&path[0]) {
                return Ok(res.iter().collect()); // convert &Vec<ResourceKind> to Vec<&ResourceKind>
            }
        }

        let mut path_iter = path.into_iter();

        let local = path_iter.next().expect("resource path is not empty");

        let mut resources = self.get_local_resource(local)
            .ok_or(analysis_error!(NOERR UnknownResource { path: path.into(), found: vec![], failed_at: local.clone() }))?;

        for p in path_iter {
            if let Some(alias) = self.extract_alias(&resources) {
                resources = GLOBAL_SCOPE.get_resource(alias)?;
            }
            
            if let Some(submodule) = self.extract_module(&resources) {
                resources = submodule.get_local_resource(p)
                    .ok_or(analysis_error!(NOERR UnknownResource { path: path.into(), found: vec![], failed_at: p.clone() }))?;
            } else if let Some(type_) = self.extract_type(&resources) {
                resources = type_.get_local_resource(p).ok_or(analysis_error!(NOERR UnknownResource { path: path.into(), found: vec![], failed_at: p.clone() }))?;
            } else { // Functions, methods & variables do not have children
                return analysis_error!(UnknownResource { path: path.to_vec(), found: resources.into_iter().cloned().collect(), failed_at: p.clone() })
            }
        }

        if let Some(alias) = self.extract_alias(&resources) {
            resources = GLOBAL_SCOPE.get_resource(alias)?;
        }

        Ok(resources)
    }

    fn get_resource_no_methods(&self, path: &[String]) -> Result<Vec<&ResourceKind>, AnalysisError> {
        let resources = self.get_resource(path)?;

        let no_methods = resources.into_iter().filter(|x| !matches!(x, ResourceKind::Method(_))).collect::<Vec<_>>();

        if !no_methods.is_empty() {
            Ok(no_methods)
        } else {
            analysis_error!(UnknownResource { path: path.into(), found: no_methods.into_iter().cloned().collect(), failed_at: path.last().expect("path is not empty").clone() })
        }
        
    }

    fn extract_function_head<'a>(&self, resources: &Vec<&'a ResourceKind>) -> Option<Vec<&'a FunctionHead>> {
        let heads = resources.into_iter().filter_map(|x| match x {
            ResourceKind::Function(func) => Some(func),
            _ => None
        }).collect::<Vec<_>>();

        if !heads.is_empty() {
            Some(heads)
        } else {
            None
        }

    }
    fn get_function_head(&self, path: &[String]) -> Result<FunctionsOrMethod, AnalysisError> {
        match self.get_resource(path) {
            Ok(resources) => {
                Ok(FunctionsOrMethod::Functions(
                    self.extract_function_head(&resources)
                        .ok_or_else(|| analysis_error!(NOERR UnknownResource { path: path.into(), found: resources.into_iter().cloned().collect(), failed_at: path.last().expect("path is not empty").clone() }))?
                    )
                )
            },
            Err(e) => {
                if path.len() == 1 {
                    return Err(e);
                }

                let instance = match self.get_variable(&path[..path.len()-1])? {
                    VariableOrAttribute::Variable(Variable { type_, mutable }) => Expression {
                        data: ExpressionData::Variable(path[..path.len()-1].into()),
                        type_: type_.clone(),
                        mutable: *mutable
                    },
                    VariableOrAttribute::Attribute(instance) => instance,
                };
                
                Ok(FunctionsOrMethod::Method {
                    instance,
                    method_name: path.last().expect("path is not empty").clone()
                })
        
            }
        }
        

    }

    fn extract_type<'a>(&self, resources: &Vec<&'a ResourceKind>) -> Option<&'a TypeDefinition> {
        resources.into_iter().filter_map(|x| match x {
            ResourceKind::Type(ty) => Some(ty),
            _ => None
        }).next()
    }
    fn get_type(&self, path: &[String]) -> Result<&TypeDefinition, AnalysisError> {
        let resources = self.get_resource(path)?;
        
        self.extract_type(&resources).ok_or(analysis_error!(NOERR UnknownResource { path: path.into(), found: resources.into_iter().cloned().collect(), failed_at: path.last().cloned().unwrap_or_default() }))
    }

    fn get_named_type(&self, type_: &Type) -> Result<&TypeDefinition, AnalysisError> {
        match type_ {
            Type::Path(path) => GLOBAL_SCOPE.get_type(path),
            _ => analysis_error!(NotAStruct { found: type_.clone() })
        }
    }

    fn extract_variable<'a>(&self, resources: &Vec<&'a ResourceKind>) -> Option<&'a Variable> {
        resources.into_iter().filter_map(|x| match x {
            ResourceKind::Variable(var) => Some(var),
            _ => None
        }).next()
    }

    fn get_variable(&self, path: &[String]) -> Result<VariableOrAttribute, AnalysisError> {
        // probably O(n²) where n = path.len()
        let mut resources = self.get_resource(&path[..=0])?;
        let mut variable_end = None;
        for index in 1..path.len() {
            if let Ok(res) = self.get_resource(&path[..index+1]) {
                resources = res;
            } else {
                variable_end = Some(index);
                break;
            }
        }

        match self.extract_variable(&resources) {
            Some(var) => {
                match variable_end {
                    None => Ok(VariableOrAttribute::Variable(var)),
                    Some(index) => {
                        let instance = Expression {
                            mutable: var.mutable,
                            type_: var.type_.clone(),
                            data: ExpressionData::Variable(path[..index].into()),
                        };
                        self.get_type_member(instance, &path[index..]).map(VariableOrAttribute::Attribute)
                    }
                }
            },
            None => return analysis_error!(UnknownResource { path: path.into(), found: resources.into_iter().cloned().collect(), failed_at: path.last().cloned().unwrap_or_default() })
        }
    }
    fn get_type_member(&self, mut instance: Expression, path: &[String]) -> Result<Expression, AnalysisError> {
        
        for p in path {
            instance = self.type_member_access(instance, p.clone())?;
        }

        Ok(instance)
    }

    fn extract_method_head<'a>(&self, resources: &Vec<&'a ResourceKind>) -> Option<Vec<&'a MethodHead>> {
        let heads = resources.into_iter().filter_map(|x: &&ResourceKind| match x {
            ResourceKind::Method(meth) => Some(meth),
            _ => None
        }).collect::<Vec<_>>();

        if !heads.is_empty() {
            Some(heads)
        } else {
            None
        }
    }
    fn get_method_head(&self, name: String) -> Result<Vec<&MethodHead>, AnalysisError> {
        let resources = &self.get_local_resource(&name)
            .ok_or_else(|| analysis_error!(NOERR UnknownResource { path: vec![name.clone()], found: vec![], failed_at: name.clone() }))?;


        Ok( self.extract_method_head(resources)
            .ok_or_else(|| analysis_error!(NOERR UnknownResource { failed_at: name.clone(), path: vec![name], found: resources.into_iter().cloned().cloned().collect() }))?
        )
    }

    fn extract_alias<'a>(&self, resources: &Vec<&'a ResourceKind>) -> Option<&'a Vec<String>> {
        resources.into_iter().filter_map(|x| match x {
            ResourceKind::Alias(path) => Some(path),
            _ => None
        }).next()
    }

    fn extract_module<'a>(&self, resources: &Vec<&'a ResourceKind>) -> Option<&'a ModuleScope> {
        resources.into_iter().filter_map(|x| match x {
            ResourceKind::Module(submodule) => Some(submodule),
            _ => None
        }).next()
    }
    fn get_module(&self, path: &[String]) -> Result<&ModuleScope, AnalysisError> {
        let resources = self.get_resource(path)?;
        
        self.extract_module(&resources).ok_or(analysis_error!(NOERR UnknownResource { path: path.into(), found: resources.into_iter().cloned().collect(), failed_at: path.last().cloned().unwrap_or_default() }))
    }

    fn type_member_access(&self, instance: Expression, member: String) -> Result<Expression, AnalysisError> {
        match &instance.type_ {
            Type::Void => analysis_error!(NotAStruct { found: Type::Void }),
            Type::Path(path) => {
                match GLOBAL_SCOPE.get_type(&path)
                        .map_err(|e| e.with_member(member.clone()))?.kind.clone() {
                    TypeKind::Struct { members } => {
                        // get the type of the member if it exists, otherwise return an error
                        let member_type = members
                            .get(&member)
                            .ok_or(analysis_error!(NOERR UnknownMember {
                                instance_type: Type::Path(path.clone()),
                                member: member.clone(),
                            }))?
                            .clone();

                        Ok(Expression {
                            mutable: instance.mutable,
                            data: ExpressionData::StructMember {
                                instance: Box::new(instance),
                                member,
                            },
                            type_: member_type.typed().clone(),
                        })
                    }
                    TypeKind::Primitive => analysis_error!(NotAStruct { found: Type::Path(path.clone()) }),
                }
            },
            Type::Reference { .. } => {
                let instance = CoercionMethod::Deref.apply(self, instance, true)?;

                self.type_member_access(instance, member)
            }
        }
    }
}

pub(crate) trait LocatedScope: Scope {
    fn path(&self) -> &[String];

    fn make_path_absolute(&self, path: Vec<String>) -> Result<Vec<String>, AnalysisError> {
        if path.len() == 1 {
            if super::builtins::BUILTINS.get(&path[0]).is_some() {
                return Ok(path);
            }
        }

        let mut absolute_path = Vec::with_capacity(path.len());

        let mut path_iter = path.iter().peekable();

        absolute_path.extend(self.path().iter().cloned());

        let start = path_iter.next().expect("resource path is not empty");
        let mut resources = self.get_local_resource(start)
            .ok_or_else(|| analysis_error!(NOERR UnknownResource { path: path.clone(), found: vec![], failed_at: path.last().cloned().unwrap_or_default() }))?;

        absolute_path.push(start.clone());

        if path_iter.peek().is_none() {

            while let Some(alias) = self.extract_alias(&resources) {
                absolute_path.clear();
                absolute_path.extend_from_slice(alias);

                resources = GLOBAL_SCOPE.get_resource(alias)?;
            }

            return Ok(absolute_path)
        }

        for p in path_iter {
            while let Some(alias) = self.extract_alias(&resources) {
                absolute_path.clear();
                absolute_path.extend_from_slice(alias);

                resources = GLOBAL_SCOPE.get_resource(alias)?;
            }
            absolute_path.push(p.clone());

            if let Some(submodule) = self.extract_module(&resources) {
                resources = submodule.get_local_resource(&p)
                    .ok_or_else(|| analysis_error!(NOERR UnknownResource { path: path.clone(), found: vec![], failed_at: p.clone() }))?;
            } else if let Some(type_) = self.extract_type(&resources) {
                resources = type_.get_local_resource(&p)
                    .ok_or_else(|| analysis_error!(NOERR UnknownResource { path: path.clone(), found: vec![], failed_at: p.clone() }))?;
            } else { // Functions and methods do not have children
                return analysis_error!(UnknownResource { path: path.clone(), found: resources.into_iter().cloned().collect(), failed_at: p.clone() })
            }
        }

        while let Some(alias) = self.extract_alias(&resources) {
            absolute_path.clear();
            absolute_path.extend_from_slice(alias);

            resources = GLOBAL_SCOPE.get_resource(alias)?;
        }

        Ok(absolute_path)

    }

    fn type_expression(&self, expr: ast::Expression, maybe_mutable: bool) -> Result<Expression, AnalysisError> {
        match expr {
            ast::Expression::Binary {
                left,
                operator,
                right,
            } => {
                let left = self.type_expression(*left, maybe_mutable)?;
                let right = self.type_expression(*right, maybe_mutable)?;

                use crate::lexer::TokenData;
                let operator = match operator {
                    TokenData::Plus => BinaryOperator::Plus,
                    TokenData::Minus => BinaryOperator::Minus,
                    TokenData::Star => BinaryOperator::Mul,
                    TokenData::Slash => BinaryOperator::Div,
                    TokenData::Equal => BinaryOperator::Equal,
                    TokenData::NotEqual => BinaryOperator::NotEqual,
                    TokenData::Greater => BinaryOperator::Greater,
                    TokenData::GreatorOrEqual => BinaryOperator::GreaterOrEqual,
                    TokenData::Lesser => BinaryOperator::Lesser,
                    TokenData::LesserOrEqual => BinaryOperator::LesserOrEqual,
                    other => return analysis_error!(UnknownBinaryOperator(other)),
                };
                match (&left.type_, &right.type_) {
                    (Type::Path(ltype), Type::Path(rtype)) => {
                        let ltypedef = self.get_type(ltype)?;
                        let rtypedef = self.get_type(rtype)?;

                        Ok(
                            match ltypedef.apply_binary(operator, Type::Path(rtype.clone()))
                            {
                                Some(type_) => Expression {
                                    data: ExpressionData::Binary {
                                        left: Box::new(left),
                                        operator,
                                        right: Box::new(right),
                                    },
                                    type_: type_.clone(),
                                    mutable: maybe_mutable
                                },
                                None => match rtypedef.apply_binary(operator, left.type_.clone()) {
                                    Some(type_) => Expression {
                                        data: ExpressionData::Binary {
                                            left: Box::new(left),
                                            operator,
                                            right: Box::new(right),
                                        },
                                        type_: type_.clone(),
                                        mutable: maybe_mutable
                                    },
                                    None => {
                                        return analysis_error!(UnsupportedBinaryOperation {
                                            op: operator,
                                            left: left.type_,
                                            right: right.type_,
                                        })
                                    }
                                },
                            },
                        )
                    }
                    (left, right) => analysis_error!(UnsupportedBinaryOperation {
                        op: operator,
                        left: left.clone(),
                        right: right.clone(),
                    }),
                }
            }
            ast::Expression::Unary { operator, argument } => {
                let argument = self.type_expression(*argument, true)?;

                use crate::lexer::TokenData;
                let operator = match operator {
                    TokenData::Plus => UnaryOperator::Plus,
                    TokenData::Minus => UnaryOperator::Minus,
                    TokenData::Not => UnaryOperator::Not,
                    TokenData::Ref => UnaryOperator::Ref,
                    TokenData::MutRef => UnaryOperator::MutRef,
                    TokenData::Star => UnaryOperator::Deref,
                    other => return analysis_error!(UnknownUnaryOperator(other)),
                };

                match (argument.type_.clone(), operator) {
                    (arg_type, UnaryOperator::Ref) => Ok(Expression {
                        data: ExpressionData::Unary {
                            operator: UnaryOperator::Ref,
                            argument: Box::new(argument),
                        },
                        type_: Type::Reference {
                            inner: Box::new(arg_type),
                            mutable: false,
                        },
                        mutable: false
                    }),
                    (arg_type, UnaryOperator::MutRef) => {
                        if !argument.mutable {
                            return analysis_error!(MutRefOfImmutableValue { value: argument })
                        }

                        Ok(Expression {
                            data: ExpressionData::Unary {
                                operator: UnaryOperator::Ref,
                                argument: Box::new(argument),
                            },
                            type_: Type::Reference {
                                inner: Box::new(arg_type),
                                mutable: maybe_mutable,
                            },
                            mutable: maybe_mutable
                        })
                    },
                    (Type::Path(path), _) => {
                        let arg_type = self.get_type(&path)?;
                        match arg_type.apply_unary(operator) {
                            Some(ty) => Ok(Expression {
                                data: ExpressionData::Unary {
                                    operator,
                                    argument: Box::new(argument),
                                },
                                type_: ty.clone(),
                                mutable: maybe_mutable
                            }),
                            None => analysis_error!(UnsupportedUnaryOperation {
                                op: operator,
                                argument: Type::Path(path),
                            }),
                        }
                    }
                    (Type::Reference{inner, mutable}, UnaryOperator::Deref) => Ok(Expression {
                        data: ExpressionData::Unary {
                            operator: UnaryOperator::Deref,
                            argument: Box::new(argument),
                        },
                        type_: *inner,
                        mutable: maybe_mutable && mutable,
                    }),
                    (argument, op) => analysis_error!(UnsupportedUnaryOperation { op, argument })
                }
            }
            ast::Expression::ParenBlock(inner) => {
                let inner = self.type_expression(*inner, maybe_mutable)?;
                let type_ = inner.type_.clone();
                Ok(Expression {
                    mutable: inner.mutable,
                    data: ExpressionData::ParenBlock(Box::new(inner)),
                    type_,
                })
            }
            ast::Expression::FunctionCall {
                function: function_name,
                arguments,
            } => {
                match self.get_function_head(&function_name)? {
                    FunctionsOrMethod::Functions(overloaded_functions) => {
                        let mut typed_args = vec![];
                        for arg in arguments {
                            typed_args.push(self.type_expression(arg, true)?);
                        }

                        let (_, function, coerced_args) = self.select_overload(&overloaded_functions, typed_args, false)?;

                        let path = self.make_path_absolute(function_name)?;
        
                        Ok(Expression {
                            data: ExpressionData::FunctionCall {
                                head: function.clone(),
                                function: path,
                                arguments: coerced_args,
                            },
                            type_: function.return_type.typed().clone(),
                            mutable: maybe_mutable
                        })
                    },
                    FunctionsOrMethod::Method { instance, method_name } 
                        => self.type_method_call(instance, method_name, arguments, maybe_mutable)
                }
            }
            ast::Expression::MethodCall { instance, method, arguments } => {
                let instance = self.type_expression(*instance, true)?;

                self.type_method_call(instance, method, arguments, maybe_mutable)
            },
            ast::Expression::Variable(name) => Ok(match self.get_variable(&name)? {
                VariableOrAttribute::Variable(var) => Expression {
                    data: ExpressionData::Variable(name),
                    type_: var.type_.clone(),
                    mutable: maybe_mutable && var.mutable
                },
                VariableOrAttribute::Attribute(expr) => expr,
            }),
            ast::Expression::StructMember { instance, member } => {
                let instance = self.type_expression(*instance, maybe_mutable)?;
                self.type_member_access(instance, member)
            }
            ast::Expression::StructInit { path, mut members } => {
                let ty = self.get_type(&path)?;
                let path = self.make_path_absolute(path)?;

                let TypeKind::Struct { members: decl_members } = ty.kind.clone()
                    else { return analysis_error!(NotAStruct { found: Type::Path(path) }) };

                let mut typed_members = HashMap::new();

                for (m_name, m_type) in decl_members {
                    let value = members
                        .get(&m_name)
                        .ok_or(analysis_error!(NOERR MissingMemberInInit {
                            struct_name: path.clone(),
                            missing: m_name.clone(),
                        }))?
                        .clone();

                    // TODO: ownership
                    members.remove(&m_name);

                    typed_members.insert(
                        m_name, 
                        self.type_expression(value, maybe_mutable)?
                            .coerce_to_new(self, m_type.typed(), false)?
                    );
                }

                if !members.is_empty() {
                    return analysis_error!(UnknownMember {
                        instance_type: Type::Path(path),
                        member: members.into_keys().next().expect("members is not empty"),
                    });
                }

                Ok(Expression {
                    data: ExpressionData::StructInit {
                        path: path.clone(),
                        members: typed_members,
                    },
                    type_: Type::Path(path.clone()),
                    mutable: true
                })
            }
            ast::Expression::Literal(lit) => self.type_literal(lit),
        }
    }

    fn analyse_type(&self, ty: ast::Type) -> Result<Type, AnalysisError> {
        Ok(match ty {
            ast::Type::Void => Type::Void,
            ast::Type::Path(name) => {
                self.get_type(&name)?;
                Type::Path(self.make_path_absolute(name)?)
            }
            ast::Type::Reference { inner, mutable } => Type::Reference {
                inner: Box::new(self.analyse_type(*inner)?),
                mutable: mutable
            },
        })
    }

    fn type_literal(&self, value: Literal) -> Result<Expression, AnalysisError> {
        let type_ = match &value {
            Literal::String(_) => type_!(str),
            Literal::Integer {
                value: _,
                signed,
                size,
            } => match size {
                None => {
                    if *signed {
                        type_!(int)
                    } else {
                        type_!(uint)
                    }
                }
                Some(8) => {
                    if *signed {
                        type_!(int8)
                    } else {
                        type_!(uint8)
                    }
                }
                Some(16) => {
                    if *signed {
                        type_!(int16)
                    } else {
                        type_!(uint16)
                    }
                }
                Some(32) => {
                    if *signed {
                        type_!(int32)
                    } else {
                        type_!(uint32)
                    }
                }
                Some(64) => {
                    if *signed {
                        type_!(int64)
                    } else {
                        type_!(uint64)
                    }
                }
                Some(other) => {
                    return analysis_error!(UnknownIntegerSize {
                        found: *other,
                        expected: &[8, 16, 32, 64],
                    })
                }
            },
            Literal::Float { value: _, size } => match size {
                None => type_!(float),
                Some(32) => type_!(float32),
                Some(64) => type_!(float64),
                Some(other) => {
                    return analysis_error!(UnknownFloatSize {
                        found: *other,
                        expected: &[32, 64],
                    })
                }
            },
            Literal::Null => type_!(&void),
            Literal::False | Literal::True => type_!(bool),
        };

        Ok(Expression {
            data: ExpressionData::Literal(value),
            type_,
            mutable: true
        })
    }

    fn type_method_call(&self, instance: Expression, method: String, arguments: Vec<ast::Expression>, maybe_mutable: bool) -> Result<Expression, AnalysisError> {

        let overloaded_methods = self.get_method_head(method.clone()).unwrap_or_default();
        let overloaded_heads = overloaded_methods.iter().map(|x| &x.head).collect::<Vec<_>>();

        let mut typed_args = vec![instance];
        for arg in arguments {
            typed_args.push(self.type_expression(arg, true)?)
        }

        let definition_module = typed_args[0].type_.definition_module()
            .map(|x| GLOBAL_SCOPE.get_module(x)
                .expect("definition module of receiver type exists"));


        let intrinsic_overloaded_methods = definition_module.map(|x| x.get_method_head(method.clone()));

        let (head, coerced_args) = match self.select_overload(&overloaded_heads, typed_args.clone(), true) {
            Ok(x) => {
                let (id, _, coerced_args) = x;
                let head = overloaded_methods[id].clone();

                (head, coerced_args)
            },
            Err(e) => {
                let Some(intrinsic_overloaded_methods) = intrinsic_overloaded_methods else {
                    return Err(e)
                };

                let intrinsic_overloaded_methods = intrinsic_overloaded_methods?;

                let intrinsic_overloaded_heads = intrinsic_overloaded_methods.iter().map(|x| &x.head).collect::<Vec<_>>();

                let x = self.select_overload(&intrinsic_overloaded_heads, typed_args, true)?;

                let (id, _, coerced_args) = x;
                let head = intrinsic_overloaded_methods[id].clone();

                (head, coerced_args)
            }
        };
    

        Ok(Expression {
            type_: head.head.return_type.typed().clone(),

            data: ExpressionData::MethodCall {
                head,
                method,
                arguments: coerced_args,
            },
            mutable: maybe_mutable
        })

    }
    
    fn select_overload<'a>(&'a self, overloaded_functions: &'a [&FunctionHead], typed_args: Vec<Expression>, is_method: bool) -> Result<(usize, &FunctionHead, Vec<Expression>), AnalysisError> {
        let arg_n = typed_args.len();

        let mut candidates = vec![];
        'overloaded_loop: for (id, function) in overloaded_functions.iter().enumerate() {
            let func_args = function.arguments.iter()
                .map(|(name, ty)| (name, ty.typed()) ).collect::<Vec<_>>();

            let mut coercions = vec![];
            if let Some(true) = function.is_variadic {
                if function.arguments.len() > arg_n {
                    continue 'overloaded_loop;
                }

                for (index, found) in typed_args.iter().enumerate() {


                    match func_args.get(index) {
                        Some(expected) => {
                            let should_be_mutable = true;

                            let coercion = match found.type_.coerce_method(self, &expected.1) {
                                Some(way) => way,
                                None => continue 'overloaded_loop,
                            };

                            coercions.push((coercion, Some(should_be_mutable)))
                        }
                        None => {
                            // we cannot coerce the argument because the parameter is variadic
                            coercions.push((CoercionMethod::None, None))
                        }
                    }
                }
            } else {
                if function.arguments.len() != arg_n {
                    continue;
                }

                for (expected, found) in std::iter::zip(func_args, &typed_args) {
                    // TODO: ownership
                    let should_be_mutable = true;
                    
                    let coercion = match found.type_.coerce_method(self, &expected.1) {
                        Some(way) => way,
                        None => continue 'overloaded_loop,
                    };
                    
                    coercions.push((coercion, Some(should_be_mutable)))
                }
            
            }
        
            candidates.push((id, function, coercions))
        }

        let (id, function, coercions) = match candidates.len() {
            0 => return analysis_error!(InvalidArguments { 
                expected: overloaded_functions.into_iter().cloned()
                    .map(|x| x.arguments.iter().map(|(_, ty)| ty.typed()).cloned().collect())
                    .collect(), 
                found: typed_args.into_iter().map(|x| x.type_).collect()
            }),
            1 => candidates.pop().expect("candidates' length is 1"),
            _ => todo!("solve non-trivial function overloading - candidates are {candidates:#?}")
        };

        let mut first = true;
        let mut coerced_args = vec![];
        for (arg, (coercion, _)) in iter::zip(typed_args, coercions) {
            coerced_args.push(coercion.apply(self, arg, first && is_method)?);
            first = false;
        }

        Ok((id, function, coerced_args))

    }
}

impl Scope for ModuleScope {
    fn get_local_resource(&self, child: &String) -> Option<Vec<&ResourceKind>> {
        Some(self.resources.get(child)?.iter().map(|x| &x.kind).collect())
    }
}

impl LocatedScope for ModuleScope {
    fn path(&self) -> &[String] {
        &self.path
    }
}

impl Scope for FunctionScope {
    fn get_local_resource(&self, child: &String) -> Option<Vec<&ResourceKind>> {
        match self.resources.get(child) {
            None => self.module().get_local_resource(child),
            Some(local_resources) => {
                let mut local_resources = local_resources.into_iter().collect::<Vec<_>>();

                let parent_resources = match self.module().get_local_resource(child) {
                    Some(r) => r,
                    None => return Some(local_resources)
                };

                let mut main_resource_exists = false;

                if let Some(_) = self.extract_module(&local_resources) {
                    main_resource_exists = true;
                } else if let Some(_) = self.extract_type(&local_resources) {
                    main_resource_exists = true;
                } else if let Some(_) = self.extract_variable(&local_resources) {
                    main_resource_exists = true;
                } else if let Some(_) = self.extract_alias(&local_resources) {
                    main_resource_exists = true;
                } else if !self.extract_function_head(&local_resources).is_some() {
                    main_resource_exists = true;
                }

                if main_resource_exists {
                    local_resources.extend(parent_resources.into_iter().filter(|x| matches!(x, ResourceKind::Method{..})))
                } else {
                    local_resources.extend_from_slice(&parent_resources)
                }

                Some(local_resources)
            },
            
        }
    }
}

impl LocatedScope for FunctionScope {
    fn path(&self) -> &[String] {
        &self.module().path
    }
}

impl Scope for TypeDefinition {
    fn get_local_resource(&self, child: &String) -> Option<Vec<&ResourceKind>> {
        todo!("static methods (called with {child})")
    }
}

// I know this is really bad but I don't care
pub(crate) struct GlobalPackage(pub(crate) UnsafeCell<HashMap<String, ResourceKind>>);

impl GlobalPackage {
    fn new() -> Self {
        GlobalPackage(UnsafeCell::new(HashMap::new()))
    }
    
    pub fn get_res(&self, k: &String) -> Option<&ResourceKind> {
        unsafe { &*self.0.get() }.get(k)
    }

    pub fn get_mut(&self, k: &String) -> Option<&mut ModuleScope> {
        match self.get_res_mut(k)? {
            ResourceKind::Module(m) => Some(m),
            _ => unreachable!("resources stored in global package should a module")
        }
    }
    
    pub fn get_res_mut(&self, k: &String) -> Option<&mut ResourceKind> {
        unsafe { &mut *self.0.get() }.get_mut(k)
    }

    pub fn insert(&self, k: String, v: ModuleScope) {
        unsafe { &mut *self.0.get() }.insert(k, ResourceKind::Module(v));
    }
}

// look, I tried everything but this is the simplest solution
// I am NOT using RwLock<HashMap<String, Arc<RwLock<ModuleScope>>>>
thread_local! {
    pub(crate) static PACKAGES: GlobalPackage = GlobalPackage::new();
}

pub struct GlobalScope;

pub static GLOBAL_SCOPE: GlobalScope = GlobalScope;

impl Scope for GlobalScope {
    fn get_local_resource(&self, child: &String) -> Option<Vec<&ResourceKind>> {
        PACKAGES.with(|p| 
            p.get_res(child)
            .map(|m| vec![m])
            .map(|x| x.into_iter().map(|y| unsafe { &*(y as *const _) }).collect()) // lifetimes!
        )
    }
}

#[derive(Clone, Debug)]
pub struct FunctionHead {
    pub(crate) generics: Vec<GenericParam>,
    pub(crate) return_type: MaybeTyped,
    pub(crate) arguments: Vec<(String, MaybeTyped)>,
    pub(crate) is_variadic: Option<bool>,
    pub(crate) no_mangle: bool
}

impl FunctionHead {
    fn is_generic(&self, ty: ast::Type) -> bool {
        use ast::Type;
        match ty {
            Type::Path(path) => {
                if path.len() != 1 {
                    return false
                }

                for g in &self.generics {
                    if g.name == path[0] {
                        return true;
                    }
                }

                return false;
            },
            Type::Void => false,
            Type::Reference { inner, .. } => self.is_generic(*inner)
        }
    }
}

pub(crate) enum VariableOrAttribute<'a> {
    Variable(&'a Variable),
    Attribute(Expression),
}

pub(crate) enum FunctionsOrMethod<'a> {
    Functions(Vec<&'a FunctionHead>),
    Method {
        instance: Expression,
        method_name: String
    },
}

#[derive(Debug, Clone)]
pub struct Variable {
    pub(crate) type_: Type,
    pub(crate) mutable: bool,
}

#[derive(Debug, Clone)]
pub struct MethodHead {
    pub head: FunctionHead,
    pub source: Vec<String>
}

#[derive(Debug, Clone)]
pub enum ResourceKind {
    Function(FunctionHead),
    Method(MethodHead),
    Type(TypeDefinition),
    #[allow(dead_code)]
    Variable(Variable),
    Module(ModuleScope),
    Alias(Vec<String>),
}

// this is safe because fuck rust
// and also because most of the time a ModuleScope contains a null pointer
unsafe impl Sync for ResourceKind {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Visibility {
    Public,
    Module,
}

impl Default for Visibility {
    fn default() -> Self {
        // TODO: make resources private by default
        Visibility::Public
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Resource {
    pub kind: ResourceKind,
    #[allow(dead_code)]
    pub visibility: Visibility
}
