use std::collections::HashMap;
use std::ffi::OsStr;
use std::fmt::Debug;
use std::ops::Index;
use std::path::PathBuf;
use std::{fs, mem, vec, iter, ptr};

use crate::analysis::expression::BinaryOperator;
use crate::analysis::resources::ResourceKind;
use crate::ast::{self, FunctionKind, GenericParam};
use crate::parser::ParserError;
use crate::transpiler::ModuleTranspiler;
use crate::{lexer, parser, TranspileError};

use self::expression::{Expression, Type, TypeDefinition, TypeKind, UnaryOperator, MaybeTyped};
use self::resources::{FunctionHead, Resource, Scope, LocatedScope, Visibility, Variable, GLOBAL_SCOPE, MethodHead};

macro_rules! analysis_error {
    (NOERR $err:expr) => {{
        use $crate::analysis::AnalysisErrorKind::*;

        let kind: $crate::analysis::AnalysisErrorKind = $err;

        #[cfg(debug_assertions)]
        let err = $crate::analysis::AnalysisError {
            kind,
            source: $crate::analysis::DebugSource {
                file: file!(),
                loc: (line!(), column!()),
                trace: std::backtrace::Backtrace::force_capture()
            },
        };
        
        #[cfg(not(debug_assertions))]
        let err = $crate::analysis::AnalysisError { kind };
        
        err
    }};
    (PANIC $err:expr) => {{
        Err($crate::analysis::analysis_error!(NOERR $err)).unwrap()
    }};
    ($err:expr) => {{        
        Err($crate::analysis::analysis_error!(NOERR $err))
    }}
}
use analysis_error;


#[macro_use]
pub mod builtins;
pub mod resources;
pub mod expression;


#[derive(Debug, Clone)]
pub enum AnalysisErrorKind {
    UnknownBinaryOperator(lexer::TokenData),
    UnknownUnaryOperator(lexer::TokenData),
    UnknownResource{
        path: Vec<String>,
        found: Vec<ResourceKind>,
        failed_at: String,
    },
    UnsupportedBinaryOperation {
        op: BinaryOperator,
        left: Type,
        right: Type,
    },
    UnsupportedUnaryOperation {
        op: UnaryOperator,
        argument: Type,
    },
    UnexpectedType {
        expected: Type,
        found: Type,
    },
    NonExternVariadic {
        name: String,
    },
    StatementInWrongContext {
        statement: ast::Statement,
        found_context: &'static str,
    },
    UnknownIntegerSize {
        found: usize,
        expected: &'static [usize],
    },
    UnknownFloatSize {
        found: usize,
        expected: &'static [usize],
    },
    MemberAccessOnNonStruct {
        instance_type: Type,
        member: String,
    },
    UnknownMember {
        instance_type: Type,
        member: String,
    },
    #[allow(unused)]
    DuplicateStructMember {
        struct_name: String,
        duplicated_member: String,
    },
    MissingMemberInInit {
        struct_name: Vec<String>,
        missing: String,
    },
    AssignmentOnValue {
        value: Expression,
    },
    ParserError(Vec<ParserError>),
    DuplicateModuleFile {
        path: Vec<String>,
        files: (PathBuf, PathBuf),
    },
    RootModuleFileOutside {
        path: Vec<String>,
        file: PathBuf,
    },
    ResourceShadowing {
        name: String
    },
    WriteOnImmutableReference,
    MutRefOfImmutableValue {
        value: Expression
    },
    ExpectedMutableValue {
        value: Expression
    },
    EmptyReturn,
    ExternMethod {
        recv: Type,
        name: String
    },
    ExternGenerics {
        name: String,
        generics: Vec<ast::GenericParam>,
    },
    NotAStruct {
        found: Type,
    },
    AmbiguousOverloading {
        defined: FunctionHead,
        conflicting: FunctionHead
    },
    #[allow(unused)]
    AmbiguousCall {
        candidates: Vec<FunctionHead>,
    },
    InvalidArguments {
        expected: Vec<Vec<Type>>,
        found: Vec<Type>
    },
    NonLocalMethodDefinition {
        recv_type: Type,
        name: String
    }
}

pub struct DebugSource {
    loc: (u32, u32),
    file: &'static str,
    trace: std::backtrace::Backtrace
}

impl Debug for DebugSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}:{}:{}", self.file, self.loc.0, self.loc.1)?;
        writeln!(f, "backtrace: ")?;
        write ! (f, "{}", self.trace)
    }
}

#[derive(Debug)]
pub struct AnalysisError {
    kind: AnalysisErrorKind,
    #[cfg(debug_assertions)]
    #[allow(unused)]
    source: DebugSource
}

impl AnalysisError {
    fn with_member(self, member: String) -> Self {
        match self.kind {
            AnalysisErrorKind::NotAStruct { found } => Self {
                kind: AnalysisErrorKind::MemberAccessOnNonStruct {
                    instance_type: found,
                    member: member,
                },
                ..self
            },
            _ => self
        }
    }
}


#[derive(Clone, Debug)]
pub(crate) enum Statement {
    Expression(Expression),
    LetAssignment {
        name: String,
        value: Expression,
    },
    Assignment {
        lhs: Expression,
        rhs: Expression,
    },
    StructDeclaration {
        name: String,
    },
    If {
        conditions_and_bodies: Vec<(Expression, Vec<Statement>)>,
        else_body: Option<Vec<Statement>>,
    },
    While {
        condition: Expression,
        body: Vec<Statement>,
    },
    Return(Option<Expression>),
    Import(String),
}

#[derive(Debug, Clone)]
pub struct GenericFunction {
    pub(crate) generics: Vec<GenericParam>,

    pub(crate) head: FunctionHead,
    pub(crate) source: Vec<ast::Statement>,
    pub(crate) specializations: HashMap<Vec<Type>, FunctionScope>,
}

impl GenericFunction {
    fn specialize<'a>(&'a mut self, generic_arguments: Vec<Type>) -> Option<&'a FunctionScope> {
        if self.generics.len() != generic_arguments.len() {
            return None
        }

        let specialized_soruce = self.source.iter()
            .cloned().map(|s| self.specialize_statement(s, &generic_arguments)).collect();

        let specialized_head = self.specialize_head(&generic_arguments);

        let specialized_function = FunctionScope::new(specialized_soruce, specialized_head);

        

        self.specializations.insert(generic_arguments.clone(), specialized_function);

        Some(&self.specializations[&generic_arguments])
    }

    fn specialize_statement(&self, stmt: ast::Statement, generic_arguments: &[Type]) -> ast::Statement {
        match stmt {
            ast::Statement::Expression(expr) => ast::Statement::Expression(self.specialize_expression(expr, generic_arguments)),
            ast::Statement::LetAssignment { name, value } => {
                ast::Statement::LetAssignment {
                    name,
                    value: self.specialize_expression(value, generic_arguments),
                }
            }
            ast::Statement::Assignment { lhs, rhs } => {
                ast::Statement::Assignment {
                    lhs: self.specialize_expression(lhs, generic_arguments), 
                    rhs: self.specialize_expression(rhs, generic_arguments), 
                }
            }
            ast::Statement::If {
                conditions_and_bodies,
                else_body,
            } => {
                let conditions_and_bodies = conditions_and_bodies.into_iter()
                    .map(|(condition, body)| {(
                        self.specialize_expression(condition, generic_arguments), 
                        body.into_iter().map(|s| self.specialize_statement(s, generic_arguments)).collect()
                    )}).collect();

                let else_body = else_body
                    .map(|body| body.into_iter().map(|s| self.specialize_statement(s, generic_arguments)).collect());


                ast::Statement::If { conditions_and_bodies, else_body }
            }
            ast::Statement::While { condition, body } => {
                let condition = self.specialize_expression(condition, generic_arguments);

                let body = body.into_iter()
                    .map(|s| self.specialize_statement(s, generic_arguments)).collect();

                ast::Statement::While { condition, body }
            }
            ast::Statement::Return(expr) => {
                ast::Statement::Return(expr.map(|x| self.specialize_expression(x, generic_arguments)))
            }
            other @ (ast::Statement::FunctionDeclaration { .. }
            | ast::Statement::ExternFunctionDeclaration { .. }
            | ast::Statement::ExternBlock { .. }
            | ast::Statement::StructDeclaration { .. }
            | ast::Statement::Import { .. }) => analysis_error!(PANIC StatementInWrongContext {
                statement: other,
                found_context: "function body",
            }), // i cannot wait to finish this project asap
        }

    }

    fn specialize_expression(&self, expr: ast::Expression, generic_arguments: &[Type]) -> ast::Expression {
        match expr {
            ast::Expression::Binary { left, operator, right } => {
                ast::Expression::Binary {
                    left: Box::new(self.specialize_expression(*left, generic_arguments)),
                    operator, 
                    right: Box::new(self.specialize_expression(*right, generic_arguments))
                }
            },
            ast::Expression::Unary { operator, argument } => {
                ast::Expression::Unary { operator, argument: Box::new(self.specialize_expression(*argument, generic_arguments)) }
            },
            ast::Expression::ParenBlock(inner) => ast::Expression::ParenBlock(Box::new(self.specialize_expression(*inner, generic_arguments))),
            ast::Expression::FunctionCall { mut function, arguments } => {
                if function.len() == 1 {
                    for (param, arg) in iter::zip(&self.generics, generic_arguments) {
                        if param.name == function[0] {
                            function = match arg {
                                Type::Path(path) => path.clone(),
                                other => todo!("figure out what to do then")
                            };
                            break;
                        }
                    }
                }

                ast::Expression::FunctionCall {
                    function,
                    arguments: arguments.into_iter().map(|e| self.specialize_expression(e, generic_arguments)).collect()
                }
            },
            ast::Expression::MethodCall { instance, method, arguments } => {
                ast::Expression::MethodCall {
                    instance: Box::new(self.specialize_expression(*instance, generic_arguments)),
                    method,
                    arguments: arguments.into_iter().map(|e| self.specialize_expression(e, generic_arguments)).collect(),
                }
            },
            ast::Expression::StructMember { instance, member } => {
                ast::Expression::StructMember {
                    instance: Box::new(self.specialize_expression(*instance, generic_arguments)),
                    member
                }
            }, 
            ast::Expression::StructInit { mut path, members } => {
                if path.len() == 1 {
                    for (param, arg) in iter::zip(&self.generics, generic_arguments) {
                        if param.name == path[0] {
                            path = match arg {
                                Type::Path(path) => path.clone(),
                                other => todo!("figure out what to do then")
                            };
                            break;
                        }
                    }
                }

                ast::Expression::StructInit {
                    path: path,
                    members: members.into_iter().map(|(name, expr)| (
                        name,
                        self.specialize_expression(expr, generic_arguments)
                    )).collect(),
                }
            },
            ast::Expression::Variable(mut var) => {
                if var.len() == 1 {
                    for (param, arg) in iter::zip(&self.generics, generic_arguments) {
                        if param.name == var[0] {
                            var = match arg {
                                Type::Path(path) => path.clone(),
                                other => todo!("figure out what to do then")
                            };
                            break;
                        }
                    }
                }
                ast::Expression::Variable(var)
            },
            ast::Expression::Literal(lit) => ast::Expression::Literal(lit)
        }
    }

    fn specialize_type(&self, ty: ast::Type, generic_arguments: &[Type]) -> ast::Type {
        match ty {
            ast::Type::Void => ast::Type::Void,
            ast::Type::Path(mut path) => {
                if path.len() == 1 {
                    for (param, arg) in iter::zip(&self.generics, generic_arguments) {
                        if param.name == path[0] {
                            path = match arg {
                                Type::Path(path) => path.clone(),
                                other => todo!("figure out what to do then")
                            };
                            break;
                        }
                    }
                }
                ast::Type::Path(path)
            },
            ast::Type::Reference { inner, mutable } => {
                ast::Type::Reference { inner: Box::new(self.specialize_type(*inner, generic_arguments)), mutable }
            }
        }
    }

    fn specialize_head(&self, generic_arguments: &[Type]) -> FunctionHead {
        let head = &self.head;

        FunctionHead {
            generics: vec![],
            return_type: MaybeTyped::Untyped(self.specialize_type(head.return_type.untyped().clone(), generic_arguments)),
            arguments: head.arguments.iter().map(|(name, ty)| (
                name.clone(),
                MaybeTyped::Untyped(self.specialize_type(ty.untyped().clone(), generic_arguments))
            )).collect(),
            is_variadic: head.is_variadic,
            no_mangle: head.no_mangle,
        }
    }
}

#[derive(Debug, Clone)]
pub enum MaybeGeneric {
    Generic(GenericFunction),
    NonGeneric(FunctionScope)
}

#[derive(Clone, Debug)]
pub struct FunctionScope {
    pub(crate) head: FunctionHead,
    pub(crate) source: Vec<ast::Statement>,
    pub(crate) statements: Vec<Statement>,
    pub(crate) resources: HashMap<String, Vec<ResourceKind>>,
    pub(crate) module: *mut ModuleScope
}

impl FunctionScope {
    fn module(&self) -> &mut ModuleScope {
        unsafe {
            if self.module == ptr::null_mut() {
                panic!("attempt to access parent ModuleScope while FuntionScope did not have access it")
            } else {
                &mut *self.module
            }
        }
    }

    pub(crate) fn declaration_typing_pass(&mut self) -> Result<(), AnalysisError> {

        // SAFETY: module is set by the caller
        let module = unsafe { &*self.module };

        for (_, ty) in self.head.arguments.iter_mut() {
            ty.analyse(module)?;
        }

        self.head.return_type.analyse(module)?;

        self.resources.extend(
            self.head.arguments
            .iter()
            .cloned()
            .map(|(name, type_)| (name, vec![ResourceKind::Variable(Variable { mutable: true, type_: type_.typed().clone() })]))
        );

        Ok(())
    }

    fn execution_pass(&mut self) -> Result<(), AnalysisError> {
        let source = mem::take(&mut self.source);

        // TODO: accumulate errors in a vector to catch more than one error at compile time
        for stmt in source {
            let stmt = self.analyse_statement(stmt.clone())?;

            self.statements.push(stmt);
        }
        Ok(())
    }

    fn add_resource(&mut self, at: String, mut resource: ResourceKind) -> Result<(), AnalysisError> {
        use std::collections::hash_map::Entry;

        // borrowing rules! (or does it?)
        let unsafe_self = unsafe {&mut *(self as *mut _)};

        match self.resources.entry(at) {
            Entry::Vacant(x) => {
                x.insert(vec![resource]);
            },
            Entry::Occupied(mut x) => {
                match &mut resource {
                    ResourceKind::Alias(_)
                    | ResourceKind::Module(_)
                    => {
                        if x.get().iter().all(|r| matches!(r, ResourceKind::Method(_))) {
                            // methods are not real resources, no disambiguation required
                            x.get_mut().push(resource);
                        } else {
                            return analysis_error!(ResourceShadowing { name: x.key().clone() })
                        }
                    },
                    ResourceKind::Variable(var_to_insert) => {
                        // allow variable overloading in function scopes
                        
                        for res in x.get_mut() {
                            match res {
                                ResourceKind::Method(_) => (),
                                ResourceKind::Variable(old_var) => {
                                    mem::swap(old_var, var_to_insert)
                                },
                                _ => return analysis_error!(ResourceShadowing { name: x.key().clone() })
                            }
                        }
                    }
                    ResourceKind::Function(head) => {
                        for res in x.get() {
                            match &res {
                                ResourceKind::Function(existing_head) => {
                                    if existing_head.arguments.len() == head.arguments.len() {

                                        let is_similar = 
                                            iter::zip(&existing_head.arguments, &head.arguments)
                                            .map(|((name1, ty1), (name2, ty2))| ((name1, ty1.typed()), (name2, ty2.typed())))
                                            .all(|((_, existing), (_, new))| 
                                                   existing.coerce_method(unsafe_self, new).is_some() 
                                                || new.coerce_method(unsafe_self, existing).is_some()
                                            );

                                        if is_similar {
                                            return analysis_error!(AmbiguousOverloading {
                                                defined: head.clone(),
                                                conflicting: existing_head.clone()
                                            });
                                        }
                                    }
                                },
                                ResourceKind::Method(_) // methods are not real
                                | ResourceKind::Type(_) // to support constructors as plain functions
                                    => (),
                                ResourceKind::Alias     (_)
                                | ResourceKind::Module  (_) 
                                | ResourceKind::Variable(_) 
                                    => return analysis_error!(ResourceShadowing { name: x.key().clone() })
                            }
                        }
                        x.get_mut().push(resource);
                    },
                    ResourceKind::Method(_) => x.get_mut().push(resource),
                    _ => todo!()
                }
            }
        };

        Ok(())
    }


    fn analyse_statement(&mut self, stmt: ast::Statement) -> Result<Statement, AnalysisError> {
        match stmt {
            ast::Statement::Expression(expr) => Ok(Statement::Expression(self.type_expression(expr, false)?)),
            ast::Statement::LetAssignment { name, value } => {
                let rhs = self.type_expression(value, true)?;

                self.add_resource(name.clone(), ResourceKind::Variable(Variable {
                    type_: rhs.type_.clone(),
                    mutable: true
                }))?;
                Ok(Statement::LetAssignment {
                    name: name,
                    value: rhs,
                })
            }
            ast::Statement::Assignment { lhs, rhs } => {
                let lhs = self.type_expression(lhs, true)?;
                let lhs_ty = lhs.type_lhs(self)?;

                let rhs = self.type_expression(rhs, false)?
                    .coerce_to_new(self, &lhs_ty, false)?;

                Ok(Statement::Assignment { lhs, rhs })
            }
            ast::Statement::If {
                conditions_and_bodies,
                else_body,
            } => {
                let mut typed_conditions_and_bodies = vec![];
                for (condition, body) in conditions_and_bodies {
                    // TODO: invalidate variables that may not exist (let var = ... in if block)
                    let typed_condition = self.type_expression(condition, false)?
                        .coerce_to_new(self, &type_!(bool), false)?;

                    let mut inner = vec![];
                    for stmt in body {
                        inner.push(self.analyse_statement(stmt)?);
                    }
                    typed_conditions_and_bodies.push((typed_condition, inner))
                }

                match else_body {
                    Some(body) => {
                        let mut inner = vec![];
                        for stmt in body {
                            inner.push(self.analyse_statement(stmt)?);
                        }

                        Ok(Statement::If {
                            conditions_and_bodies: typed_conditions_and_bodies,
                            else_body: Some(inner),
                        })
                    }
                    None => Ok(Statement::If {
                        conditions_and_bodies: typed_conditions_and_bodies,
                        else_body: None,
                    }),
                }
            }
            ast::Statement::While { condition, body } => {
                let condition = self.type_expression(condition, false)?
                    .coerce_to_new(self, &type_!(bool), false)?;

                let mut inner = vec![];
                for stmt in body {
                    inner.push(self.analyse_statement(stmt)?);
                }

                Ok(Statement::While {
                    condition,
                    body: inner,
                })
            }
            ast::Statement::Return(expr) => {
                let head_return = self.head.return_type.typed();

                let expr = match expr {
                    Some(expr) => {
                        Some(
                            self.type_expression(expr, false)?
                                .coerce_to_new(self, head_return, false)?
                        )
                    }
                    None => {
                        if head_return != &type_!(void) {
                            return analysis_error!(EmptyReturn)
                        }
                        
                        None
                    }
                };

                Ok(Statement::Return(expr))
            }
            other @ (ast::Statement::FunctionDeclaration { .. }
            | ast::Statement::ExternFunctionDeclaration { .. }
            | ast::Statement::ExternBlock { .. }
            | ast::Statement::StructDeclaration { .. }
            | ast::Statement::Import { .. }) => analysis_error!(StatementInWrongContext {
                statement: other,
                found_context: "function body",
            }),
        }
    }

    fn new(source: Vec<ast::Statement>, head: FunctionHead) -> Self {
        // let resources = HashMap::from_iter(
        //     head.arguments
        //     .iter()
        //     .cloned()
        //     .map(|(name, type_)| (name.clone(), vec![ResourceKind::Variable(Variable { mutable: true, type_ })]))
        // );

        FunctionScope {
            head,
            source,
            statements: vec![],
            resources: HashMap::new(),
            module: ptr::null_mut()
        }
    }
}

#[derive(Clone)]
pub struct ModuleScope {
    pub(crate) file: PathBuf,
    pub(crate) path: Vec<String>,
    is_main: bool,

    source: Vec<ast::Statement>,
    pub(crate) statements: Vec<Statement>,
    pub(crate) declared_functions: Vec<(String, MaybeGeneric)>,
    pub(crate) declared_methods: Vec<(String, FunctionScope)>,
    pub(crate) resources: HashMap<String, Vec<Resource>>,
    pub(crate) externs: Vec<String>,
}

impl std::fmt::Debug for ModuleScope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<{}Module at \"{}\">", if self.is_main{"Main "}else{""}, self.path.join("."))
    }
}

impl ModuleScope {
    pub fn analyse(&mut self) -> Result<(), AnalysisError> {
        self.declaration_pass()?;
        self.declaration_typing_pass()?;
        self.method_inheritance_pass()?;
        self.execution_pass()?;

        Ok(())
    }

    pub(crate) fn declaration_pass(&mut self) -> Result<(), AnalysisError> {
        for stmt in self.source.clone() {
            match stmt {
                ast::Statement::FunctionDeclaration {
                    generics,
                    kind,
                    mut return_type,
                    mut arguments,
                    body,
                    is_variadic,
                    visibility
                } => {
                    match kind {
                        FunctionKind::Function(name) => {
                            if is_variadic {
                                return analysis_error!(NonExternVariadic { name });
                            }
                
                            let is_main = self.is_main && name == "main";
        
                            if is_main {
                                // implicitly return int if function is main
                                if return_type == ast::Type::Void {
                                    return_type = ast::Type::Path(vec!["int".to_string()]);
                                }
                            }

                            let has_generics = generics.len() != 0;
                                    
                            let head: FunctionHead = FunctionHead {
                                generics: generics.clone(),
                                return_type: MaybeTyped::Untyped(return_type),
                                arguments: arguments.into_iter().map(|(name, ty)| (name, MaybeTyped::Untyped(ty))).collect(),
                                is_variadic: None,
                                no_mangle: is_main
                            };

                            self.add_resource(name.clone(), Resource { kind: ResourceKind::Function(head.clone()), visibility })?;
                            
                            let func = if has_generics {
                                MaybeGeneric::Generic(GenericFunction { head, generics, source: body, specializations: HashMap::new() })
                            } else {
                                MaybeGeneric::NonGeneric(FunctionScope::new(body, head))
                            };
                            self.declared_functions.push((name, func));
                        }
                        FunctionKind::Method { receiver: (recv_name, recv_type), name: method_name } => {
                            if is_variadic {
                                return analysis_error!(NonExternVariadic { name: format!("({recv_type:?}).{method_name}") });
                            }

                            // a method is a function that takes its receiver as the first argument
                            arguments.insert(0, (recv_name, recv_type));

                            let head = FunctionHead {
                                generics,
                                return_type: MaybeTyped::Untyped(return_type),
                                arguments: arguments.into_iter().map(|(name, ty)| (name, MaybeTyped::Untyped(ty))).collect(),
                                is_variadic: None,
                                no_mangle: false
                            };

                            let func = FunctionScope::new(body, head.clone());

                            self.add_resource(method_name.clone(), Resource {
                                kind: ResourceKind::Method(MethodHead {
                                    head,
                                    source: self.path.clone()
                                }), 
                                visibility
                            })?;
                            self.declared_methods.push((method_name, func));
                        }
                    }
                }
                ast::Statement::ExternBlock { source, body } => {
                    for stmt in body {
                        match stmt {
                            ast::Statement::ExternFunctionDeclaration {
                                generics,
                                kind,
                                arguments,
                                return_type,
                                is_variadic,
                                visibility,
                            } => {
                                let name = match kind {
                                    FunctionKind::Function(name) => name,
                                    FunctionKind::Method { receiver: (_, recv), name } => return analysis_error!(ExternMethod { recv: self.analyse_type(recv)?, name })
                                };

                                if generics.len() != 0 {
                                    return analysis_error!(ExternGenerics { name, generics })
                                }

                                let func = FunctionHead {
                                    generics: vec![],
                                    return_type: MaybeTyped::Untyped(return_type),
                                    arguments: arguments.into_iter().map(|(name, ty)| (name, MaybeTyped::Untyped(ty))).collect(),
                                    is_variadic: Some(is_variadic),
                                    no_mangle: true
                                };

                                self.add_resource(name, Resource { kind: ResourceKind::Function(func), visibility })?;
                            }
                            _ => unreachable!(
                                "extern blocks should only contain body-less function declarations"
                            ),
                        }
                    }

                    self.externs.push(source)
                }
                ast::Statement::StructDeclaration { name, members, visibility } => {
                    self.add_resource(
                        name.clone(),
                        Resource { 
                            kind: ResourceKind::Type(TypeDefinition {
                                kind: TypeKind::Struct {    
                                    members: members.into_iter().map(|(name, ty)| (name, MaybeTyped::Untyped(ty))).collect(),
                                },
                                // TODO: operator overloading
                                // (or at least provide a default internal implementation for `==`)
                                binary_operations: HashMap::new(),
                                unary_operations: HashMap::new(),
                            }),
                            visibility
                        }
                    )?;
                    self.statements.push(Statement::StructDeclaration { name })
                }
                ast::Statement::Import { kind, visibility } => match kind {
                    ast::Import::Absolute(path) => self.add_alias(path, visibility)?,
                    ast::Import::Relative(name) => self.add_submodule(name, visibility)?,
                },
                other @ (ast::Statement::Expression(_)
                | ast::Statement::If { .. }
                | ast::Statement::While { .. }
                | ast::Statement::Return { .. }
                | ast::Statement::ExternFunctionDeclaration { .. }
                | ast::Statement::LetAssignment { .. }
                | ast::Statement::Assignment { .. }) => {
                    return analysis_error!(StatementInWrongContext {
                        statement: other,
                        found_context: "module",
                    })
                }
            }
        }
        Ok(())
    }

    pub(crate) fn declaration_typing_pass(&mut self) -> Result<(), AnalysisError> {
        let unsafe_self = unsafe { &*(self as *const Self) };


        for res in self.resources.values_mut() {
            for r in res {
                match &mut r.kind {
                    ResourceKind::Module(m) => {
                        m.declaration_typing_pass()?;
                    },
                    ResourceKind::Function(head) | ResourceKind::Method(MethodHead { head, .. }) => {
                        for (_, ty) in head.arguments.iter_mut() {
                            ty.analyse(unsafe_self)?;
                        }
                
                        head.return_type.analyse(unsafe_self)?;
                    },
                    ResourceKind::Type(TypeDefinition { kind: TypeKind::Struct { members }, .. }) => {
                        for (_, ty) in members {
                            ty.analyse(unsafe_self)?;
                        }
                    },
                    ResourceKind::Alias(path) => {
                        GLOBAL_SCOPE.get_resource_no_methods(path)?;
                    },
                    _ => {}
                }
            }
        }

        let mut declared_functions = mem::take(&mut self.declared_functions);

        for (_, func) in &mut declared_functions {
            if let MaybeGeneric::NonGeneric(func) = func {
                // SAFETY: func has exclusive access to self
                func.module = self as *mut _;
                func.declaration_typing_pass()?;
                // set pointer to null to revoke access to self
                func.module = ptr::null_mut();
            }
        }

        self.declared_functions = declared_functions;

        let mut declared_methods = mem::take(&mut self.declared_methods);

        for (name, func) in &mut declared_methods {
            // SAFETY: func has exclusive access to self
            func.module = self as *mut _;
            func.declaration_typing_pass()?;
            // set pointer to null to revoke access to self
            func.module = ptr::null_mut();

            let recv_type = func.head.arguments[0].1.typed();
            if let Some(path) = recv_type.definition_module() {
                if path != &self.path {
                    return analysis_error!(NonLocalMethodDefinition { recv_type: recv_type.clone(), name: name.clone() })
                }
            }
        }

        self.declared_methods = declared_methods;

        Ok(())
    }

    pub(crate) fn method_inheritance_pass(&mut self) -> Result<(), AnalysisError> {
        let unsafe_self = unsafe { &*(self as *const Self) };
        let mut inherited_methods = vec![];

        for res in self.resources.values_mut() {
            for r in res {
                match &mut r.kind {
                    ResourceKind::Module(m) => {
                        m.method_inheritance_pass()?;
                        for (name, res) in &m.resources {
                            for r in res {
                                if let ResourceKind::Method(meth) = &r.kind {
                                    // only inherit locally defined methods
                                    if meth.source == m.path {
                                        inherited_methods.push((name.clone(), meth.clone()));
                                    }
                                }    
                            }
                        }
                    },
                    ResourceKind::Alias(path) => {
                        let resources = GLOBAL_SCOPE.get_resource_no_methods(path).expect("aliases are validated in the declaration typing pass");

                        if let Some(module) = unsafe_self.extract_module(&resources) {
                            for (name, res) in &module.resources {
                                for r in res {
                                    if let ResourceKind::Method(meth) = &r.kind {
                                        // only inherit locally defined methods
                                        if &meth.source == path {
                                            inherited_methods.push((name.clone(), meth.clone()));
                                        }
                                    }    
                                }
                            }
                        }
                    },

                    _ => {}
                }
            }
        }

        for res in self.resources.values_mut() {
            for r in res {
                match &mut r.kind {
                    _ => {}
                }
            }
        }


        for (name, head) in inherited_methods {
            self.add_resource(name, Resource {
                kind: ResourceKind::Method(head), 
                visibility: Visibility::Module
            }).expect("adding a method into scope never fails");
        }

        Ok(())
    }

    pub(crate) fn execution_pass(&mut self) -> Result<(), AnalysisError> {
        let mut declared_functions = mem::take(&mut self.declared_functions);

        for (_, func) in &mut declared_functions {
            if let MaybeGeneric::NonGeneric(func) = func {
                // SAFETY: func has exclusive access to self
                func.module = self as *mut _;
                func.execution_pass()?;
                // set pointer to null to revoke access to self
                func.module = ptr::null_mut();
            }
        }

        self.declared_functions = declared_functions;

        let mut declared_methods = mem::take(&mut self.declared_methods);

        for (_, func) in &mut declared_methods {
            // SAFETY: func has exclusive access to self
            func.module = self as *mut _;
            func.execution_pass()?;
            // set pointer to null to revoke access to self
            func.module = ptr::null_mut();
        }

        self.declared_methods = declared_methods;

        for res in self.resources.values_mut() {
            for r in res {
                match &mut r.kind {
                    ResourceKind::Module(m) => {
                        m.execution_pass()?;
                    },
                    _ => {}
                }
            }
        }

        Ok(())
    }

    fn add_resource(&mut self, at: String, resource: Resource) -> Result<(), AnalysisError> {
        use std::collections::hash_map::Entry;

        match self.resources.entry(at) {
            Entry::Vacant(x) => {
                x.insert(vec![resource]);
            },
            Entry::Occupied(mut x) => {
                match &resource.kind {
                    ResourceKind::Alias(_)
                    | ResourceKind::Module(_)
                    | ResourceKind::Variable(_)
                    => {
                        if x.get().iter().all(|r| matches!(r.kind, ResourceKind::Method(_))) {
                            // methods are not real resources, no disambiguation required
                            x.get_mut().push(resource);
                        } else {
                            return analysis_error!(ResourceShadowing { name: x.key().clone() })
                        }
                    },
                    ResourceKind::Function(head) => {
                        for res in x.get() {
                            match &res.kind {
                                ResourceKind::Function(existing_head) => {
                                    if existing_head.arguments.len() == head.arguments.len() {
                                        /* TODO: check conflicts */
                                    }
                                },
                                ResourceKind::Method(_) // methods are not real
                                | ResourceKind::Type(_) // to support constructors as plain functions
                                    => (),
                                ResourceKind::Alias     (_)
                                | ResourceKind::Module  (_) 
                                | ResourceKind::Variable(_) 
                                    => return analysis_error!(ResourceShadowing { name: x.key().clone() })
                            }
                        }
                        x.get_mut().push(resource);
                    },
                    ResourceKind::Method(_) => x.get_mut().push(resource),
                    _ => todo!()
                }
            }
        };

        Ok(())
    }

    fn add_submodule(&mut self, end: String, visibility: Visibility) -> Result<(), AnalysisError> {
        let mut submodule = self.child(end.clone())?;

        submodule.declaration_pass()?;

        self.statements
            .push(Statement::Import(end.clone()));

        self.add_resource(end, Resource { kind: ResourceKind::Module(submodule), visibility })?;

        Ok(())
    }

    fn add_alias(&mut self, path: Vec<String>, visibility: Visibility) -> Result<(), AnalysisError> {
        self.add_resource(
            path.last().expect("path is not empty").clone(), 
            Resource {
                kind: ResourceKind::Alias(path),
                visibility 
            }
        )
    }

    // constructors
    pub fn main(root: PathBuf) -> Result<String, TranspileError> {
        let mut root = root
            .canonicalize()
            .map_err(|e| TranspileError::FileError(e))?;

        let package = root.file_stem().unwrap().to_str().unwrap().to_string();

        if let Some(ext) = root.extension() {
            if ext != OsStr::new("chi") {
                return Err(TranspileError::WrongExtension(root));
            }
        }

        let file = root.clone();

        root.pop();

        let source = parser::Parser::from_source(&fs::read_to_string(&file).unwrap())
            .parse()
            .map_err(|e| TranspileError::ParserError(e))?;

        let new = ModuleScope {
            path: vec![package.clone()],
            is_main: true,
            file,
            source,
            statements: vec![],
            resources: HashMap::new(),
            declared_functions: vec![],
            declared_methods: vec![],
            externs: vec![],
        };

        resources::PACKAGES.with(|p| p.insert(package.clone(), new));
        
        Ok(package)
    }

    pub(crate) fn child(&self, end: String) -> Result<Self, AnalysisError> {
        let ModuleScope {
            file,
            mut path,
            is_main,
            ..
        } = self.clone();

        path.push(end.clone());

        if !is_main
            && file.parent().unwrap().file_name().unwrap()
                != file.file_stem().expect("module file have a stem")
        {
            return analysis_error!(RootModuleFileOutside {
                path: path,
                file: file,
            });
        }

        let mut single_file_module = file.clone();

        single_file_module.pop();
        single_file_module.push(end.clone());
        single_file_module.set_extension("chi");

        let mut multiple_files_module_root = file.clone();
        multiple_files_module_root.pop();
        multiple_files_module_root.push(end.clone());
        multiple_files_module_root.push(end.clone());
        multiple_files_module_root.set_extension("chi");

        let single_exists = single_file_module.is_file();
        let multiple_exists = multiple_files_module_root.is_file();

        // module file resolution
        let file = if single_exists && multiple_exists {
            return analysis_error!(DuplicateModuleFile {
                path: path,
                files: (single_file_module, multiple_files_module_root),
            });
        } else if single_exists {
            single_file_module
        } else if multiple_exists {
            multiple_files_module_root
        } else {
            return analysis_error!(UnknownResource { path: path.clone(), found: vec![], failed_at: end })
        };

        let source = parser::Parser::from_source(&fs::read_to_string(&file).unwrap())
            .parse()
            .map_err(|e| analysis_error!(NOERR ParserError(e)))?;

        Ok(ModuleScope {
            file,
            path,
            is_main: false,
            source,
            statements: vec![],
            resources: HashMap::new(),
            declared_functions: vec![],
            declared_methods: vec![],
            externs: vec![],
        })
    }

    // post-analysis utilities
    pub fn transpile(&mut self, target_file: PathBuf) -> Result<(), TranspileError> {
        let transpiled = ModuleTranspiler::transpile(self);

        fs::write(target_file, transpiled.to_string()).map_err(|e| TranspileError::FileError(e))?;

        Ok(())
    }
}
