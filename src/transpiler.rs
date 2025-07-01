use std::{collections::{HashMap, HashSet}, fmt::Display};

use crate::{
    analysis::{ModuleScope, Statement, resources::{Scope, FunctionHead, Resource, ResourceKind, LocatedScope}, expression::{TypeKind, ExpressionData, Type}, MaybeGeneric},
    ast::Literal,
};

pub(crate) struct ModuleTranspiler<'a> {
    indent: usize,
    scope: &'a ModuleScope,
    shadowed_variables: HashMap<String, usize>,
    includes: HashSet<String>,
    global_variables: Vec<String>,
    functions: Vec<(String, String)>, // declaration-body pairs
    structs: Vec<(String, String)>, // name-body pairs
}

impl<'a> ModuleTranspiler<'a> {

    pub fn transpile(
        scope: &'a ModuleScope,
    ) -> ModuleTranspiler<'a> { 
        let mut new = ModuleTranspiler {
            indent: 0,
            scope,
            shadowed_variables: HashMap::new(),
            includes: HashSet::from([
                "<stddef.h>".to_string(),
                "<stdbool.h>".to_string(),
                "<stdint.h>".to_string(),
            ]),
            global_variables: vec![],
            functions: vec![],
            structs: vec![]
        };

        // TODO: lazily add includes (e.g. include stddef.h only when NULL is used)
        for ext in &new.scope.externs {
            new.includes.insert(if ext.starts_with('<') && ext.ends_with('>') { ext.clone() } else { format!("\"{}\"", ext) });
        }

        for (name, func) in &new.scope.declared_functions {
            let funcs = match func {
                MaybeGeneric::NonGeneric(func) => {
                    vec![func]
                },
                MaybeGeneric::Generic(gfun) => {
                    gfun.specializations.values().collect()
                }
            };
            for func in funcs {
                let head_args = func.head.arguments.iter().map(|(name, ty)| (name, ty.typed()));
            
                let mut args = head_args
                    .map(|(name, type_)| {
                        new.shadowed_variables.insert(name.clone(), 0);
                        new.transpile_declaration(type_, name)
                    })
                    .collect::<Vec<String>>()
                    .join(", ");
    
                if args.is_empty() {
                    args = "void".to_string();
                }
                
                let func_name = if func.head.no_mangle {
                    name.clone()
                } else {
                    new.mangle_function(
                        &new.scope.make_path_absolute(vec![name.clone()]).expect("referenced path exists"),
                        &func.head
                    ) 
                };
                let declaration = new
                    .transpile_declaration(func.head.return_type.typed(), &format!("{func_name}({args})"));
    
                let mut code = vec![];
                new.indent += 1;
                for stmt in &func.statements {
                    code.push(new.transpile_statement(stmt))
                }
                new.shadowed_variables.clear();
                new.indent -= 1;
                //new.source.pop();
                new.functions.push((declaration, code.join("\n")))
    
            }
        }

        for (method, func) in &new.scope.declared_methods {
            let mut head_args = func.head.arguments.iter().map(|(name, ty)| (name, ty.typed())).peekable();
            let receiver = head_args.peek().expect("methods have at least a receiver").1.clone();

            let args = head_args
                .map(|(name, type_)| {
                    new.shadowed_variables.insert(name.clone(), 0);
                    new.transpile_declaration(type_, name)
                })
                .collect::<Vec<String>>()
                .join(", ");

            // args is never empty since it has at least a receiver

            let name = new.mangle_method(&receiver, method, &func.head);
            let declaration = new
                .transpile_declaration(&func.head.return_type.typed(), &format!("{name}({args})"));

            let mut code = vec![];
            new.indent += 1;
            for stmt in &func.statements {
                code.push(new.transpile_statement(stmt))
            }
            new.shadowed_variables.clear();
            new.indent -= 1;
            //new.source.pop();
            new.functions.push((declaration, code.join("\n")))
        }

        for stmt in &new.scope.statements {
            match stmt {
                Statement::StructDeclaration { name } => {
                    let struct_type = new
                        .scope
                        .get_type(&vec![name.clone()])
                        .expect("declared struct exists");
    
                    let TypeKind::Struct {members} = struct_type.kind.clone()
                        else { unreachable!("defined struct should have struct type ") };
    
                    let struct_name = new.mangle_struct(&new.scope.make_path_absolute(vec![name.clone()]).expect("referenced path exists"));

                    let mut body = vec![];
                    new.indent += 1;
                    for (m_name, m_type) in members {
                        let decl = new.transpile_declaration(m_type.typed(), &m_name);
                        body.push(new.add_line(format!("{decl};")));
                    }
                    new.indent -= 1;
                    
                    new.structs.push((struct_name, body.join("\n")));
                }
                Statement::LetAssignment { .. } => todo!("global variable transpilation"),
                Statement::Import(child) => {
                    let submodule = match &new.scope.resources.get(child).expect("imported submodule is valid").as_slice() {
                        [Resource { kind: ResourceKind::Module(m), .. }] => m,
                        _ => unreachable!("imported submodule is a resource of type Module")
                    };
                    let mut transpiled_submodule = ModuleTranspiler::transpile(submodule);

                    new.includes.extend(transpiled_submodule.includes.drain());
                    new.global_variables.append(&mut transpiled_submodule.global_variables);
                    new.functions.append(&mut transpiled_submodule.functions);
                    new.structs.append(&mut transpiled_submodule.structs);

                },
                Statement::Expression(_)
                | Statement::If { .. }
                | Statement::Assignment { .. }
                | Statement::Return(_)
                | Statement::While { .. } => unreachable!("those statements cannot exist in a module scope")
            }
        }

        new
    }

    fn add_line(&mut self, line: String) -> String {
        format!("{}{line}", "    ".repeat(self.indent))
    }

    fn transpile_statement(&mut self, stmt: &Statement) -> String {
        use Statement::*;
        match stmt {
            Expression(expr) => {
                let expr = self.transpile_expression(&expr.data);
                self.add_line(format!("{expr};"))
            }
            LetAssignment { name, value } => {
                let expr = self.transpile_expression(&value.data);
                let name = self.transpile_new_variable(name);
                let declaration = self.transpile_declaration(&value.type_, &name);

                self.add_line(format!("{} = {};", declaration, expr))
            }
            Assignment { lhs, rhs } => {
                let lhs = self.transpile_expression(&lhs.data);
                let rhs = self.transpile_expression(&rhs.data);

                self.add_line(format!("{} = {};", lhs, rhs))
            }
            If { conditions_and_bodies, else_body, } => {
                let mut code = vec![];

                let mut first = true;
                for (condition, body) in conditions_and_bodies {
                    let condition = self.transpile_expression(&condition.data);
                    if first {
                        first = false;
                        code.push(self.add_line(format!("if ({}) {{", condition)));
                    } else {
                        code.push(self.add_line(format!("}} else if ({}) {{", condition)));
                    }

                    self.indent += 1;
                    for stmt in body {
                        code.push(self.transpile_statement(stmt));
                    }
                    self.indent -= 1;
                }

                if let Some(body) = else_body {
                    self.add_line("} else {".to_string());
                    self.indent += 1;
                    for stmt in body {
                        code.push(self.transpile_statement(stmt));
                    }
                    self.indent -= 1;
                }

                code.push(self.add_line('}'.to_string()));

                code.join("\n")
            }
            While { condition, body } => {
                let mut code = vec![];

                let condition = self.transpile_expression(&condition.data);
                code.push(self.add_line(format!("while ({}) {{", condition)));

                self.indent += 1;
                for stmt in body {
                    code.push(self.transpile_statement(stmt));
                }
                self.indent -= 1;

                code.push(self.add_line('}'.to_string()));

                code.join("\n")
            }
            Return(expr) => {
                match expr {
                    Some(expr) => {
                        let expr = self.transpile_expression(&expr.data);
                        self.add_line(format!("return {};", expr))
                    }
                    None => self.add_line(format!("return;")),
                }
            },
            StructDeclaration { .. }
            | Import(_) => unreachable!("those statements cannot exist in a function scope")
        }
    }

    fn transpile_expression(&mut self, expr: &ExpressionData) -> String {
        match expr {
            ExpressionData::Binary { left, operator, right, } => {
                format!(
                    "({} {operator} {})",
                    self.transpile_expression(&left.data),
                    self.transpile_expression(&right.data)
                )
            }
            ExpressionData::FunctionCall { function, arguments, head } => {
                let name = if head.no_mangle {
                    function.last().expect("path is not empty").clone()
                } else {
                    self.mangle_function(function, head)
                };
                let args = arguments
                    .into_iter()
                    .map(|e| self.transpile_expression(&e.data))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{name}({args})")
            }
            ExpressionData::MethodCall { method, arguments, head } => {
                let receiver = arguments[0].type_.clone();
                
                let name = self.mangle_method(&receiver, &method, &head.head);
                let args = arguments
                    .into_iter()
                    .map(|e| self.transpile_expression(&e.data))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{name}({args})")
            },
            ExpressionData::Literal(lit) => match lit {
                Literal::String(content) => format!("\"{}\"", content),
                Literal::Integer { value, .. } => value.clone(),
                Literal::Float { value, size } => match size {
                    Some(32) => format!("{}f", value),
                    _ => value.clone(),
                },
                Literal::Null => "NULL".to_string(),
                Literal::True => "true".to_string(),
                Literal::False => "false".to_string(),
            },
            ExpressionData::ParenBlock(inner) => {
                format!("({})", self.transpile_expression(&inner.data))
            }
            ExpressionData::Unary { operator, argument } => {
                format!("({operator}{})", self.transpile_expression(&argument.data))
            }
            ExpressionData::Variable(path) => {
                if path.len() == 1 {
                    self.transpile_variable(&path[0])
                } else {
                    todo!("transpile namespaced variable {path:?}")
                }
                
            },
            ExpressionData::StructMember { instance, member } => {
                format!("{}.{}", self.transpile_expression(&instance.data), member)
            }
            ExpressionData::StructInit { path, members } => {
                let members = members
                    .into_iter()
                    .map(|(m_name, m_value)| {
                        format!(".{m_name} = {}", self.transpile_expression(&m_value.data))
                    })
                    .collect::<Vec<_>>()
                    .join(", ");

                format!("(({}) {{ {members} }})", self.transpile_named_type(&path))
            }
        }
    }

    fn transpile_declaration(&mut self, type_: &Type, variable: &String) -> String {
        match type_ {
            Type::Void => format!("void {variable}",), // cursed void variable but i'll fix it later
            Type::Path(path) if path[0] == "str" => {
                // hack until a real string type is implemented
                format!("char *{variable}")
            },
            Type::Path(path) => format!("{} {variable}", self.transpile_named_type(&path)),
            Type::Reference { inner, mutable: _ } => {
                match **inner {
                    Type::Void | Type::Path(_) | Type::Reference{..} => {
                        self.transpile_declaration(inner, &format!("*{variable}"))
                    }
                    // _ => self.transpile_declaration(*inner, format!("(*{variable})"))
                }
            }
            // Type::Array { base, size } => {
            //     match *base {
            //         Type::Void | Type::Identifier(_) /* | Type::Array { .. } */  => self.transpile_declaration(*base, format!("{variable}[{size}]")),
            //         _ => self.transpile_declaration(*base, format!("({variable}[{size}])")),
            //     }
            // },
            // Type::Function { .. } => todo!("function pointer transpile") // for my own sanity
        }
    }

    fn transpile_variable(&self, name: &String) -> String {
        let n = self.shadowed_variables.get(name).expect("used variables should be declared").clone();
        format!("{name}{}", "_".repeat(n))
    }

    fn transpile_new_variable(&mut self, name: &String) -> String {
        let n = match self.shadowed_variables.get(name).cloned() {
            Some(n) => n+1,
            None => 0
        };
        self.shadowed_variables.insert(name.clone(), n);
        self.transpile_variable(name)
    }

    fn transpile_named_type(&self, path: &Vec<String>) -> String {
        if path.len() == 1 {
            match path[0].as_str() {
                "int" => "int32_t".to_string(),
                "uint" => "uint32_t".to_string(),
                "float" => "double".to_string(),
                "bool" => "_Bool".to_string(),
                "char" => "char".to_string(),

                "int8" => "int8_t".to_string(),
                "uint8" => "uint8_t".to_string(),
                "int16" => "int16_t".to_string(),
                "uint16" => "uint16_t".to_string(),
                "int32" => "int32_t".to_string(),
                "uint32" => "uint32_t".to_string(),
                "int64" => "int64_t".to_string(),
                "uint64" => "uint64_t".to_string(),

                "float32" => "float".to_string(),
                "float64" => "double".to_string(),

                "usize" => "size_t".to_string(),
                "isize" => "ptrdiff_t".to_string(),

                _ => self.mangle_struct(path),
            }
        } else {
            self.mangle_struct(path)
        }
    }
}

impl<'a> ModuleTranspiler<'a> {
    const MANGLE_PREFIX: &'static str = "_C";

    fn mangle_ident(&self, ident: &String) -> String {
        format!("{}{}", ident.len(), ident)
    }
    
    fn mangle_path(&self, path: &Vec<String>) -> String {
        format!("N{}E", path.iter().map(|x| self.mangle_ident(x)).collect::<Vec<_>>().join(""))
    }

    fn mangle_named_type(&self, path: &Vec<String>) -> String {
        if path.len() == 1 {
            match path[0].as_str() {
                "int" => "i".to_string(),
                "uint" => "u".to_string(),
                "float" => "f".to_string(),
                "bool" => "b".to_string(),
                "char" => "c".to_string(),

                "int8" => "i8".to_string(),
                "uint8" => "u8".to_string(),
                "int16" => "i16".to_string(),
                "uint16" => "u16".to_string(),
                "int32" => "i32".to_string(),
                "uint32" => "u32".to_string(),
                "int64" => "i64".to_string(),
                "uint64" => "u64".to_string(),

                "float32" => "f32".to_string(),
                "float64" => "f64".to_string(),

                "usize" => "si".to_string(),
                "isize" => "su".to_string(),

                _ => self.mangle_path(path),
            }
        } else {
            self.mangle_path(path)
        }
    }

    fn mangle_type(&self, ty: &Type) -> String {
        match ty {
            Type::Void => "v".to_string(),
            Type::Path(path) => self.mangle_named_type(path),
            Type::Reference { inner, mutable } => {
                if *mutable {
                    format!("M{}", self.mangle_type(inner))
                } else {
                    format!("R{}", self.mangle_type(inner))
                }
            }
        }
    }

    fn mangle_method(&self, receiver: &Type, method: &String, head: &FunctionHead) -> String {
        let head_args = head.arguments.iter().map(|(name, ty)| (name, ty.typed())).peekable();
        let mut args = String::with_capacity(head_args.len());
        
        for (_, arg_type) in head_args {
            args.push_str(&self.mangle_type(arg_type))
        }

        let return_type = self.mangle_type(head.return_type.typed());

        format!("{}M{}{}{args}R{return_type}", Self::MANGLE_PREFIX, self.mangle_type(receiver), self.mangle_ident(method))
    }

    fn mangle_function(&self, path: &Vec<String>, head: &FunctionHead) -> String {
        let mut args;

        let mut function_arguments = head.arguments.iter().map(|(name, ty)| (name, ty.typed())).peekable();

        if function_arguments.peek().is_none() {
            args = "v".to_string();
        } else {
            args = String::with_capacity(function_arguments.len());
            for (_, arg_type) in function_arguments {
                args.push_str(&self.mangle_type(arg_type))
            }
        }

        let return_type = self.mangle_type(head.return_type.typed());

        format!("{}F{}{args}R{return_type}", Self::MANGLE_PREFIX, self.mangle_path(path))
    }

    fn mangle_struct(&self, path: &Vec<String>) -> String {
        format!("{}S{}", Self::MANGLE_PREFIX, self.mangle_path(path))
    }
}

impl<'a> Display for ModuleTranspiler<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut something = false;
        
        for inc in &self.includes {
            something = true;
            writeln!(f, "#include {inc}")?;
        }

        if something { writeln!(f)?; }
        something = false;

        for (name, _) in &self.structs {
            something = true;

            writeln!(f, "typedef struct {name} {name};")?;
        }

        if something { writeln!(f)?; }
        something = false;

        for (decl, _) in &self.functions {
            something = true;

            writeln!(f, "{decl};")?;
        }

        if something { writeln!(f)?; }
        something = false;

        for var in &self.global_variables {
            something = true;

            writeln!(f, "{var};")?;
        }

        if something { writeln!(f)?; }
        something = false;

        for (name, body) in &self.structs {
            something = true;

            writeln!(f, "struct {name} {{\n{body}\n}};\n")?;
        }

        if something { writeln!(f)?; }

        for (decl, body) in &self.functions {
            writeln!(f, "{decl} {{\n{body}\n}}\n")?;
        }

        Ok(())
    }
}
