use crate::core::*;
use crate::names::Namespace;
use crate::token::Index;
use crate::Error;

pub fn resolve_indices<'a>(fields: &mut Vec<ModuleField<'a>>) -> Result<(), Error> {
    let mut resolver = IndexResolver::default();
    resolver.process(fields)?;
    Ok(())
}

/// Context structure used to perform name resolution.
#[derive(Default)]
pub struct IndexResolver<'a> {
    types: Namespace<'a>,
    type_info: Vec<TypeInfo<'a>>,
}

impl<'a> IndexResolver<'a> {
    fn process(&mut self, fields: &mut Vec<ModuleField<'a>>) -> Result<(), Error> {
        // Then we can replace all our `Index::Id` instances with `Index::Num`
        // in the AST. Note that this also recurses into nested modules.
        for field in fields.iter_mut() {
            match field {
                ModuleField::Type(t) => self.register_type(t)?,
                _ => {}
            }
        }
        for field in fields.iter_mut() {
            self.resolve_field(field)?;
        }
        Ok(())
    }

    fn register_type(&mut self, ty: &mut Type<'a>) -> Result<(), Error> {
        // Record function signatures as we see them to so we can
        // generate errors for mismatches in references such as
        // `call_indirect`.
        match &mut ty.def {
            TypeDef::Func(f) => {
                let params = f.params.iter().map(|p| p.2).collect();
                self.type_info.push(TypeInfo {
                    params,
                });

                self.resolve_func_type(f)?;
            }
            _ => {},
        }

        self.types.register(ty.id, "type")?;
        Ok(())
    }

    fn resolve_func_type(&self, ty: &mut IndexedFunctionType<'a>) -> Result<(), Error> {
        // Clunky as f*** but keeps the rust borrow checker happy
        let mut resolver = IndexTypeResolver::new(false, None);
        resolver.resolve_type(ty)
    }

    fn resolve_field(&self, field: &mut ModuleField<'a>) -> Result<(), Error> {
        match field {
            ModuleField::Func(f) => {
                if let FuncKind::Inline { locals, expression } = &mut f.kind {

                    // Build a scope with a local namespace for the function
                    // body
                    let mut scope = Namespace::default();

                    // Parameters come first in the scope...
                    if let Some(inline) = &mut f.ty.inline {
                        self.resolve_func_type(inline)?;

                        for (id, _, _) in inline.params.iter() {
                            scope.register(*id, "local")?;
                        }
                    } else if let Some(idx) = &f.ty.index {
                        let n = match idx {
                            Index::Num(n, _) => *n,
                            Index::Id(_) => panic!("expected `Num`"),
                        };

                        if let Some(TypeInfo { params, ..}) =
                            self.type_info.get(n as usize)
                        {
                            for _ in 0..params.len() {
                                scope.register(None, "local")?;
                            }
                        }
                    }

                    // .. followed by locals themselves
                    for local in locals {
                        scope.register(local.id, "local")?;
                    }

                    let type_resolver = IndexTypeResolver::new(true, Some(scope));

                    // Initialize the expression resolver with this scope
                    let mut resolver = IndexExprResolver::new(type_resolver);

                    // and then we can resolve the expression!
                    resolver.resolve(expression)?;
                }
                Ok(())
            },
            _ => Ok(()),
        }
    }/*

    fn check_func_index_term(&self, it: &IndexTerm<'a>, in_func: bool) -> Result<(), Error> {
        match it {
            IndexTerm::Local(local) => {
                if in_func {
                    return Err(Error::new(
                        local.span(),
                        "can't have a local reference in a constraint in a function type".to_string(),
                    ));
                } else if !local.is_resolved() {
                    return Err(Error::new(
                        local.span(),
                        "can't have a local reference outside an inline block type definition".to_string(),
                    ));
                }
            },
            _ => {}
        }
        Ok(())
    }

    fn check_func_constraint(&self, c: &Constraint<'a>, in_func: bool) -> Result<(), Error> {
        // Resolve the (ref T) value types in the final function type
        match c {
            Constraint::Eq(x,y) => {
                self.check_func_index_term(x, in_func)?;
                self.check_func_index_term(y, in_func)?;
            },
            Constraint::And(x, y) => {
                self.check_func_constraint(& *x, in_func)?;
                self.check_func_constraint(& *y, in_func)?;
            },
            Constraint::Or(x, y) => {
                self.check_func_constraint(& *x, in_func)?;
                self.check_func_constraint(& *y, in_func)?;
            },
            Constraint::If(i, t, e) => {
                self.check_func_constraint(& *i, in_func)?;
                self.check_func_constraint(& *t, in_func)?;
                self.check_func_constraint(& *e, in_func)?;
            },
            Constraint::Not(x) => {
                self.check_func_constraint(& *x, in_func)?;
            },
        }
        Ok(())
    }*/
}

struct IndexExprResolver<'a> {
    resolver: IndexTypeResolver<'a>,
}

impl<'a> IndexExprResolver<'a> {
    fn new(resolver: IndexTypeResolver<'a>) -> IndexExprResolver<'a> {
        IndexExprResolver {
            resolver,
        }
    }

    fn resolve(&mut self, expr: &mut Expression<'a>) -> Result<(), Error> {
        for instr in expr.instrs.iter_mut() {
            self.resolve_instr(instr)?;
        }
        Ok(())
    }

    fn resolve_instr(&mut self, instr: &mut Instruction<'a>) -> Result<(), Error> {
        use Instruction::*;

        match instr {
            Block(bt) | If(bt) | Loop(bt) | Try(bt) => {
                if let Some(inline) = &mut bt.ty.inline {
                    self.resolver.resolve_type(inline)?;
                }
            }

            _ => {}
        }
        Ok(())
    }
}

struct IndexTypeResolver<'a> {
    // If local_scope is none, this must be a function type or an inline block type
    local_scope: Option<Namespace<'a>>,
    // If we're in a function type, locals aren't allowed, if it's not a function, and local_scope is None, then it must be an inline block, so locals must already be resolved
    is_func: bool,
    pre_scope: Namespace<'a>,
    post_scope: Namespace<'a>,
}

impl<'a> IndexTypeResolver<'a> {
    fn new(
        is_func: bool,
        local_scope: Option<Namespace<'a>>,
    ) -> IndexTypeResolver<'a> {
        IndexTypeResolver {
            local_scope,
            is_func,
            pre_scope: Namespace::default(),
            post_scope: Namespace::default(),
        }
    }
    
    fn resolve_type(&mut self, ty: &mut IndexedFunctionType<'a>) -> Result<(), Error> {
        for (id,_,_) in ty.params.iter() {
            self.pre_scope.register(*id, "index")?;
        }
        for (id,_,_) in ty.results.iter() {
            self.post_scope.register(*id, "index")?;
        }

        for constraint in ty.pre_constraints.iter_mut() {
            self.resolve_constraint(constraint)?;
        }
        for constraint in ty.post_constraints.iter_mut() {
            self.resolve_constraint(constraint)?;
        }

        Ok(())
    }

    fn resolve_local(&self, i: &mut Index<'a>) -> Result<(), Error> {
        if let Some(locals) = &self.local_scope {
            if let Err(_) = locals.resolve(i, "local") {
                return Err(Error::new(
                    i.span(),
                    "unresolvable local reference".to_string(),
                ));
            }
        } else if self.is_func {
            return Err(Error::new(
                i.span(),
                "can't have a local reference in a constraint in a function type".to_string(),
            ));
        } else if !i.is_resolved() {
            return Err(Error::new(
                i.span(),
                "can't have a local reference outside an inline block type definition".to_string(),
            ));
        }
        Ok(())
    }

    fn resolve_index_term(&self, it: &mut IndexTerm<'a>) -> Result<(), Error> {
        match it {
            IndexTerm::Local(local) => self.resolve_local(local)?,
            IndexTerm::Alpha(id) => {
                if let Ok(n) = self.post_scope.resolve(&mut Index::Id(*id), "index") {
                    *it = IndexTerm::Post(Index::Num(n,id.span()));
                } else if let Ok(n) = self.pre_scope.resolve(&mut Index::Id(*id), "index") {
                    *it = IndexTerm::Pre(Index::Num(n,id.span()));
                } else {
                    return Err(Error::new(
                        id.span(),
                        "unresolvable index type variable".to_string(),
                    ));
                }
            }
            IndexTerm::IBinOp(_, x, y) => {
                self.resolve_index_term(&mut *x)?;
                self.resolve_index_term(&mut *y)?;
            }
            IndexTerm::IRelOp(_, x, y) => {
                self.resolve_index_term(&mut *x)?;
                self.resolve_index_term(&mut *y)?;
            }
            IndexTerm::ITestOp(_, x) => {
                self.resolve_index_term(&mut *x)?;
            }
            IndexTerm::IUnOp(_, x) => {
                self.resolve_index_term(&mut *x)?;
            }
            IndexTerm::IConstant(_) => {},
            IndexTerm::Pre(idx) | IndexTerm::Post(idx) => {
                if !idx.is_resolved() {
                    return Err(Error::new(
                        idx.span(),
                        "unresolvable index type variable".to_string(),
                    ));
                }
            }
        }
        Ok(())
    }

    fn resolve_constraint(&self, c: &mut Constraint<'a>) -> Result<(), Error> {
        // Resolve the (ref T) value types in the final function type
        match c {
            Constraint::Eq(x,y) => {
                self.resolve_index_term(x)?;
                self.resolve_index_term(y)?;
            },
            Constraint::And(x, y) => {
                self.resolve_constraint(&mut *x)?;
                self.resolve_constraint(&mut *y)?;
            },
            Constraint::Or(x, y) => {
                self.resolve_constraint(&mut *x)?;
                self.resolve_constraint(&mut *y)?;
            },
            Constraint::If(i, t, e) => {
                self.resolve_constraint(&mut *i)?;
                self.resolve_constraint(&mut *t)?;
                self.resolve_constraint(&mut *e)?;
            },
            Constraint::Not(x) => {
                self.resolve_constraint(&mut *x)?;
            },
        }
        Ok(())
    }
}

struct TypeInfo<'a> {
    params: Box<[ValType<'a>]>,
}
