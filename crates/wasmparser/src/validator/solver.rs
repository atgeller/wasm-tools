//use index_language::constraint;

use crate::{
    BinOp, Constant, Constraint, IndexTerm, RelOp, UnOp, TestOp, ValType,
};
use z3::{Config, Context, ast, SatResult};
use z3::ast::{Bool, BV, Ast};


pub trait ConstraintSolver {
    fn satisfies(gamma: &Vec<Option<ValType>>, phi1: &Vec<Constraint>, phi2: &Vec<Constraint>) -> bool;
}

pub struct Z3<'a> {
    ctx: &'a Context,
    vars: Vec<BV<'a>>,
}

impl<'a> Z3<'a> {
    /*fn ty_to_sort(ty: ValType, ctx: &'a Context) -> Sort<'a> {
        match ty {
            ValType::I32 => Sort::bitvector(ctx, 32),
            ValType::I64 => Sort::bitvector(ctx, 64),
            _ => todo!(),
        }
    }*/

    fn process_binop(&self, binop: &BinOp, bv1: BV<'a>, bv2: BV<'a>) -> BV<'a> {
        match binop {
            BinOp::I32Add => bv1.bvadd(&bv2),
            BinOp::I32Sub => bv1.bvsub(&bv2),
            BinOp::I32Mul => bv1.bvmul(&bv2),
            BinOp::I32DivS => bv1.bvsdiv(&bv2),
            BinOp::I32DivU => bv1.bvudiv(&bv2),
            BinOp::I32RemS => bv1.bvsrem(&bv2),
            BinOp::I32RemU => bv1.bvurem(&bv2),
            BinOp::I32And => bv1.bvand(&bv2),
            BinOp::I32Or => bv1.bvor(&bv2),
            BinOp::I32Xor => bv1.bvxor(&bv2),
            BinOp::I32Shl => bv1.bvshl(&bv2),
            BinOp::I32ShrS => bv1.bvashr(&bv2),
            BinOp::I32ShrU => bv1.bvlshr(&bv2),
            BinOp::I32Rotl => bv1.bvrotl(&bv2),
            BinOp::I32Rotr => bv1.bvrotr(&bv2),
            BinOp::I64Add => bv1.bvadd(&bv2),
            BinOp::I64Sub => bv1.bvsub(&bv2),
            BinOp::I64Mul => bv1.bvmul(&bv2),
            BinOp::I64DivS => bv1.bvsdiv(&bv2),
            BinOp::I64DivU => bv1.bvudiv(&bv2),
            BinOp::I64RemS => bv1.bvsrem(&bv2),
            BinOp::I64RemU => bv1.bvurem(&bv2),
            BinOp::I64And => bv1.bvand(&bv2),
            BinOp::I64Or => bv1.bvor(&bv2),
            BinOp::I64Xor => bv1.bvxor(&bv2),
            BinOp::I64Shl => bv1.bvshl(&bv2),
            BinOp::I64ShrS => bv1.bvashr(&bv2),
            BinOp::I64ShrU => bv1.bvlshr(&bv2),
            BinOp::I64Rotl => bv1.bvrotl(&bv2),
            BinOp::I64Rotr => bv1.bvrotr(&bv2),
        }
    }

    fn process_relop(&self, relop: &RelOp, bv1: BV<'a>, bv2: BV<'a>) -> BV<'a> {
        let i32_true = BV::from_i64(self.ctx, 1, 32);
        let i32_false = BV::from_i64(self.ctx, 0, 32);
        match relop {
            RelOp::I32Eq => bv1._eq(&bv2).ite(&i32_true, &i32_false),
            RelOp::I32Ne => bv1._eq(&bv2).ite(&i32_false, &i32_true),
            RelOp::I32LtS => bv1.bvslt(&bv2).ite(&i32_true, &i32_false),
            RelOp::I32LtU => bv1.bvult(&bv2).ite(&i32_true, &i32_false),
            RelOp::I32GtS => bv1.bvsgt(&bv2).ite(&i32_true, &i32_false),
            RelOp::I32GtU => bv1.bvugt(&bv2).ite(&i32_true, &i32_false),
            RelOp::I32LeS => bv1.bvsle(&bv2).ite(&i32_true, &i32_false),
            RelOp::I32LeU => bv1.bvule(&bv2).ite(&i32_true, &i32_false),
            RelOp::I32GeS => bv1.bvsge(&bv2).ite(&i32_true, &i32_false),
            RelOp::I32GeU => bv1.bvuge(&bv2).ite(&i32_true, &i32_false),
            RelOp::I64Eq => bv1._eq(&bv2).ite(&i32_true, &i32_false),
            RelOp::I64Ne => bv1._eq(&bv2).ite(&i32_false, &i32_true),
            RelOp::I64LtS => bv1.bvslt(&bv2).ite(&i32_true, &i32_false),
            RelOp::I64LtU => bv1.bvult(&bv2).ite(&i32_true, &i32_false),
            RelOp::I64GtS => bv1.bvsgt(&bv2).ite(&i32_true, &i32_false),
            RelOp::I64GtU => bv1.bvugt(&bv2).ite(&i32_true, &i32_false),
            RelOp::I64LeS => bv1.bvsle(&bv2).ite(&i32_true, &i32_false),
            RelOp::I64LeU => bv1.bvule(&bv2).ite(&i32_true, &i32_false),
            RelOp::I64GeS => bv1.bvsge(&bv2).ite(&i32_true, &i32_false),
            RelOp::I64GeU => bv1.bvuge(&bv2).ite(&i32_true, &i32_false),
        }
    }

    fn process_testop(&self, testop: &TestOp, bv1: BV<'a>) -> BV<'a> {
        let i32_true = BV::from_i64(self.ctx, 1, 32);
        let i32_false = BV::from_i64(self.ctx, 0, 32);
        match testop {
            TestOp::I32Eqz => {
                bv1._eq(&i32_false).ite(&i32_true, &i32_false)
            },
            TestOp::I64Eqz => {
                let i64_false = BV::from_i64(self.ctx, 0, 64);
                bv1._eq(&i64_false).ite(&i32_true, &i32_false)
            },
        }
    }

    fn process_unop(&self, unop: &UnOp, _bv1: BV<'a>) -> BV<'a> {
        match unop {
            UnOp::I32Clz => todo!(),
            UnOp::I32Ctz => todo!(),
            UnOp::I32Popcnt => todo!(),
            UnOp::I64Clz => todo!(),
            UnOp::I64Ctz => todo!(),
            UnOp::I64Popcnt => todo!(),
        }
    }

    fn process_index_term(&self, term: &IndexTerm) -> BV<'a> {
        match term {
            IndexTerm::IBinOp(binop, x, y) => {
                let bv1 = self.process_index_term(&*x);
                let bv2 = self.process_index_term(&*y);
                self.process_binop(binop, bv1, bv2)
            }
            IndexTerm::IRelOp(relop, x, y) => {
                let bv1 = self.process_index_term(&*x);
                let bv2 = self.process_index_term(&*y);
                self.process_relop(relop, bv1, bv2)
            }
            IndexTerm::ITestOp(testop, x) => {
                let bv1 = self.process_index_term(&*x);
                self.process_testop(testop, bv1)
            }
            IndexTerm::IUnOp(unop, x) => {
                let bv1 = self.process_index_term(&*x);
                self.process_unop(unop, bv1)
            }
            IndexTerm::Alpha(idx) => {
                self.vars[*idx as usize].clone()
            }
            IndexTerm::IConstant(c) => {
                match c {
                    Constant::I32Const(val) => BV::from_i64(&self.ctx, (*val).into(), 32),
                    Constant::I64Const(val) => BV::from_i64(&self.ctx, *val, 64),
                }
            }
            _ => panic!("Unresolved variable in index term!"),
        }
    }

    fn process_constraint(&self, constraint: &Constraint) -> Bool<'a> {
        match constraint {
            Constraint::Eq(x, y) => {
                let bv1 = self.process_index_term(x);
                let bv2 = self.process_index_term(y);
                bv1._eq(&bv2)
            },
            Constraint::And(x, y) => {
                Bool::and(&self.ctx, &[&self.process_constraint(&*x), &self.process_constraint(&*y)])
            },
            Constraint::Or(x, y) => {
                Bool::or(&self.ctx, &[&self.process_constraint(&*x), &self.process_constraint(&*y)])
            },
            Constraint::Not(x) => {
                self.process_constraint(&*x).not()
            },
            Constraint::If(x, y, z) => {
                self.process_constraint(&*x).ite(&self.process_constraint(&*y), &self.process_constraint(&*z))
            },
        }
    }
}

impl ConstraintSolver for Z3<'static> {
    fn satisfies(gamma: &Vec<Option<ValType>>, phi1: &Vec<Constraint>, phi2: &Vec<Constraint>) -> bool {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let solver = z3::Solver::new(&ctx);
        let vars = gamma.iter()
            .enumerate()
            .filter_map(|(idx,opty)| {
                opty.map(|ty| {
                    let size = match ty {
                        ValType::I32 => 32,
                        ValType::I64 => 64,
                        _ => 1, // No harm, no foul, right?
                    };
                    ast::BV::new_const(&ctx, format!("alpha_{:?}", idx),size)
                })
            }).collect();
        let instance = Z3 { ctx: &ctx, vars };
        for c in phi1 {
            solver.assert(&instance.process_constraint(c));
        }

        let mut rhs = Vec::new();
        for c in phi2 {
            rhs.push(instance.process_constraint(c));
        }
        let binding = rhs.iter().map(|x| x).collect::<Vec<&Bool>>();
        solver.assert(&Bool::and(&ctx, binding.as_slice()).not());

        let result = solver.check();
        match result {
            SatResult::Unsat => true,
            _ => { println!("Model: {:?}", solver.get_model()); false},
        }
    }
}