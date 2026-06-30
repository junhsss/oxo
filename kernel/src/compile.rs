use crate::{ind_head, ETerm, Sig};
use std::rc::Rc;

#[derive(Clone)]
pub enum Op {
    Constr(usize, usize, Vec<usize>),
    Call(usize, Vec<usize>),
}

#[derive(Clone)]
pub struct Branch {
    pub nbind: usize,
    pub body: Expr,
}

#[derive(Clone)]
pub enum Expr {
    Ret(usize),
    Let(Op, Box<Expr>),
    Case(usize, usize, Vec<Branch>),
}

#[derive(Clone)]
pub struct Func {
    pub nparams: usize,
    pub body: Expr,
}

pub struct Program {
    pub funcs: Vec<Func>,
    pub sig: Rc<Sig>,
}

pub enum Shape {
    NatLike,
    EnumLike,
}

pub fn shape(sig: &Sig, i: usize) -> Shape {
    let ind = &sig[i];
    if ind.constructors.iter().all(|c| c.args.is_empty()) {
        return Shape::EnumLike;
    }
    if ind.constructors.len() == 2
        && ind.constructors[0].args.is_empty()
        && ind.constructors[1].args.len() == 1
        && ind_head(&ind.constructors[1].args[0]) == Some(i)
    {
        return Shape::NatLike;
    }
    unreachable!()
}

pub fn encode(sig: &Sig, i: usize, j: usize, fields: &[i64]) -> i64 {
    match shape(sig, i) {
        Shape::EnumLike => j as i64,
        Shape::NatLike => {
            if j == 0 {
                0
            } else {
                fields[0] + 1
            }
        }
    }
}

pub fn decode(sig: &Sig, i: usize, v: i64) -> (usize, Vec<i64>) {
    match shape(sig, i) {
        Shape::EnumLike => (v as usize, Vec::new()),
        Shape::NatLike => {
            if v == 0 {
                (0, Vec::new())
            } else {
                (1, vec![v - 1])
            }
        }
    }
}

pub fn decode_to_eterm(sig: &Sig, i: usize, v: i64) -> ETerm {
    let (tag, fields) = decode(sig, i, v);
    let mut out = ETerm::Constr(i, tag);
    for f in fields {
        out = ETerm::App(Box::new(out), Box::new(decode_to_eterm(sig, i, f)));
    }
    out
}

#[derive(Clone)]
struct Frame {
    locals: Vec<i64>,
    ctrl: Expr,
}

pub struct State {
    cur: Frame,
    stack: Vec<Frame>,
}

#[derive(Debug, PartialEq)]
pub enum RunError {
    Stuck,
    OutOfResources,
}

fn step(prog: &Program, st: State) -> Option<State> {
    let State { mut cur, mut stack } = st;
    let ctrl = std::mem::replace(&mut cur.ctrl, Expr::Ret(0));
    match ctrl {
        Expr::Ret(slot) => {
            let v = cur.locals[slot];
            let mut caller = stack.pop()?;
            caller.locals.push(v);
            Some(State { cur: caller, stack })
        }
        Expr::Let(Op::Constr(i, j, fs), rest) => {
            let vs: Vec<i64> = fs.iter().map(|s| cur.locals[*s]).collect();
            let v = encode(&prog.sig, i, j, &vs);
            cur.locals.push(v);
            cur.ctrl = *rest;
            Some(State { cur, stack })
        }
        Expr::Let(Op::Call(f, args), rest) => {
            let avs: Vec<i64> = args.iter().map(|s| cur.locals[*s]).collect();
            cur.ctrl = *rest;
            stack.push(cur);
            let callee = Frame {
                locals: avs,
                ctrl: prog.funcs[f].body.clone(),
            };
            Some(State { cur: callee, stack })
        }
        Expr::Case(i, scrut, branches) => {
            let v = cur.locals[scrut];
            let (tag, fields) = decode(&prog.sig, i, v);
            let br = branches.into_iter().nth(tag)?;
            cur.locals.extend(fields);
            cur.ctrl = br.body;
            Some(State { cur, stack })
        }
    }
}

pub fn run(prog: &Program, entry: usize, args: &[i64], fuel: usize) -> Result<i64, RunError> {
    let mut st = State {
        cur: Frame {
            locals: args.to_vec(),
            ctrl: prog.funcs[entry].body.clone(),
        },
        stack: Vec::new(),
    };
    for _ in 0..fuel {
        if let Expr::Ret(slot) = &st.cur.ctrl {
            if st.stack.is_empty() {
                return Ok(st.cur.locals[*slot]);
            }
        }
        match step(prog, st) {
            Some(next) => st = next,
            None => return Err(RunError::Stuck),
        }
    }
    Err(RunError::OutOfResources)
}

struct Lowerer {
    funcs: Vec<Func>,
    sig: Rc<Sig>,
}

fn seal(ops: Vec<Op>, ret: usize) -> Expr {
    let mut e = Expr::Ret(ret);
    for op in ops.into_iter().rev() {
        e = Expr::Let(op, Box::new(e));
    }
    e
}

fn flatten(e: &ETerm) -> (&ETerm, Vec<&ETerm>) {
    let mut args = Vec::new();
    let mut head = e;
    while let ETerm::App(f, x) = head {
        args.push(&**x);
        head = &**f;
    }
    args.reverse();
    (head, args)
}

impl Lowerer {
    fn build(&mut self, ops: &mut Vec<Op>, base: usize, e: &ETerm, env: &[usize]) -> usize {
        match e {
            ETerm::Var(i) => env[env.len() - 1 - i],
            ETerm::Constr(i, j) => {
                let slot = base + ops.len();
                ops.push(Op::Constr(*i, *j, Vec::new()));
                slot
            }
            ETerm::App(..) => self.build_app(ops, base, e, env),
            _ => unreachable!(),
        }
    }

    fn build_app(&mut self, ops: &mut Vec<Op>, base: usize, e: &ETerm, env: &[usize]) -> usize {
        let (head, args) = flatten(e);
        match head {
            ETerm::Lam(_) => {
                let mut arg_slots = Vec::new();
                for &a in &args {
                    let s = if let ETerm::Box = a {
                        usize::MAX
                    } else {
                        self.build(ops, base, a, env)
                    };
                    arg_slots.push(s);
                }
                let mut menv = env.to_vec();
                let mut cur = head;
                let mut k = 0;
                while let ETerm::Lam(b) = cur {
                    if k < arg_slots.len() {
                        menv.push(arg_slots[k]);
                        k += 1;
                        cur = &**b;
                    } else {
                        unreachable!()
                    }
                }
                if k == arg_slots.len() {
                    self.build(ops, base, cur, &menv)
                } else {
                    unreachable!()
                }
            }
            ETerm::Constr(i, j) => {
                let mut field_slots = Vec::new();
                for &a in &args {
                    if let ETerm::Box = a {
                        continue;
                    }
                    let s = self.build(ops, base, a, env);
                    field_slots.push(s);
                }
                let slot = base + ops.len();
                ops.push(Op::Constr(*i, *j, field_slots));
                slot
            }
            ETerm::Rec(i) => self.build_rec(ops, base, *i, &args, env),
            _ => unreachable!(),
        }
    }

    fn build_rec(
        &mut self,
        ops: &mut Vec<Op>,
        base: usize,
        i: usize,
        args: &[&ETerm],
        env: &[usize],
    ) -> usize {
        let sig = self.sig.clone();
        let ind = &sig[i];
        let p = ind.params.len();
        let k = ind.constructors.len();
        let n = ind.indices.len();
        let methods: Vec<&ETerm> = (0..k).map(|m| args[p + 1 + m]).collect();
        let major = args[p + 1 + k + n];
        let major_slot = self.build(ops, base, major, env);
        let cap = base + ops.len();
        let idx = self.funcs.len();
        self.funcs.push(Func {
            nparams: 0,
            body: Expr::Ret(0),
        });
        let mut branches = Vec::new();
        for (j, method) in methods.iter().enumerate() {
            let cargs = &sig[i].constructors[j].args;
            let nbind = cargs.len();
            let field_base = cap + 1;
            let mut branch_ops = Vec::new();
            let mut menv = env.to_vec();
            for f in 0..nbind {
                menv.push(field_base + f);
            }
            for (f, aty) in cargs.iter().enumerate() {
                if ind_head(aty) == Some(i) {
                    let mut ca: Vec<usize> = (0..cap).collect();
                    ca.push(field_base + f);
                    menv.push(field_base + nbind + branch_ops.len());
                    branch_ops.push(Op::Call(idx, ca));
                }
            }
            let mut m = *method;
            for _ in 0..nbind + branch_ops.len() {
                match m {
                    ETerm::Lam(b) => m = &**b,
                    _ => unreachable!(),
                }
            }
            let branch_base = field_base + nbind;
            let result = self.build(&mut branch_ops, branch_base, m, &menv);
            branches.push(Branch {
                nbind,
                body: seal(branch_ops, result),
            });
        }
        self.funcs[idx] = Func {
            nparams: cap + 1,
            body: Expr::Case(i, cap, branches),
        };
        let result = base + ops.len();
        let mut call_args: Vec<usize> = (0..cap).collect();
        call_args.push(major_slot);
        ops.push(Op::Call(idx, call_args));
        result
    }
}

pub fn compile(sig: Rc<Sig>, e: &ETerm) -> (Program, usize) {
    let mut lo = Lowerer {
        funcs: Vec::new(),
        sig: sig.clone(),
    };
    let mut env = Vec::new();
    let mut body = e;
    let mut nparams = 0;
    while let ETerm::Lam(b) = body {
        env.push(nparams);
        nparams += 1;
        body = &**b;
    }
    let mut ops = Vec::new();
    let slot = lo.build(&mut ops, nparams, body, &env);
    let entry = lo.funcs.len();
    lo.funcs.push(Func {
        nparams,
        body: seal(ops, slot),
    });
    (
        Program {
            funcs: lo.funcs,
            sig,
        },
        entry,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{enorm, erase, Constructor, Context, Inductive, Term};

    fn v(i: usize) -> Term {
        Term::Var(i)
    }
    fn lam(a: Term, t: Term) -> Term {
        Term::Lam(Box::new(a), Box::new(t))
    }
    fn app(f: Term, x: Term) -> Term {
        Term::App(Box::new(f), Box::new(x))
    }
    fn lett(op: Op, rest: Expr) -> Expr {
        Expr::Let(op, Box::new(rest))
    }

    fn nat_sig() -> Rc<Sig> {
        Rc::new(vec![Inductive {
            params: vec![],
            indices: vec![],
            sort: 1,
            constructors: vec![
                Constructor {
                    args: vec![],
                    index_values: vec![],
                },
                Constructor {
                    args: vec![Term::Ind(0)],
                    index_values: vec![],
                },
            ],
        }])
    }

    fn bool_sig() -> Rc<Sig> {
        Rc::new(vec![Inductive {
            params: vec![],
            indices: vec![],
            sort: 1,
            constructors: vec![
                Constructor {
                    args: vec![],
                    index_values: vec![],
                },
                Constructor {
                    args: vec![],
                    index_values: vec![],
                },
            ],
        }])
    }

    #[test]
    fn machine_runs_lowered_nat_plus_against_evaluator() {
        let sig = nat_sig();
        let nat = 0;
        let rec_plus = Func {
            nparams: 3,
            body: Expr::Case(
                nat,
                0,
                vec![
                    Branch {
                        nbind: 0,
                        body: Expr::Ret(1),
                    },
                    Branch {
                        nbind: 1,
                        body: lett(
                            Op::Call(0, vec![3, 1, 2]),
                            lett(Op::Constr(nat, 1, vec![4]), Expr::Ret(5)),
                        ),
                    },
                ],
            ),
        };
        let plus = Func {
            nparams: 2,
            body: lett(Op::Call(0, vec![1, 0, 1]), Expr::Ret(2)),
        };
        let main = Func {
            nparams: 0,
            body: lett(
                Op::Constr(nat, 0, vec![]),
                lett(
                    Op::Constr(nat, 1, vec![0]),
                    lett(
                        Op::Constr(nat, 1, vec![1]),
                        lett(
                            Op::Constr(nat, 1, vec![0]),
                            lett(Op::Call(1, vec![2, 3]), Expr::Ret(4)),
                        ),
                    ),
                ),
            ),
        };
        let prog = Program {
            funcs: vec![rec_plus, plus, main],
            sig: sig.clone(),
        };
        let result = run(&prog, 2, &[], 100_000).unwrap();
        assert_eq!(result, 3);

        let zero = Term::Constr(0, 0);
        let succ = |n: Term| app(Term::Constr(0, 1), n);
        let plus_src = lam(
            Term::Ind(0),
            lam(
                Term::Ind(0),
                app(
                    app(
                        app(app(Term::Rec(0, 1), lam(Term::Ind(0), Term::Ind(0))), v(0)),
                        lam(Term::Ind(0), lam(Term::Ind(0), succ(v(0)))),
                    ),
                    v(1),
                ),
            ),
        );
        let src = app(app(plus_src, succ(succ(zero.clone()))), succ(zero));
        let ctx = Context::with_sig(sig.clone());
        let expected = enorm(&sig, &erase(&ctx, &src).unwrap());
        assert_eq!(decode_to_eterm(&sig, nat, result), expected);
    }

    #[test]
    fn machine_runs_lowered_bool_not() {
        let sig = bool_sig();
        let boolean = 0;
        let rec_not = Func {
            nparams: 1,
            body: Expr::Case(
                boolean,
                0,
                vec![
                    Branch {
                        nbind: 0,
                        body: lett(Op::Constr(boolean, 1, vec![]), Expr::Ret(1)),
                    },
                    Branch {
                        nbind: 0,
                        body: lett(Op::Constr(boolean, 0, vec![]), Expr::Ret(1)),
                    },
                ],
            ),
        };
        let prog = Program {
            funcs: vec![rec_not],
            sig: sig.clone(),
        };
        let tru = encode(&sig, boolean, 1, &[]);
        let fls = encode(&sig, boolean, 0, &[]);

        let not_true = run(&prog, 0, &[tru], 1000).unwrap();
        assert_eq!(not_true, fls);
        assert_eq!(
            decode_to_eterm(&sig, boolean, not_true),
            ETerm::Constr(0, 0)
        );

        let not_false = run(&prog, 0, &[fls], 1000).unwrap();
        assert_eq!(not_false, tru);
        assert_eq!(
            decode_to_eterm(&sig, boolean, not_false),
            ETerm::Constr(0, 1)
        );
    }

    fn nat_bool_sig() -> Rc<Sig> {
        Rc::new(vec![
            Inductive {
                params: vec![],
                indices: vec![],
                sort: 1,
                constructors: vec![
                    Constructor {
                        args: vec![],
                        index_values: vec![],
                    },
                    Constructor {
                        args: vec![Term::Ind(0)],
                        index_values: vec![],
                    },
                ],
            },
            Inductive {
                params: vec![],
                indices: vec![],
                sort: 1,
                constructors: vec![
                    Constructor {
                        args: vec![],
                        index_values: vec![],
                    },
                    Constructor {
                        args: vec![],
                        index_values: vec![],
                    },
                ],
            },
        ])
    }

    fn nat_lit(mut k: usize) -> Term {
        let mut t = Term::Constr(0, 0);
        while k > 0 {
            t = app(Term::Constr(0, 1), t);
            k -= 1;
        }
        t
    }

    #[test]
    fn compiles_nat_plus_against_evaluator() {
        let sig = nat_sig();
        let ctx = Context::with_sig(sig.clone());
        let plus_src = lam(
            Term::Ind(0),
            lam(
                Term::Ind(0),
                app(
                    app(
                        app(app(Term::Rec(0, 1), lam(Term::Ind(0), Term::Ind(0))), v(0)),
                        lam(
                            Term::Ind(0),
                            lam(Term::Ind(0), app(Term::Constr(0, 1), v(0))),
                        ),
                    ),
                    v(1),
                ),
            ),
        );
        let (prog, entry) = compile(sig.clone(), &erase(&ctx, &plus_src).unwrap());
        let got = run(&prog, entry, &[2, 1], 1_000_000).unwrap();
        assert_eq!(got, 3);
        let applied = app(app(plus_src, nat_lit(2)), nat_lit(1));
        let want = enorm(&sig, &erase(&ctx, &applied).unwrap());
        assert_eq!(decode_to_eterm(&sig, 0, got), want);
    }

    #[test]
    fn straightline_constr_program_structure_matches_logic_reflection() {
        let sig = nat_sig();
        let s = |x: ETerm| ETerm::App(Box::new(ETerm::Constr(0, 1)), Box::new(x));
        let e2 = ETerm::Lam(Box::new(s(ETerm::Var(0))));
        let (prog, entry) = compile(sig.clone(), &e2);
        assert_eq!(entry, 0);
        assert_eq!(prog.funcs.len(), 1);
        assert_eq!(prog.funcs[0].nparams, 1);
        match &prog.funcs[0].body {
            Expr::Let(Op::Constr(i, j, fields), rest) => {
                assert_eq!((*i, *j), (0, 1));
                assert_eq!(fields.as_slice(), [0]);
                assert!(matches!(&**rest, Expr::Ret(1)));
            }
            _ => panic!("unexpected e2 body"),
        }
        let e3 = ETerm::Lam(Box::new(s(s(ETerm::Var(0)))));
        let (prog3, _) = compile(sig, &e3);
        match &prog3.funcs[0].body {
            Expr::Let(Op::Constr(_, _, f0), r0) => {
                assert_eq!(f0.as_slice(), [0]);
                match &**r0 {
                    Expr::Let(Op::Constr(_, _, f1), r1) => {
                        assert_eq!(f1.as_slice(), [1]);
                        assert!(matches!(&**r1, Expr::Ret(2)));
                    }
                    _ => panic!("unexpected e3 inner"),
                }
            }
            _ => panic!("unexpected e3 body"),
        }
    }

    #[test]
    fn rec_identity_program_structure_matches_logic_reflection() {
        let sig = nat_sig();
        let s = |x: ETerm| ETerm::App(Box::new(ETerm::Constr(0, 1)), Box::new(x));
        let step = ETerm::Lam(Box::new(ETerm::Lam(Box::new(s(ETerm::Var(0))))));
        let body = ETerm::App(
            Box::new(ETerm::App(
                Box::new(ETerm::App(
                    Box::new(ETerm::App(Box::new(ETerm::Rec(0)), Box::new(ETerm::Box))),
                    Box::new(ETerm::Constr(0, 0)),
                )),
                Box::new(step),
            )),
            Box::new(ETerm::Var(0)),
        );
        let (prog, entry) = compile(sig, &ETerm::Lam(Box::new(body)));
        assert_eq!(entry, 1);
        assert_eq!(prog.funcs.len(), 2);
        assert_eq!(prog.funcs[1].nparams, 1);
        match &prog.funcs[1].body {
            Expr::Let(Op::Call(f, a), r) => {
                assert_eq!(*f, 0);
                assert_eq!(a.as_slice(), [0, 0]);
                assert!(matches!(&**r, Expr::Ret(1)));
            }
            _ => panic!("entry body"),
        }
        assert_eq!(prog.funcs[0].nparams, 2);
        match &prog.funcs[0].body {
            Expr::Case(i, scrut, branches) => {
                assert_eq!((*i, *scrut), (0, 1));
                assert_eq!(branches.len(), 2);
                assert_eq!(branches[0].nbind, 0);
                match &branches[0].body {
                    Expr::Let(Op::Constr(_, 0, f), r) => {
                        assert!(f.is_empty());
                        assert!(matches!(&**r, Expr::Ret(2)));
                    }
                    _ => panic!("Z branch"),
                }
                assert_eq!(branches[1].nbind, 1);
                match &branches[1].body {
                    Expr::Let(Op::Call(f, a), r0) => {
                        assert_eq!(*f, 0);
                        assert_eq!(a.as_slice(), [0, 2]);
                        match &**r0 {
                            Expr::Let(Op::Constr(_, 1, fl), r1) => {
                                assert_eq!(fl.as_slice(), [3]);
                                assert!(matches!(&**r1, Expr::Ret(4)));
                            }
                            _ => panic!("S inner"),
                        }
                    }
                    _ => panic!("S branch"),
                }
            }
            _ => panic!("rec body"),
        }

        let plus_body = ETerm::App(
            Box::new(ETerm::App(
                Box::new(ETerm::App(
                    Box::new(ETerm::App(Box::new(ETerm::Rec(0)), Box::new(ETerm::Box))),
                    Box::new(ETerm::Var(1)),
                )),
                Box::new(ETerm::Lam(Box::new(ETerm::Lam(Box::new(s(ETerm::Var(0)))))))),
            ),
            Box::new(ETerm::Var(0)),
        );
        let plus = ETerm::Lam(Box::new(ETerm::Lam(Box::new(plus_body))));
        let (pp, pe) = compile(nat_sig(), &plus);
        assert_eq!(pe, 1);
        assert_eq!(pp.funcs[1].nparams, 2);
        assert!(matches!(
            &pp.funcs[1].body,
            Expr::Let(Op::Call(0, a), r)
                if a.as_slice() == [0, 1, 1] && matches!(&**r, Expr::Ret(2))
        ));
        assert_eq!(pp.funcs[0].nparams, 3);
        match &pp.funcs[0].body {
            Expr::Case(0, 2, brs) => {
                assert!(matches!(&brs[0].body, Expr::Ret(0)) && brs[0].nbind == 0);
                assert_eq!(brs[1].nbind, 1);
                match &brs[1].body {
                    Expr::Let(Op::Call(0, a), r0) => {
                        assert_eq!(a.as_slice(), [0, 1, 3]);
                        assert!(matches!(&**r0,
                            Expr::Let(Op::Constr(_, 1, fl), r1)
                                if fl.as_slice() == [4] && matches!(&**r1, Expr::Ret(5))));
                    }
                    _ => panic!("plus S branch"),
                }
            }
            _ => panic!("plus rec body"),
        }
    }

    #[test]
    fn compiles_bool_not_against_evaluator() {
        let sig = bool_sig();
        let ctx = Context::with_sig(sig.clone());
        let not_src = lam(
            Term::Ind(0),
            app(
                app(
                    app(
                        app(Term::Rec(0, 1), lam(Term::Ind(0), Term::Ind(0))),
                        Term::Constr(0, 1),
                    ),
                    Term::Constr(0, 0),
                ),
                v(0),
            ),
        );
        let (prog, entry) = compile(sig.clone(), &erase(&ctx, &not_src).unwrap());
        let tru = encode(&sig, 0, 1, &[]);
        let fls = encode(&sig, 0, 0, &[]);
        let got_t = run(&prog, entry, &[tru], 1000).unwrap();
        let got_f = run(&prog, entry, &[fls], 1000).unwrap();
        assert_eq!(
            decode_to_eterm(&sig, 0, got_t),
            enorm(
                &sig,
                &erase(&ctx, &app(not_src.clone(), Term::Constr(0, 1))).unwrap()
            )
        );
        assert_eq!(
            decode_to_eterm(&sig, 0, got_f),
            enorm(
                &sig,
                &erase(&ctx, &app(not_src, Term::Constr(0, 0))).unwrap()
            )
        );
    }

    #[test]
    fn compiles_even_via_nested_recursors() {
        let sig = nat_bool_sig();
        let ctx = Context::with_sig(sig.clone());
        let not1 = lam(
            Term::Ind(1),
            app(
                app(
                    app(
                        app(Term::Rec(1, 1), lam(Term::Ind(1), Term::Ind(1))),
                        Term::Constr(1, 1),
                    ),
                    Term::Constr(1, 0),
                ),
                v(0),
            ),
        );
        let even_src = lam(
            Term::Ind(0),
            app(
                app(
                    app(
                        app(Term::Rec(0, 1), lam(Term::Ind(0), Term::Ind(1))),
                        Term::Constr(1, 1),
                    ),
                    lam(Term::Ind(0), lam(Term::Ind(1), app(not1, v(0)))),
                ),
                v(0),
            ),
        );
        let (prog, entry) = compile(sig.clone(), &erase(&ctx, &even_src).unwrap());
        let got4 = run(&prog, entry, &[4], 1_000_000).unwrap();
        let got3 = run(&prog, entry, &[3], 1_000_000).unwrap();
        assert_eq!(
            decode_to_eterm(&sig, 1, got4),
            enorm(
                &sig,
                &erase(&ctx, &app(even_src.clone(), nat_lit(4))).unwrap()
            )
        );
        assert_eq!(
            decode_to_eterm(&sig, 1, got3),
            enorm(&sig, &erase(&ctx, &app(even_src, nat_lit(3))).unwrap())
        );
        assert_eq!(decode_to_eterm(&sig, 1, got4), ETerm::Constr(1, 1));
        assert_eq!(decode_to_eterm(&sig, 1, got3), ETerm::Constr(1, 0));
    }

    struct Rng(u64);

    impl Rng {
        fn bits(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn below(&mut self, n: u64) -> u64 {
            self.bits() % n
        }
    }

    #[derive(Clone, Copy, PartialEq)]
    enum Ty {
        Nat,
        Bool,
    }

    fn ty_term(t: Ty) -> Term {
        match t {
            Ty::Nat => Term::Ind(0),
            Ty::Bool => Term::Ind(1),
        }
    }

    fn pick_var(ty: Ty, ctx: &[Ty], rng: &mut Rng) -> Option<Term> {
        let cands: Vec<usize> = (0..ctx.len())
            .filter(|&i| ctx[ctx.len() - 1 - i] == ty)
            .collect();
        if cands.is_empty() {
            None
        } else {
            Some(Term::Var(cands[rng.below(cands.len() as u64) as usize]))
        }
    }

    fn leaf(ty: Ty, ctx: &[Ty], rng: &mut Rng) -> Term {
        if rng.below(2) == 0 {
            if let Some(v) = pick_var(ty, ctx, rng) {
                return v;
            }
        }
        match ty {
            Ty::Nat => nat_lit(rng.below(3) as usize),
            Ty::Bool => Term::Constr(1, rng.below(2) as usize),
        }
    }

    fn gen_nat_rec(ty: Ty, ctx: &mut Vec<Ty>, depth: usize, rng: &mut Rng) -> Term {
        let base = gen(ty, ctx, depth - 1, rng);
        ctx.push(Ty::Nat);
        ctx.push(ty);
        let step = gen(ty, ctx, depth - 1, rng);
        ctx.pop();
        ctx.pop();
        let major = nat_lit(rng.below(3) as usize);
        app(
            app(
                app(app(Term::Rec(0, 1), lam(Term::Ind(0), ty_term(ty))), base),
                lam(Term::Ind(0), lam(ty_term(ty), step)),
            ),
            major,
        )
    }

    fn gen_bool_rec(ty: Ty, ctx: &mut Vec<Ty>, depth: usize, rng: &mut Rng) -> Term {
        let ef = gen(ty, ctx, depth - 1, rng);
        let et = gen(ty, ctx, depth - 1, rng);
        let major = gen(Ty::Bool, ctx, depth - 1, rng);
        app(
            app(
                app(app(Term::Rec(1, 1), lam(Term::Ind(1), ty_term(ty))), ef),
                et,
            ),
            major,
        )
    }

    fn gen(ty: Ty, ctx: &mut Vec<Ty>, depth: usize, rng: &mut Rng) -> Term {
        if depth == 0 || rng.below(3) == 0 {
            return leaf(ty, ctx, rng);
        }
        match ty {
            Ty::Nat => match rng.below(3) {
                0 => app(Term::Constr(0, 1), gen(Ty::Nat, ctx, depth - 1, rng)),
                1 => gen_nat_rec(ty, ctx, depth, rng),
                _ => gen_bool_rec(ty, ctx, depth, rng),
            },
            Ty::Bool => match rng.below(2) {
                0 => gen_nat_rec(ty, ctx, depth, rng),
                _ => gen_bool_rec(ty, ctx, depth, rng),
            },
        }
    }

    #[test]
    fn compiler_matches_evaluator_on_random_first_order_programs() {
        let sig = nat_bool_sig();
        let ctx = Context::with_sig(sig.clone());
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
        for _ in 0..3000 {
            let ty = if rng.below(2) == 0 { Ty::Nat } else { Ty::Bool };
            let mut tctx = Vec::new();
            let t = gen(ty, &mut tctx, 4, &mut rng);
            let e = erase(&ctx, &t).unwrap();
            let (prog, entry) = compile(sig.clone(), &e);
            let i = if ty == Ty::Nat { 0 } else { 1 };
            let got = run(&prog, entry, &[], 50_000_000).unwrap();
            assert_eq!(decode_to_eterm(&sig, i, got), enorm(&sig, &e));
        }
    }
}
