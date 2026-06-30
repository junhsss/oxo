use std::rc::Rc;

pub mod certificate;
pub mod compile;
pub mod logic;
pub mod target;

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Var(usize),
    Universe(u32),
    Prop,
    Pi(Box<Term>, Box<Term>),
    Lam(Box<Term>, Box<Term>),
    App(Box<Term>, Box<Term>),
    Sigma(Box<Term>, Box<Term>),
    Pair(Box<Term>, Box<Term>, Box<Term>),
    Fst(Box<Term>),
    Snd(Box<Term>),
    Ind(usize),
    Constr(usize, usize),
    Rec(usize, u32),
    Axiom(usize),
}

#[derive(Clone)]
pub struct Constructor {
    pub args: Vec<Term>,
    pub index_values: Vec<Term>,
}

#[derive(Clone)]
pub struct Inductive {
    pub params: Vec<Term>,
    pub indices: Vec<Term>,
    pub sort: u32,
    pub constructors: Vec<Constructor>,
}

pub type Sig = Vec<Inductive>;

#[derive(Clone)]
pub enum Value {
    Neutral(Neutral),
    Universe(u32),
    Prop,
    Pi(Rc<Value>, Closure),
    Lam(Rc<Value>, Closure),
    Sigma(Rc<Value>, Closure),
    Pair(Rc<Value>, Rc<Value>, Rc<Value>),
    Ind(usize, Vec<Rc<Value>>),
    Constr(usize, usize, Vec<Rc<Value>>),
    RecApp(usize, u32, Vec<Rc<Value>>),
}

#[derive(Clone)]
pub enum Neutral {
    Var(usize),
    App(Rc<Neutral>, Rc<Value>),
    Fst(Rc<Neutral>),
    Snd(Rc<Neutral>),
    Rec(usize, u32, Vec<Rc<Value>>, Rc<Neutral>),
    Axiom(usize),
}

#[derive(Clone)]
pub struct Closure {
    env: Env,
    body: Term,
    sig: Rc<Sig>,
}

type Env = Vec<Rc<Value>>;

impl Closure {
    fn apply(&self, arg: Rc<Value>) -> Rc<Value> {
        let mut env = self.env.clone();
        env.push(arg);
        eval(&self.sig, &env, &self.body)
    }
}

fn var(level: usize) -> Rc<Value> {
    Rc::new(Value::Neutral(Neutral::Var(level)))
}

fn apply(sig: &Rc<Sig>, f: Rc<Value>, arg: Rc<Value>) -> Rc<Value> {
    match &*f {
        Value::Lam(_, clo) => clo.apply(arg),
        Value::Neutral(n) => Rc::new(Value::Neutral(Neutral::App(Rc::new(n.clone()), arg))),
        Value::Ind(i, sp) => {
            let mut sp2 = sp.clone();
            sp2.push(arg);
            Rc::new(Value::Ind(*i, sp2))
        }
        Value::Constr(i, j, sp) => {
            let mut sp2 = sp.clone();
            sp2.push(arg);
            Rc::new(Value::Constr(*i, *j, sp2))
        }
        Value::RecApp(i, t, sp) => {
            let mut sp2 = sp.clone();
            sp2.push(arg);
            let ind = &sig[*i];
            let arity = ind.params.len() + 1 + ind.constructors.len() + ind.indices.len() + 1;
            if sp2.len() == arity {
                iota(sig, *i, *t, sp2)
            } else {
                Rc::new(Value::RecApp(*i, *t, sp2))
            }
        }
        _ => unreachable!(),
    }
}

fn iota(sig: &Rc<Sig>, i: usize, t: u32, sp: Vec<Rc<Value>>) -> Rc<Value> {
    let ind = &sig[i];
    let np = ind.params.len();
    let k = ind.constructors.len();
    let major = sp.last().unwrap().clone();
    match &*major {
        Value::Constr(_, j, cargs) => {
            let c = &ind.constructors[*j];
            let method = sp[np + 1 + *j].clone();
            let mask = first_order_rec_mask(sig, i, *j);
            let ctor_args: Vec<Rc<Value>> = cargs[np..].to_vec();
            let mut result = method;
            for a in &ctor_args {
                result = apply(sig, result, a.clone());
            }
            for (l, a) in ctor_args.iter().enumerate() {
                if mask[l] {
                    let fixed: Vec<Rc<Value>> = sp[0..np + 1 + k].to_vec();
                    let arg_env: Env = cargs[0..np + l].to_vec();
                    let idx_spine = spine_args(&c.args[l]);
                    let mut ih = Rc::new(Value::RecApp(i, t, fixed));
                    for it in &idx_spine[np..] {
                        ih = apply(sig, ih, eval(sig, &arg_env, it));
                    }
                    ih = apply(sig, ih, a.clone());
                    result = apply(sig, result, ih);
                }
            }
            result
        }
        Value::Neutral(n) => {
            let fixed: Vec<Rc<Value>> = sp[..sp.len() - 1].to_vec();
            Rc::new(Value::Neutral(Neutral::Rec(
                i,
                t,
                fixed,
                Rc::new(n.clone()),
            )))
        }
        _ => unreachable!(),
    }
}

fn proj1(p: Rc<Value>) -> Rc<Value> {
    match &*p {
        Value::Pair(_, a, _) => a.clone(),
        Value::Neutral(n) => Rc::new(Value::Neutral(Neutral::Fst(Rc::new(n.clone())))),
        _ => unreachable!(),
    }
}

fn proj2(p: Rc<Value>) -> Rc<Value> {
    match &*p {
        Value::Pair(_, _, b) => b.clone(),
        Value::Neutral(n) => Rc::new(Value::Neutral(Neutral::Snd(Rc::new(n.clone())))),
        _ => unreachable!(),
    }
}

fn eval(sig: &Rc<Sig>, env: &Env, term: &Term) -> Rc<Value> {
    match term {
        Term::Var(i) => env[env.len() - 1 - i].clone(),
        Term::Universe(n) => Rc::new(Value::Universe(*n)),
        Term::Prop => Rc::new(Value::Prop),
        Term::Pi(a, b) => Rc::new(Value::Pi(
            eval(sig, env, a),
            Closure {
                env: env.clone(),
                body: (**b).clone(),
                sig: sig.clone(),
            },
        )),
        Term::Lam(a, t) => Rc::new(Value::Lam(
            eval(sig, env, a),
            Closure {
                env: env.clone(),
                body: (**t).clone(),
                sig: sig.clone(),
            },
        )),
        Term::App(f, x) => apply(sig, eval(sig, env, f), eval(sig, env, x)),
        Term::Sigma(a, b) => Rc::new(Value::Sigma(
            eval(sig, env, a),
            Closure {
                env: env.clone(),
                body: (**b).clone(),
                sig: sig.clone(),
            },
        )),
        Term::Pair(s, a, b) => Rc::new(Value::Pair(
            eval(sig, env, s),
            eval(sig, env, a),
            eval(sig, env, b),
        )),
        Term::Fst(p) => proj1(eval(sig, env, p)),
        Term::Snd(p) => proj2(eval(sig, env, p)),
        Term::Ind(i) => Rc::new(Value::Ind(*i, Vec::new())),
        Term::Constr(i, j) => Rc::new(Value::Constr(*i, *j, Vec::new())),
        Term::Rec(i, t) => Rc::new(Value::RecApp(*i, *t, Vec::new())),
        Term::Axiom(i) => Rc::new(Value::Neutral(Neutral::Axiom(*i))),
    }
}

fn quote(level: usize, value: &Rc<Value>) -> Term {
    match &**value {
        Value::Neutral(n) => quote_neutral(level, n),
        Value::Universe(n) => Term::Universe(*n),
        Value::Prop => Term::Prop,
        Value::Pi(a, clo) => Term::Pi(
            Box::new(quote(level, a)),
            Box::new(quote(level + 1, &clo.apply(var(level)))),
        ),
        Value::Lam(a, clo) => Term::Lam(
            Box::new(quote(level, a)),
            Box::new(quote(level + 1, &clo.apply(var(level)))),
        ),
        Value::Sigma(a, clo) => Term::Sigma(
            Box::new(quote(level, a)),
            Box::new(quote(level + 1, &clo.apply(var(level)))),
        ),
        Value::Pair(s, a, b) => Term::Pair(
            Box::new(quote(level, s)),
            Box::new(quote(level, a)),
            Box::new(quote(level, b)),
        ),
        Value::Ind(i, sp) => quote_spine(level, Term::Ind(*i), sp),
        Value::Constr(i, j, sp) => quote_spine(level, Term::Constr(*i, *j), sp),
        Value::RecApp(i, t, sp) => quote_spine(level, Term::Rec(*i, *t), sp),
    }
}

fn quote_spine(level: usize, head: Term, spine: &[Rc<Value>]) -> Term {
    let mut out = head;
    for a in spine {
        out = Term::App(Box::new(out), Box::new(quote(level, a)));
    }
    out
}

fn quote_neutral(level: usize, neutral: &Neutral) -> Term {
    match neutral {
        Neutral::Var(l) => Term::Var(level - 1 - l),
        Neutral::App(f, a) => {
            Term::App(Box::new(quote_neutral(level, f)), Box::new(quote(level, a)))
        }
        Neutral::Fst(n) => Term::Fst(Box::new(quote_neutral(level, n))),
        Neutral::Snd(n) => Term::Snd(Box::new(quote_neutral(level, n))),
        Neutral::Rec(i, t, fixed, major) => {
            let head = quote_spine(level, Term::Rec(*i, *t), fixed);
            Term::App(Box::new(head), Box::new(quote_neutral(level, major)))
        }
        Neutral::Axiom(i) => Term::Axiom(*i),
    }
}

fn level_of_sort(sort: &Value) -> u32 {
    match sort {
        Value::Prop => 0,
        Value::Universe(n) => n + 1,
        _ => unreachable!(),
    }
}

fn sort_value(level: u32) -> Value {
    if level == 0 {
        Value::Prop
    } else {
        Value::Universe(level - 1)
    }
}

fn type_of_neutral(ctx: &Context, neutral: &Neutral) -> Rc<Value> {
    match neutral {
        Neutral::Var(l) => ctx.types[*l].clone(),
        Neutral::App(f, a) => match &*type_of_neutral(ctx, f) {
            Value::Pi(_, clo) => clo.apply(a.clone()),
            _ => unreachable!(),
        },
        Neutral::Fst(p) => match &*type_of_neutral(ctx, p) {
            Value::Sigma(fst_ty, _) => fst_ty.clone(),
            _ => unreachable!(),
        },
        Neutral::Snd(p) => match &*type_of_neutral(ctx, p) {
            Value::Sigma(_, clo) => clo.apply(proj1(Rc::new(Value::Neutral((**p).clone())))),
            _ => unreachable!(),
        },
        Neutral::Rec(i, _, fixed, major) => {
            let np = ctx.sig[*i].params.len();
            let k = ctx.sig[*i].constructors.len();
            let mut ty = fixed[np].clone();
            for idx in &fixed[np + 1 + k..] {
                ty = apply(&ctx.sig, ty, idx.clone());
            }
            apply(&ctx.sig, ty, Rc::new(Value::Neutral((**major).clone())))
        }
        Neutral::Axiom(i) => eval(&ctx.sig, &Vec::new(), &ctx.axioms[*i]),
    }
}

fn sort_level_of_type(ctx: &Context, ty: &Rc<Value>) -> u32 {
    match &**ty {
        Value::Prop => 1,
        Value::Universe(n) => n + 2,
        Value::Pi(a, clo) => {
            let domain = sort_level_of_type(ctx, a);
            let extended = ctx.bind(a.clone());
            let codomain = sort_level_of_type(&extended, &clo.apply(var(ctx.level)));
            if codomain == 0 {
                0
            } else {
                domain.max(codomain)
            }
        }
        Value::Sigma(a, clo) => {
            let domain = sort_level_of_type(ctx, a);
            let extended = ctx.bind(a.clone());
            let codomain = sort_level_of_type(&extended, &clo.apply(var(ctx.level)));
            domain.max(codomain)
        }
        Value::Neutral(n) => level_of_sort(&type_of_neutral(ctx, n)),
        Value::Ind(i, _) => ctx.sig[*i].sort,
        _ => unreachable!(),
    }
}

fn is_prop(ctx: &Context, ty: &Rc<Value>) -> bool {
    sort_level_of_type(ctx, ty) == 0
}

fn conv(ctx: &Context, ty: &Rc<Value>, x: &Rc<Value>, y: &Rc<Value>) -> bool {
    if is_prop(ctx, ty) {
        return true;
    }
    match &**ty {
        Value::Pi(a, clo) => {
            let v = var(ctx.level);
            let extended = ctx.bind(a.clone());
            conv(
                &extended,
                &clo.apply(v.clone()),
                &apply(&ctx.sig, x.clone(), v.clone()),
                &apply(&ctx.sig, y.clone(), v),
            )
        }
        Value::Sigma(a, clo) => {
            let x1 = proj1(x.clone());
            let y1 = proj1(y.clone());
            conv(ctx, a, &x1, &y1) && {
                let snd_ty = clo.apply(x1);
                conv(ctx, &snd_ty, &proj2(x.clone()), &proj2(y.clone()))
            }
        }
        _ => conv_nf(ctx, x, y),
    }
}

fn conv_nf(ctx: &Context, x: &Rc<Value>, y: &Rc<Value>) -> bool {
    match (&**x, &**y) {
        (Value::Universe(a), Value::Universe(b)) => a == b,
        (Value::Prop, Value::Prop) => true,
        (Value::Pi(a1, c1), Value::Pi(a2, c2)) | (Value::Sigma(a1, c1), Value::Sigma(a2, c2)) => {
            conv_nf(ctx, a1, a2) && {
                let extended = ctx.bind(a1.clone());
                conv_nf(
                    &extended,
                    &c1.apply(var(ctx.level)),
                    &c2.apply(var(ctx.level)),
                )
            }
        }
        (Value::Neutral(n1), Value::Neutral(n2)) => conv_neutral(ctx, n1, n2).is_some(),
        (Value::Ind(i1, s1), Value::Ind(i2, s2)) => i1 == i2 && conv_spine(ctx, s1, s2),
        (Value::Constr(i1, j1, s1), Value::Constr(i2, j2, s2)) => {
            i1 == i2 && j1 == j2 && conv_spine(ctx, s1, s2)
        }
        (Value::RecApp(i1, t1, s1), Value::RecApp(i2, t2, s2)) => {
            i1 == i2 && t1 == t2 && conv_spine(ctx, s1, s2)
        }
        (Value::Lam(a1, c1), Value::Lam(_, c2)) => {
            let extended = ctx.bind(a1.clone());
            conv_nf(
                &extended,
                &c1.apply(var(ctx.level)),
                &c2.apply(var(ctx.level)),
            )
        }
        (Value::Lam(a1, c1), Value::Neutral(_)) => {
            let extended = ctx.bind(a1.clone());
            conv_nf(
                &extended,
                &c1.apply(var(ctx.level)),
                &apply(&ctx.sig, y.clone(), var(ctx.level)),
            )
        }
        (Value::Neutral(_), Value::Lam(a2, c2)) => {
            let extended = ctx.bind(a2.clone());
            conv_nf(
                &extended,
                &apply(&ctx.sig, x.clone(), var(ctx.level)),
                &c2.apply(var(ctx.level)),
            )
        }
        (Value::Pair(_, a1, b1), Value::Pair(_, a2, b2)) => {
            conv_nf(ctx, a1, a2) && conv_nf(ctx, b1, b2)
        }
        _ => false,
    }
}

fn conv_spine(ctx: &Context, x: &[Rc<Value>], y: &[Rc<Value>]) -> bool {
    x.len() == y.len() && x.iter().zip(y).all(|(a, b)| conv_nf(ctx, a, b))
}

fn conv_neutral(ctx: &Context, x: &Neutral, y: &Neutral) -> Option<Rc<Value>> {
    match (x, y) {
        (Neutral::Var(i), Neutral::Var(j)) => {
            if i == j {
                Some(ctx.types[*i].clone())
            } else {
                None
            }
        }
        (Neutral::App(f1, a1), Neutral::App(f2, a2)) => match &*conv_neutral(ctx, f1, f2)? {
            Value::Pi(dom, clo) if conv(ctx, dom, a1, a2) => Some(clo.apply(a1.clone())),
            _ => None,
        },
        (Neutral::Fst(p1), Neutral::Fst(p2)) => match &*conv_neutral(ctx, p1, p2)? {
            Value::Sigma(fst_ty, _) => Some(fst_ty.clone()),
            _ => None,
        },
        (Neutral::Snd(p1), Neutral::Snd(p2)) => match &*conv_neutral(ctx, p1, p2)? {
            Value::Sigma(_, clo) => Some(clo.apply(proj1(Rc::new(Value::Neutral((**p1).clone()))))),
            _ => None,
        },
        (Neutral::Rec(i1, t1, f1, m1), Neutral::Rec(i2, t2, f2, m2)) => {
            if i1 == i2
                && t1 == t2
                && conv_spine(ctx, f1, f2)
                && conv_neutral(ctx, m1, m2).is_some()
            {
                Some(type_of_neutral(ctx, x))
            } else {
                None
            }
        }
        (Neutral::Axiom(i), Neutral::Axiom(j)) => {
            if i == j {
                Some(type_of_neutral(ctx, x))
            } else {
                None
            }
        }
        _ => None,
    }
}

#[derive(Clone)]
pub struct Context {
    env: Env,
    types: Vec<Rc<Value>>,
    level: usize,
    sig: Rc<Sig>,
    axioms: Rc<Vec<Term>>,
}

impl Context {
    pub fn new() -> Self {
        Self::with_sig(Rc::new(Vec::new()))
    }

    pub fn with_sig(sig: Rc<Sig>) -> Self {
        Self::with_sig_and_axioms(sig, Rc::new(Vec::new()))
    }

    pub fn with_sig_and_axioms(sig: Rc<Sig>, axioms: Rc<Vec<Term>>) -> Self {
        Context {
            env: Vec::new(),
            types: Vec::new(),
            level: 0,
            sig,
            axioms,
        }
    }

    fn bind(&self, ty: Rc<Value>) -> Self {
        let mut next = self.clone();
        next.env.push(var(self.level));
        next.types.push(ty);
        next.level += 1;
        next
    }
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

pub fn infer(ctx: &Context, term: &Term) -> Result<Rc<Value>, String> {
    match term {
        Term::Var(i) => {
            if *i < ctx.types.len() {
                Ok(ctx.types[ctx.types.len() - 1 - i].clone())
            } else {
                Err(format!("unbound variable {}", i))
            }
        }
        Term::Universe(n) => Ok(Rc::new(Value::Universe(n + 1))),
        Term::Prop => Ok(Rc::new(Value::Universe(0))),
        Term::Pi(a, b) => {
            let domain = infer_sort(ctx, a)?;
            let av = eval(&ctx.sig, &ctx.env, a);
            let codomain = infer_sort(&ctx.bind(av), b)?;
            let s = if codomain == 0 {
                0
            } else {
                domain.max(codomain)
            };
            Ok(Rc::new(sort_value(s)))
        }
        Term::Lam(a, t) => {
            infer_sort(ctx, a)?;
            let av = eval(&ctx.sig, &ctx.env, a);
            let extended = ctx.bind(av.clone());
            let body_ty = infer(&extended, t)?;
            let codomain = quote(extended.level, &body_ty);
            Ok(Rc::new(Value::Pi(
                av,
                Closure {
                    env: ctx.env.clone(),
                    body: codomain,
                    sig: ctx.sig.clone(),
                },
            )))
        }
        Term::App(f, x) => {
            let ft = infer(ctx, f)?;
            match &*ft {
                Value::Pi(a, clo) => {
                    check(ctx, x, a)?;
                    Ok(clo.apply(eval(&ctx.sig, &ctx.env, x)))
                }
                _ => Err("application of a non-function".to_string()),
            }
        }
        Term::Sigma(a, b) => {
            let domain = infer_sort(ctx, a)?;
            let av = eval(&ctx.sig, &ctx.env, a);
            let codomain = infer_sort(&ctx.bind(av), b)?;
            Ok(Rc::new(sort_value(domain.max(codomain))))
        }
        Term::Pair(s, a, b) => {
            infer_sort(ctx, s)?;
            let sv = eval(&ctx.sig, &ctx.env, s);
            match &*sv {
                Value::Sigma(fst_ty, clo) => {
                    check(ctx, a, fst_ty)?;
                    let snd_ty = clo.apply(eval(&ctx.sig, &ctx.env, a));
                    check(ctx, b, &snd_ty)?;
                    Ok(sv.clone())
                }
                _ => Err("pair annotated with a non-Σ type".to_string()),
            }
        }
        Term::Fst(p) => {
            let pt = infer(ctx, p)?;
            match &*pt {
                Value::Sigma(fst_ty, _) => Ok(fst_ty.clone()),
                _ => Err("fst of a non-pair".to_string()),
            }
        }
        Term::Snd(p) => {
            let pt = infer(ctx, p)?;
            match &*pt {
                Value::Sigma(_, clo) => Ok(clo.apply(proj1(eval(&ctx.sig, &ctx.env, p)))),
                _ => Err("snd of a non-pair".to_string()),
            }
        }
        Term::Ind(i) => {
            if *i >= ctx.sig.len() {
                return Err(format!("unknown inductive {}", i));
            }
            Ok(eval(&ctx.sig, &Vec::new(), &ind_type_term(&ctx.sig, *i)))
        }
        Term::Constr(i, j) => {
            if *i >= ctx.sig.len() || *j >= ctx.sig[*i].constructors.len() {
                return Err(format!("unknown constructor {}.{}", i, j));
            }
            Ok(eval(
                &ctx.sig,
                &Vec::new(),
                &constr_type_term(&ctx.sig, *i, *j),
            ))
        }
        Term::Rec(i, t) => {
            if *i >= ctx.sig.len() {
                return Err(format!("unknown inductive {}", i));
            }
            if ctx.sig[*i].sort == 0 && *t != 0 && !is_subsingleton(&ctx.sig, *i) {
                return Err("large elimination from a non-subsingleton Prop".to_string());
            }
            Ok(eval(
                &ctx.sig,
                &Vec::new(),
                &rec_type_term(&ctx.sig, *i, *t),
            ))
        }
        Term::Axiom(i) => {
            if *i >= ctx.axioms.len() {
                return Err(format!("unknown axiom {}", i));
            }
            Ok(eval(&ctx.sig, &Vec::new(), &ctx.axioms[*i]))
        }
    }
}

fn infer_sort(ctx: &Context, term: &Term) -> Result<u32, String> {
    let t = infer(ctx, term)?;
    match &*t {
        Value::Prop | Value::Universe(_) => Ok(level_of_sort(&t)),
        _ => Err("expected a type".to_string()),
    }
}

pub fn check(ctx: &Context, term: &Term, expected: &Rc<Value>) -> Result<(), String> {
    let inferred = infer(ctx, term)?;
    if conv_nf(ctx, &inferred, expected) {
        Ok(())
    } else {
        Err(format!(
            "type mismatch: inferred {:?}, expected {:?}",
            quote(ctx.level, &inferred),
            quote(ctx.level, expected)
        ))
    }
}

fn sort_term(level: u32) -> Term {
    if level == 0 {
        Term::Prop
    } else {
        Term::Universe(level - 1)
    }
}

fn pis(tele: &[Term], body: Term) -> Term {
    let mut out = body;
    for a in tele.iter().rev() {
        out = Term::Pi(Box::new(a.clone()), Box::new(out));
    }
    out
}

fn apps(head: Term, args: &[Term]) -> Term {
    let mut out = head;
    for a in args {
        out = Term::App(Box::new(out), Box::new(a.clone()));
    }
    out
}

fn lift(d: usize, c: usize, term: &Term) -> Term {
    match term {
        Term::Var(k) => Term::Var(if *k >= c { k + d } else { *k }),
        Term::Universe(n) => Term::Universe(*n),
        Term::Prop => Term::Prop,
        Term::Ind(i) => Term::Ind(*i),
        Term::Constr(i, j) => Term::Constr(*i, *j),
        Term::Rec(i, t) => Term::Rec(*i, *t),
        Term::Axiom(i) => Term::Axiom(*i),
        Term::Pi(a, b) => Term::Pi(Box::new(lift(d, c, a)), Box::new(lift(d, c + 1, b))),
        Term::Lam(a, b) => Term::Lam(Box::new(lift(d, c, a)), Box::new(lift(d, c + 1, b))),
        Term::Sigma(a, b) => Term::Sigma(Box::new(lift(d, c, a)), Box::new(lift(d, c + 1, b))),
        Term::App(f, x) => Term::App(Box::new(lift(d, c, f)), Box::new(lift(d, c, x))),
        Term::Pair(s, a, b) => Term::Pair(
            Box::new(lift(d, c, s)),
            Box::new(lift(d, c, a)),
            Box::new(lift(d, c, b)),
        ),
        Term::Fst(p) => Term::Fst(Box::new(lift(d, c, p))),
        Term::Snd(p) => Term::Snd(Box::new(lift(d, c, p))),
    }
}

fn ind_type_term(sig: &Sig, i: usize) -> Term {
    let ind = &sig[i];
    let mut tele = ind.params.clone();
    tele.extend(ind.indices.clone());
    pis(&tele, sort_term(ind.sort))
}

fn constr_type_term(sig: &Sig, i: usize, j: usize) -> Term {
    let ind = &sig[i];
    let c = &ind.constructors[j];
    let np = ind.params.len();
    let na = c.args.len();
    let mut result_args = Vec::new();
    for p in 0..np {
        result_args.push(Term::Var(na + np - 1 - p));
    }
    result_args.extend(c.index_values.clone());
    let result = apps(Term::Ind(i), &result_args);
    let mut tele = ind.params.clone();
    tele.extend(c.args.clone());
    pis(&tele, result)
}

fn method_type_term(sig: &Sig, i: usize, j: usize) -> Term {
    let ind = &sig[i];
    let c = &ind.constructors[j];
    let np = ind.params.len();
    let m = c.args.len();
    let mask: Vec<bool> = (0..m).map(|l| ind_head(&c.args[l]) == Some(i)).collect();
    let nrec = mask.iter().filter(|b| **b).count();

    let mut cargs_terms = Vec::new();
    for p in 0..np {
        cargs_terms.push(Term::Var(nrec + m + j + 1 + (np - 1 - p)));
    }
    for l in 0..m {
        cargs_terms.push(Term::Var(nrec + (m - 1 - l)));
    }
    let cj_applied = apps(Term::Constr(i, j), &cargs_terms);
    let mut motive_args: Vec<Term> = c
        .index_values
        .iter()
        .map(|iv| lift(nrec, 0, &lift(j + 1, m, iv)))
        .collect();
    motive_args.push(cj_applied);
    let body = apps(Term::Var(nrec + m + j), &motive_args);

    let recpos: Vec<usize> = (0..m).filter(|l| mask[*l]).collect();
    let mut ih_types = Vec::new();
    for (q, &l) in recpos.iter().enumerate() {
        let motive_at = q + m + j;
        let arg_ref = q + (m - 1 - l);
        let idx_spine = spine_args(&c.args[l]);
        let mut ih_args: Vec<Term> = idx_spine[np..]
            .iter()
            .map(|it| lift(j + 1, q + m, &lift(q + m - l, 0, it)))
            .collect();
        ih_args.push(Term::Var(arg_ref));
        ih_types.push(apps(Term::Var(motive_at), &ih_args));
    }

    let mut out = body;
    for ih in ih_types.iter().rev() {
        out = Term::Pi(Box::new(ih.clone()), Box::new(out));
    }
    for l in (0..m).rev() {
        out = Term::Pi(Box::new(lift(1 + j, l, &c.args[l])), Box::new(out));
    }
    out
}

fn rec_type_term(sig: &Sig, i: usize, t: u32) -> Term {
    let ind = &sig[i];
    let np = ind.params.len();
    let k = ind.constructors.len();
    let ni = ind.indices.len();

    let mut motive_inner_args = Vec::new();
    for p in 0..np {
        motive_inner_args.push(Term::Var(ni + (np - 1 - p)));
    }
    for d in 0..ni {
        motive_inner_args.push(Term::Var(ni - 1 - d));
    }
    let motive_codomain = Term::Pi(
        Box::new(apps(Term::Ind(i), &motive_inner_args)),
        Box::new(sort_term(t)),
    );
    let motive_type = pis(&ind.indices, motive_codomain);

    let rec_indices: Vec<Term> = (0..ni).map(|d| lift(1 + k, d, &ind.indices[d])).collect();

    let mut major_args = Vec::new();
    for p in 0..np {
        major_args.push(Term::Var(ni + (1 + k) + (np - 1 - p)));
    }
    for d in 0..ni {
        major_args.push(Term::Var(ni - 1 - d));
    }
    let major_type = apps(Term::Ind(i), &major_args);

    let mut result_args = Vec::new();
    for d in 0..ni {
        result_args.push(Term::Var(ni - d));
    }
    result_args.push(Term::Var(0));
    let result = apps(Term::Var(ni + k + 1), &result_args);

    let mut tele = ind.params.clone();
    tele.push(motive_type);
    for j in 0..k {
        tele.push(method_type_term(sig, i, j));
    }
    tele.extend(rec_indices);
    tele.push(major_type);
    pis(&tele, result)
}

pub(crate) fn ind_head(term: &Term) -> Option<usize> {
    let mut t = term;
    loop {
        match t {
            Term::App(f, _) => t = f,
            Term::Ind(i) => return Some(*i),
            _ => return None,
        }
    }
}

fn spine_args(term: &Term) -> Vec<Term> {
    let mut out = Vec::new();
    let mut t = term;
    while let Term::App(f, x) = t {
        out.push((**x).clone());
        t = f;
    }
    out.reverse();
    out
}

fn occurs_ind(i: usize, term: &Term) -> bool {
    match term {
        Term::Var(_) | Term::Universe(_) | Term::Prop | Term::Axiom(_) => false,
        Term::Ind(j) => *j == i,
        Term::Constr(j, _) => *j == i,
        Term::Rec(j, _) => *j == i,
        Term::Pi(a, b) | Term::Lam(a, b) | Term::Sigma(a, b) => {
            occurs_ind(i, a) || occurs_ind(i, b)
        }
        Term::App(f, x) => occurs_ind(i, f) || occurs_ind(i, x),
        Term::Pair(s, a, b) => occurs_ind(i, s) || occurs_ind(i, a) || occurs_ind(i, b),
        Term::Fst(p) | Term::Snd(p) => occurs_ind(i, p),
    }
}

fn strictly_positive(i: usize, t: &Term) -> bool {
    match t {
        Term::Pi(a, b) => !occurs_ind(i, a) && strictly_positive(i, b),
        _ => match ind_head(t) {
            Some(h) if h == i => {
                let mut cur = t;
                while let Term::App(f, x) = cur {
                    if occurs_ind(i, x) {
                        return false;
                    }
                    cur = f;
                }
                true
            }
            _ => !occurs_ind(i, t),
        },
    }
}

fn is_subsingleton(sig: &Rc<Sig>, i: usize) -> bool {
    let ind = &sig[i];
    if ind.constructors.len() > 1 {
        return false;
    }
    if ind.constructors.is_empty() {
        return true;
    }
    let mut ctx = Context::with_sig(sig.clone());
    for p in &ind.params {
        if infer_sort(&ctx, p).is_err() {
            return false;
        }
        let pv = eval(&ctx.sig, &ctx.env, p);
        ctx = ctx.bind(pv);
    }
    for a in &ind.constructors[0].args {
        if infer_sort(&ctx, a) != Ok(0) {
            return false;
        }
        let av = eval(&ctx.sig, &ctx.env, a);
        ctx = ctx.bind(av);
    }
    true
}

fn first_order_rec_mask(sig: &Sig, i: usize, j: usize) -> Vec<bool> {
    sig[i].constructors[j]
        .args
        .iter()
        .map(|a| ind_head(a) == Some(i))
        .collect()
}

fn collect_ind_refs(t: &Term, out: &mut [bool]) {
    match t {
        Term::Ind(j) | Term::Constr(j, _) | Term::Rec(j, _) => {
            if *j < out.len() {
                out[*j] = true;
            }
        }
        Term::Pi(a, b) | Term::Lam(a, b) | Term::Sigma(a, b) => {
            collect_ind_refs(a, out);
            collect_ind_refs(b, out);
        }
        Term::App(f, x) => {
            collect_ind_refs(f, out);
            collect_ind_refs(x, out);
        }
        Term::Pair(s, a, b) => {
            collect_ind_refs(s, out);
            collect_ind_refs(a, out);
            collect_ind_refs(b, out);
        }
        Term::Fst(p) | Term::Snd(p) => collect_ind_refs(p, out),
        _ => {}
    }
}

fn ancestors_of(sig: &Rc<Sig>, target: usize) -> Vec<bool> {
    let len = sig.len();
    let mut refs: Vec<Vec<bool>> = Vec::with_capacity(len);
    for a in 0..len {
        let mut row = vec![false; len];
        let ind = &sig[a];
        for p in &ind.params {
            collect_ind_refs(p, &mut row);
        }
        for d in &ind.indices {
            collect_ind_refs(d, &mut row);
        }
        for c in &ind.constructors {
            for arg in &c.args {
                collect_ind_refs(arg, &mut row);
            }
            for iv in &c.index_values {
                collect_ind_refs(iv, &mut row);
            }
        }
        refs.push(row);
    }
    let mut anc = vec![false; len];
    anc[target] = true;
    let mut stack = vec![target];
    while let Some(x) = stack.pop() {
        for k in 0..len {
            if refs[k][x] && !anc[k] {
                anc[k] = true;
                stack.push(k);
            }
        }
    }
    anc
}

fn check_inductive(sig: &Rc<Sig>, i: usize) -> Result<(), String> {
    let ind = &sig[i];
    let np = ind.params.len();
    let anc = ancestors_of(sig, i);
    let mut ctx = Context::with_sig(sig.clone());
    for p in &ind.params {
        infer_sort(&ctx, p)?;
        let pv = eval(&ctx.sig, &ctx.env, p);
        ctx = ctx.bind(pv);
    }
    let mut ictx = ctx.clone();
    for d in &ind.indices {
        infer_sort(&ictx, d)?;
        let dv = eval(&ictx.sig, &ictx.env, d);
        ictx = ictx.bind(dv);
    }
    for (j, c) in ind.constructors.iter().enumerate() {
        if c.index_values.len() != ind.indices.len() {
            return Err(format!("constructor {}.{} index arity mismatch", i, j));
        }
        let mut cctx = ctx.clone();
        for a in &c.args {
            let s = infer_sort(&cctx, a)?;
            if s > ind.sort {
                return Err(format!(
                    "constructor {}.{} argument sort {} exceeds inductive sort {}",
                    i, j, s, ind.sort
                ));
            }
            for k in 0..sig.len() {
                if !anc[k] {
                    continue;
                }
                if !strictly_positive(k, a) {
                    return Err(format!(
                        "constructor {}.{} is not strictly positive in mutually-recursive inductive {}",
                        i, j, k
                    ));
                }
                if occurs_ind(k, a) && ind_head(a) != Some(k) {
                    return Err(format!(
                        "constructor {}.{} uses unsupported higher-order or nested recursion of inductive {}",
                        i, j, k
                    ));
                }
            }
            if ind_head(a) == Some(i) {
                let spine = spine_args(a);
                if spine.len() < np {
                    return Err(format!(
                        "constructor {}.{} recursive occurrence is not fully applied to the parameters",
                        i, j
                    ));
                }
                for p in 0..np {
                    if spine[p] != Term::Var(cctx.level - 1 - p) {
                        return Err(format!(
                            "constructor {}.{} recursive occurrence does not reuse parameter {} uniformly",
                            i, j, p
                        ));
                    }
                }
            }
            let av = eval(&cctx.sig, &cctx.env, a);
            cctx = cctx.bind(av);
        }
        let mut idx_env: Env = cctx.env[..np].to_vec();
        for d in 0..ind.indices.len() {
            let expected = eval(&cctx.sig, &idx_env, &ind.indices[d]);
            check(&cctx, &c.index_values[d], &expected)?;
            idx_env.push(eval(&cctx.sig, &cctx.env, &c.index_values[d]));
        }
    }
    Ok(())
}

pub fn check_signature(sig: &Rc<Sig>) -> Result<(), String> {
    for i in 0..sig.len() {
        check_inductive(sig, i)?;
    }
    Ok(())
}

pub fn check_axioms(sig: &Rc<Sig>, axioms: &Rc<Vec<Term>>) -> Result<(), String> {
    let ctx = Context::with_sig_and_axioms(sig.clone(), axioms.clone());
    for (i, ty) in axioms.iter().enumerate() {
        if infer_sort(&ctx, ty)? != 0 {
            return Err(format!("axiom {} type is not a proposition", i));
        }
    }
    Ok(())
}

pub fn normalize(term: &Term) -> Term {
    quote(0, &eval(&Rc::new(Vec::new()), &Vec::new(), term))
}

#[derive(Clone, Debug, PartialEq)]
pub enum ETerm {
    Box,
    Var(usize),
    Lam(Box<ETerm>),
    App(Box<ETerm>, Box<ETerm>),
    Pair(Box<ETerm>, Box<ETerm>),
    Fst(Box<ETerm>),
    Snd(Box<ETerm>),
    Constr(usize, usize),
    Rec(usize),
}

fn is_arity(ctx: &Context, ty: &Rc<Value>) -> bool {
    match &**ty {
        Value::Universe(_) | Value::Prop => true,
        Value::Pi(a, clo) => {
            let extended = ctx.bind(a.clone());
            is_arity(&extended, &clo.apply(var(ctx.level)))
        }
        _ => false,
    }
}

fn is_erasable(ctx: &Context, t: &Term) -> Result<bool, String> {
    let ty = infer(ctx, t)?;
    Ok(is_arity(ctx, &ty) || is_prop(ctx, &ty))
}

pub fn erase(ctx: &Context, t: &Term) -> Result<ETerm, String> {
    if is_erasable(ctx, t)? {
        return Ok(ETerm::Box);
    }
    match t {
        Term::Var(i) => Ok(ETerm::Var(*i)),
        Term::Lam(a, b) => {
            let av = eval(&ctx.sig, &ctx.env, a);
            let extended = ctx.bind(av);
            Ok(ETerm::Lam(Box::new(erase(&extended, b)?)))
        }
        Term::App(f, x) => Ok(ETerm::App(
            Box::new(erase(ctx, f)?),
            Box::new(erase(ctx, x)?),
        )),
        Term::Pair(_, a, b) => Ok(ETerm::Pair(
            Box::new(erase(ctx, a)?),
            Box::new(erase(ctx, b)?),
        )),
        Term::Fst(p) => Ok(ETerm::Fst(Box::new(erase(ctx, p)?))),
        Term::Snd(p) => Ok(ETerm::Snd(Box::new(erase(ctx, p)?))),
        Term::Constr(i, j) => Ok(ETerm::Constr(*i, *j)),
        Term::Rec(i, _) => Ok(ETerm::Rec(*i)),
        _ => unreachable!(),
    }
}

#[derive(Clone)]
pub enum EValue {
    Box,
    Neutral(ENeutral),
    Lam(EClosure),
    Pair(Rc<EValue>, Rc<EValue>),
    Constr(usize, usize, Vec<Rc<EValue>>),
    RecApp(usize, Vec<Rc<EValue>>),
}

#[derive(Clone)]
pub enum ENeutral {
    Var(usize),
    App(Rc<ENeutral>, Rc<EValue>),
    Fst(Rc<ENeutral>),
    Snd(Rc<ENeutral>),
    Rec(usize, Vec<Rc<EValue>>, Rc<ENeutral>),
}

#[derive(Clone)]
pub struct EClosure {
    env: EEnv,
    body: ETerm,
    sig: Rc<Sig>,
}

type EEnv = Vec<Rc<EValue>>;

impl EClosure {
    fn apply(&self, arg: Rc<EValue>) -> Rc<EValue> {
        let mut env = self.env.clone();
        env.push(arg);
        eeval(&self.sig, &env, &self.body)
    }
}

fn evar(level: usize) -> Rc<EValue> {
    Rc::new(EValue::Neutral(ENeutral::Var(level)))
}

fn eapply(sig: &Rc<Sig>, f: Rc<EValue>, arg: Rc<EValue>) -> Rc<EValue> {
    match &*f {
        EValue::Box => Rc::new(EValue::Box),
        EValue::Lam(clo) => clo.apply(arg),
        EValue::Neutral(n) => Rc::new(EValue::Neutral(ENeutral::App(Rc::new(n.clone()), arg))),
        EValue::Constr(i, j, sp) => {
            let mut sp2 = sp.clone();
            sp2.push(arg);
            Rc::new(EValue::Constr(*i, *j, sp2))
        }
        EValue::RecApp(i, sp) => {
            let mut sp2 = sp.clone();
            sp2.push(arg);
            let ind = &sig[*i];
            let arity = ind.params.len() + 1 + ind.constructors.len() + ind.indices.len() + 1;
            if sp2.len() == arity {
                eiota(sig, *i, sp2)
            } else {
                Rc::new(EValue::RecApp(*i, sp2))
            }
        }
        EValue::Pair(..) => unreachable!(),
    }
}

fn eindex(sig: &Rc<Sig>, env: &EEnv, term: &Term) -> Rc<EValue> {
    match term {
        Term::Var(i) => env[env.len() - 1 - i].clone(),
        Term::Constr(i, j) => Rc::new(EValue::Constr(*i, *j, Vec::new())),
        Term::App(f, x) => eapply(sig, eindex(sig, env, f), eindex(sig, env, x)),
        Term::Ind(_) | Term::Universe(_) | Term::Prop | Term::Pi(..) | Term::Sigma(..) => {
            Rc::new(EValue::Box)
        }
        _ => unreachable!(),
    }
}

fn eiota(sig: &Rc<Sig>, i: usize, sp: Vec<Rc<EValue>>) -> Rc<EValue> {
    let ind = &sig[i];
    let np = ind.params.len();
    let k = ind.constructors.len();
    let major = sp.last().unwrap().clone();
    match &*major {
        EValue::Constr(_, j, cargs) => {
            let c = &ind.constructors[*j];
            let method = sp[np + 1 + *j].clone();
            let mask = first_order_rec_mask(sig, i, *j);
            let ctor_args: Vec<Rc<EValue>> = cargs[np..].to_vec();
            let mut result = method;
            for a in &ctor_args {
                result = eapply(sig, result, a.clone());
            }
            for (l, a) in ctor_args.iter().enumerate() {
                if mask[l] {
                    let fixed: Vec<Rc<EValue>> = sp[0..np + 1 + k].to_vec();
                    let arg_env: EEnv = cargs[0..np + l].to_vec();
                    let idx_spine = spine_args(&c.args[l]);
                    let mut ih = Rc::new(EValue::RecApp(i, fixed));
                    for it in &idx_spine[np..] {
                        ih = eapply(sig, ih, eindex(sig, &arg_env, it));
                    }
                    ih = eapply(sig, ih, a.clone());
                    result = eapply(sig, result, ih);
                }
            }
            result
        }
        EValue::Neutral(n) => {
            let fixed: Vec<Rc<EValue>> = sp[..sp.len() - 1].to_vec();
            Rc::new(EValue::Neutral(ENeutral::Rec(i, fixed, Rc::new(n.clone()))))
        }
        EValue::Box => {
            let c = &ind.constructors[0];
            let m = c.args.len();
            let mask = first_order_rec_mask(sig, i, 0);
            let mut result = sp[np + 1].clone();
            for _ in 0..m {
                result = eapply(sig, result, Rc::new(EValue::Box));
            }
            for &rec in &mask {
                if rec {
                    result = eapply(sig, result, Rc::new(EValue::Box));
                }
            }
            result
        }
        _ => unreachable!(),
    }
}

fn eproj1(p: Rc<EValue>) -> Rc<EValue> {
    match &*p {
        EValue::Box => Rc::new(EValue::Box),
        EValue::Pair(a, _) => a.clone(),
        EValue::Neutral(n) => Rc::new(EValue::Neutral(ENeutral::Fst(Rc::new(n.clone())))),
        _ => unreachable!(),
    }
}

fn eproj2(p: Rc<EValue>) -> Rc<EValue> {
    match &*p {
        EValue::Box => Rc::new(EValue::Box),
        EValue::Pair(_, b) => b.clone(),
        EValue::Neutral(n) => Rc::new(EValue::Neutral(ENeutral::Snd(Rc::new(n.clone())))),
        _ => unreachable!(),
    }
}

fn eeval(sig: &Rc<Sig>, env: &EEnv, term: &ETerm) -> Rc<EValue> {
    match term {
        ETerm::Box => Rc::new(EValue::Box),
        ETerm::Var(i) => env[env.len() - 1 - i].clone(),
        ETerm::Lam(b) => Rc::new(EValue::Lam(EClosure {
            env: env.clone(),
            body: (**b).clone(),
            sig: sig.clone(),
        })),
        ETerm::App(f, x) => eapply(sig, eeval(sig, env, f), eeval(sig, env, x)),
        ETerm::Pair(a, b) => Rc::new(EValue::Pair(eeval(sig, env, a), eeval(sig, env, b))),
        ETerm::Fst(p) => eproj1(eeval(sig, env, p)),
        ETerm::Snd(p) => eproj2(eeval(sig, env, p)),
        ETerm::Constr(i, j) => Rc::new(EValue::Constr(*i, *j, Vec::new())),
        ETerm::Rec(i) => Rc::new(EValue::RecApp(*i, Vec::new())),
    }
}

fn equote(level: usize, value: &Rc<EValue>) -> ETerm {
    match &**value {
        EValue::Box => ETerm::Box,
        EValue::Neutral(n) => equote_neutral(level, n),
        EValue::Lam(clo) => ETerm::Lam(Box::new(equote(level + 1, &clo.apply(evar(level))))),
        EValue::Pair(a, b) => ETerm::Pair(Box::new(equote(level, a)), Box::new(equote(level, b))),
        EValue::Constr(i, j, sp) => equote_spine(level, ETerm::Constr(*i, *j), sp),
        EValue::RecApp(i, sp) => equote_spine(level, ETerm::Rec(*i), sp),
    }
}

fn equote_spine(level: usize, head: ETerm, spine: &[Rc<EValue>]) -> ETerm {
    let mut out = head;
    for a in spine {
        out = ETerm::App(Box::new(out), Box::new(equote(level, a)));
    }
    out
}

fn equote_neutral(level: usize, neutral: &ENeutral) -> ETerm {
    match neutral {
        ENeutral::Var(l) => ETerm::Var(level - 1 - l),
        ENeutral::App(f, a) => ETerm::App(
            Box::new(equote_neutral(level, f)),
            Box::new(equote(level, a)),
        ),
        ENeutral::Fst(n) => ETerm::Fst(Box::new(equote_neutral(level, n))),
        ENeutral::Snd(n) => ETerm::Snd(Box::new(equote_neutral(level, n))),
        ENeutral::Rec(i, fixed, major) => {
            let head = equote_spine(level, ETerm::Rec(*i), fixed);
            ETerm::App(Box::new(head), Box::new(equote_neutral(level, major)))
        }
    }
}

pub fn enorm(sig: &Rc<Sig>, term: &ETerm) -> ETerm {
    equote(0, &eeval(sig, &Vec::new(), term))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn u(n: u32) -> Term {
        Term::Universe(n)
    }
    fn prop() -> Term {
        Term::Prop
    }
    fn pi(a: Term, b: Term) -> Term {
        Term::Pi(Box::new(a), Box::new(b))
    }
    fn lam(a: Term, t: Term) -> Term {
        Term::Lam(Box::new(a), Box::new(t))
    }
    fn app(f: Term, x: Term) -> Term {
        Term::App(Box::new(f), Box::new(x))
    }
    fn sigma(a: Term, b: Term) -> Term {
        Term::Sigma(Box::new(a), Box::new(b))
    }
    fn pair(s: Term, a: Term, b: Term) -> Term {
        Term::Pair(Box::new(s), Box::new(a), Box::new(b))
    }
    fn fst(p: Term) -> Term {
        Term::Fst(Box::new(p))
    }
    fn snd(p: Term) -> Term {
        Term::Snd(Box::new(p))
    }
    fn v(i: usize) -> Term {
        Term::Var(i)
    }
    fn empty() -> Rc<Sig> {
        Rc::new(Vec::new())
    }
    fn val(term: &Term) -> Rc<Value> {
        eval(&empty(), &Vec::new(), term)
    }
    fn norm(sig: &Rc<Sig>, term: &Term) -> Term {
        quote(0, &eval(sig, &Vec::new(), term))
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

    #[test]
    fn universe_typing() {
        let ctx = Context::new();
        assert_eq!(quote(0, &infer(&ctx, &u(0)).unwrap()), u(1));
    }

    #[test]
    fn prop_is_a_type() {
        let ctx = Context::new();
        assert_eq!(quote(0, &infer(&ctx, &prop()).unwrap()), u(0));
    }

    #[test]
    fn polymorphic_identity() {
        let ctx = Context::new();
        let id = lam(u(0), lam(v(0), v(0)));
        assert_eq!(
            quote(0, &infer(&ctx, &id).unwrap()),
            pi(u(0), pi(v(0), v(1)))
        );
    }

    #[test]
    fn application_reduces() {
        let ctx = Context::new();
        let term = app(lam(u(1), v(0)), u(0));
        assert_eq!(quote(0, &infer(&ctx, &term).unwrap()), u(1));
        assert_eq!(normalize(&term), u(0));
    }

    #[test]
    fn dependent_application() {
        let ctx = Context::new();
        let id = lam(u(1), lam(v(0), v(0)));
        let applied = app(id, u(0));
        assert_eq!(quote(0, &infer(&ctx, &applied).unwrap()), pi(u(0), u(0)));
    }

    #[test]
    fn ill_typed_is_rejected() {
        let ctx = Context::new();
        assert!(infer(&ctx, &app(u(0), u(0))).is_err());
        assert!(infer(&ctx, &v(0)).is_err());
    }

    #[test]
    fn sigma_formation() {
        let ctx = Context::new();
        assert_eq!(quote(0, &infer(&ctx, &sigma(u(1), v(0))).unwrap()), u(2));
    }

    #[test]
    fn dependent_pair_projects() {
        let ctx = Context::new();
        let s = sigma(u(1), v(0));
        let a = pi(u(0), u(0));
        let b = lam(u(0), v(0));
        let p = pair(s.clone(), a.clone(), b.clone());

        assert_eq!(quote(0, &infer(&ctx, &p).unwrap()), s);
        assert_eq!(quote(0, &infer(&ctx, &fst(p.clone())).unwrap()), u(1));
        assert_eq!(normalize(&fst(p.clone())), a);
        assert_eq!(quote(0, &infer(&ctx, &snd(p.clone())).unwrap()), a);
        assert_eq!(normalize(&snd(p)), b);
    }

    #[test]
    fn ill_typed_pair_is_rejected() {
        let ctx = Context::new();
        let bad = pair(sigma(u(1), v(0)), u(5), lam(u(0), v(0)));
        assert!(infer(&ctx, &bad).is_err());
    }

    #[test]
    fn proof_irrelevance_holds() {
        let ctx = Context::new();
        let term = lam(
            prop(),
            lam(
                pi(v(0), u(0)),
                lam(v(1), lam(v(2), lam(app(v(2), v(1)), v(0)))),
            ),
        );
        let expected = pi(
            prop(),
            pi(
                pi(v(0), u(0)),
                pi(v(1), pi(v(2), pi(app(v(2), v(1)), app(v(3), v(1))))),
            ),
        );
        assert!(check(&ctx, &term, &val(&expected)).is_ok());
    }

    #[test]
    fn relevance_fails_in_type() {
        let ctx = Context::new();
        let term = lam(
            u(0),
            lam(
                pi(v(0), u(0)),
                lam(v(1), lam(v(2), lam(app(v(2), v(1)), v(0)))),
            ),
        );
        let expected = pi(
            u(0),
            pi(
                pi(v(0), u(0)),
                pi(v(1), pi(v(2), pi(app(v(2), v(1)), app(v(3), v(1))))),
            ),
        );
        assert!(check(&ctx, &term, &val(&expected)).is_err());
    }

    #[test]
    fn prop_is_impredicative() {
        let ctx = Context::new();
        assert_eq!(quote(0, &infer(&ctx, &pi(prop(), v(0))).unwrap()), prop());
        assert_eq!(quote(0, &infer(&ctx, &pi(u(0), v(0))).unwrap()), u(1));
    }

    #[test]
    fn mutual_inductive_positivity_hole() {
        let sig = Rc::new(vec![
            Inductive {
                params: vec![],
                indices: vec![],
                sort: 0,
                constructors: vec![],
            },
            Inductive {
                params: vec![],
                indices: vec![],
                sort: 1,
                constructors: vec![Constructor {
                    args: vec![Term::Pi(Box::new(Term::Ind(2)), Box::new(Term::Ind(0)))],
                    index_values: vec![],
                }],
            },
            Inductive {
                params: vec![],
                indices: vec![],
                sort: 1,
                constructors: vec![Constructor {
                    args: vec![Term::Ind(1)],
                    index_values: vec![],
                }],
            },
        ]);
        assert!(
            check_signature(&sig).is_err(),
            "non-positive mutual signature must be rejected (ADR-0172)"
        );
    }

    #[test]
    fn audit_three_inductive_negative_cycle_rejected() {
        let sig = Rc::new(vec![
            Inductive {
                params: vec![],
                indices: vec![],
                sort: 0,
                constructors: vec![],
            },
            Inductive {
                params: vec![],
                indices: vec![],
                sort: 1,
                constructors: vec![Constructor {
                    args: vec![Term::Pi(Box::new(Term::Ind(2)), Box::new(Term::Ind(0)))],
                    index_values: vec![],
                }],
            },
            Inductive {
                params: vec![],
                indices: vec![],
                sort: 1,
                constructors: vec![Constructor {
                    args: vec![Term::Ind(3)],
                    index_values: vec![],
                }],
            },
            Inductive {
                params: vec![],
                indices: vec![],
                sort: 1,
                constructors: vec![Constructor {
                    args: vec![Term::Ind(1)],
                    index_values: vec![],
                }],
            },
        ]);
        assert!(
            check_signature(&sig).is_err(),
            "length-3 negative mutual cycle must be rejected (ADR-0172)"
        );
    }

    #[test]
    fn audit_positive_mutual_cycle_accepted() {
        let sig = Rc::new(vec![
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
                        args: vec![Term::Ind(1)],
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
                        args: vec![Term::Ind(0)],
                        index_values: vec![],
                    },
                ],
            },
        ]);
        assert!(
            check_signature(&sig).is_ok(),
            "positive mutual cycle must stay accepted (no over-rejection)"
        );
    }

    #[test]
    fn audit_sigma_over_type_is_not_prop() {
        let ctx = Context::new();
        let ty = sigma(u(0), v(0));
        let s = infer(&ctx, &ty).expect("Σ(A:Type0) A is well-formed");
        assert!(
            matches!(&*s, Value::Universe(_)),
            "Σ over a Type component must live in a Universe, not Prop"
        );
    }

    #[test]
    fn bool_signature_is_valid() {
        assert!(check_signature(&bool_sig()).is_ok());
        assert!(check_signature(&nat_sig()).is_ok());
    }

    #[test]
    fn bool_formation_and_intro() {
        let ctx = Context::with_sig(bool_sig());
        assert_eq!(quote(0, &infer(&ctx, &Term::Ind(0)).unwrap()), u(0));
        assert_eq!(
            quote(0, &infer(&ctx, &Term::Constr(0, 0)).unwrap()),
            Term::Ind(0)
        );
        assert_eq!(
            quote(0, &infer(&ctx, &Term::Constr(0, 1)).unwrap()),
            Term::Ind(0)
        );
    }

    #[test]
    fn bool_recursor_type() {
        let ctx = Context::with_sig(bool_sig());
        let expected = pi(
            pi(Term::Ind(0), u(0)),
            pi(
                app(v(0), Term::Constr(0, 0)),
                pi(
                    app(v(1), Term::Constr(0, 1)),
                    pi(Term::Ind(0), app(v(3), v(0))),
                ),
            ),
        );
        assert_eq!(quote(0, &infer(&ctx, &Term::Rec(0, 1)).unwrap()), expected);
    }

    #[test]
    fn bool_recursor_computes() {
        let sig = bool_sig();
        let not = lam(
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
        let ctx = Context::with_sig(sig.clone());
        assert_eq!(
            quote(0, &infer(&ctx, &not).unwrap()),
            pi(Term::Ind(0), Term::Ind(0))
        );
        assert_eq!(
            norm(&sig, &app(not.clone(), Term::Constr(0, 0))),
            Term::Constr(0, 1)
        );
        assert_eq!(
            norm(&sig, &app(not, Term::Constr(0, 1))),
            Term::Constr(0, 0)
        );
    }

    #[test]
    fn nat_recursor_computes_addition() {
        let sig = nat_sig();
        let zero = Term::Constr(0, 0);
        let succ = |n: Term| app(Term::Constr(0, 1), n);
        let plus = lam(
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
        let ctx = Context::with_sig(sig.clone());
        assert_eq!(
            quote(0, &infer(&ctx, &plus).unwrap()),
            pi(Term::Ind(0), pi(Term::Ind(0), Term::Ind(0)))
        );
        let two = succ(succ(zero.clone()));
        let one = succ(zero.clone());
        let three = succ(succ(succ(zero)));
        assert_eq!(norm(&sig, &app(app(plus, two), one)), three);
    }

    fn nat_list_sig() -> Rc<Sig> {
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
                params: vec![u(0)],
                indices: vec![],
                sort: 1,
                constructors: vec![
                    Constructor {
                        args: vec![],
                        index_values: vec![],
                    },
                    Constructor {
                        args: vec![v(0), app(Term::Ind(1), v(1))],
                        index_values: vec![],
                    },
                ],
            },
        ])
    }

    #[test]
    fn parametric_list_signature_is_valid() {
        assert!(check_signature(&nat_list_sig()).is_ok());
    }

    #[test]
    fn list_recursor_computes_length() {
        let sig = nat_list_sig();
        let zero = Term::Constr(0, 0);
        let succ = |n: Term| app(Term::Constr(0, 1), n);
        let nat = Term::Ind(0);
        let nil = |a: Term| app(Term::Constr(1, 0), a);
        let cons = |a: Term, x: Term, xs: Term| app(app(app(Term::Constr(1, 1), a), x), xs);

        let motive = lam(app(Term::Ind(1), v(1)), Term::Ind(0));
        let m_cons = lam(
            v(1),
            lam(app(Term::Ind(1), v(2)), lam(Term::Ind(0), succ(v(0)))),
        );
        let length = lam(
            u(0),
            lam(
                app(Term::Ind(1), v(0)),
                app(
                    app(
                        app(app(app(Term::Rec(1, 1), v(1)), motive), zero.clone()),
                        m_cons,
                    ),
                    v(0),
                ),
            ),
        );

        let ctx = Context::with_sig(sig.clone());
        assert_eq!(
            quote(0, &infer(&ctx, &length).unwrap()),
            pi(u(0), pi(app(Term::Ind(1), v(0)), Term::Ind(0)))
        );

        let empty_list = nil(nat.clone());
        let one_list = cons(nat.clone(), zero.clone(), nil(nat.clone()));
        assert_eq!(
            norm(&sig, &app(app(length.clone(), nat.clone()), empty_list)),
            zero
        );
        assert_eq!(norm(&sig, &app(app(length, nat), one_list)), succ(zero));
    }

    #[test]
    fn non_positive_inductive_is_rejected() {
        let bad = Rc::new(vec![Inductive {
            params: vec![],
            indices: vec![],
            sort: 1,
            constructors: vec![Constructor {
                args: vec![pi(Term::Ind(0), Term::Ind(0))],
                index_values: vec![],
            }],
        }]);
        assert!(check_signature(&bad).is_err());
    }

    fn bool_id_sig() -> Rc<Sig> {
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
                        args: vec![],
                        index_values: vec![],
                    },
                ],
            },
            Inductive {
                params: vec![u(0), v(0)],
                indices: vec![v(1)],
                sort: 0,
                constructors: vec![Constructor {
                    args: vec![],
                    index_values: vec![v(0)],
                }],
            },
        ])
    }

    #[test]
    fn prop_id_signature_is_valid() {
        assert!(check_signature(&bool_id_sig()).is_ok());
    }

    #[test]
    fn id_is_proof_irrelevant() {
        let sig = bool_id_sig();
        let ctx = Context::with_sig(sig.clone());
        let id_true = app(
            app(app(Term::Ind(1), Term::Ind(0)), Term::Constr(0, 1)),
            Term::Constr(0, 1),
        );
        assert_eq!(
            sort_level_of_type(&ctx, &eval(&sig, &Vec::new(), &id_true)),
            0
        );
    }

    #[test]
    fn large_elimination_from_subsingleton_prop_computes() {
        let sig = bool_id_sig();
        let bool_ty = Term::Ind(0);
        let tru = Term::Constr(0, 1);
        let id = |a: Term, x: Term, y: Term| app(app(app(Term::Ind(1), a), x), y);
        let refl = |a: Term, x: Term| app(app(Term::Constr(1, 0), a), x);

        let motive = lam(
            bool_ty.clone(),
            lam(id(bool_ty.clone(), tru.clone(), v(0)), bool_ty.clone()),
        );
        let method = tru.clone();
        let j = app(
            app(
                app(
                    app(
                        app(app(Term::Rec(1, 1), bool_ty.clone()), tru.clone()),
                        motive,
                    ),
                    method,
                ),
                tru.clone(),
            ),
            refl(bool_ty.clone(), tru.clone()),
        );

        let ctx = Context::with_sig(sig.clone());
        assert!(infer(&ctx, &j).is_ok());
        assert_eq!(norm(&sig, &j), tru);
    }

    #[test]
    fn large_elimination_from_nonsubsingleton_prop_is_rejected() {
        let sig = Rc::new(vec![Inductive {
            params: vec![],
            indices: vec![],
            sort: 0,
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
        }]);
        assert!(check_signature(&sig).is_ok());
        let ctx = Context::with_sig(sig);
        assert!(infer(&ctx, &Term::Rec(0, 0)).is_ok());
        assert!(infer(&ctx, &Term::Rec(0, 1)).is_err());
    }

    fn vec_sig() -> Rc<Sig> {
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
                params: vec![u(0)],
                indices: vec![Term::Ind(0)],
                sort: 1,
                constructors: vec![
                    Constructor {
                        args: vec![],
                        index_values: vec![Term::Constr(0, 0)],
                    },
                    Constructor {
                        args: vec![Term::Ind(0), v(1), app(app(Term::Ind(1), v(2)), v(1))],
                        index_values: vec![app(Term::Constr(0, 1), v(2))],
                    },
                ],
            },
        ])
    }

    #[test]
    fn vec_signature_is_valid() {
        assert!(check_signature(&vec_sig()).is_ok());
    }

    #[test]
    fn vec_indexed_recursion_computes() {
        let sig = vec_sig();
        let nat = Term::Ind(0);
        let zero = Term::Constr(0, 0);
        let succ = |n: Term| app(Term::Constr(0, 1), n);
        let nil = |a: Term| app(Term::Constr(1, 0), a);
        let cons = |a: Term, n: Term, x: Term, xs: Term| {
            app(app(app(app(Term::Constr(1, 1), a), n), x), xs)
        };

        let motive = lam(
            nat.clone(),
            lam(app(app(Term::Ind(1), nat.clone()), v(0)), nat.clone()),
        );
        let m_nil = zero.clone();
        let m_cons = lam(
            nat.clone(),
            lam(
                nat.clone(),
                lam(
                    app(app(Term::Ind(1), nat.clone()), v(1)),
                    lam(nat.clone(), succ(v(0))),
                ),
            ),
        );

        let count = |n: Term, xs: Term| {
            app(
                app(
                    app(
                        app(
                            app(app(Term::Rec(1, 1), nat.clone()), motive.clone()),
                            m_nil.clone(),
                        ),
                        m_cons.clone(),
                    ),
                    n,
                ),
                xs,
            )
        };

        let ctx = Context::with_sig(sig.clone());

        let v0 = nil(nat.clone());
        let v1 = cons(nat.clone(), zero.clone(), zero.clone(), nil(nat.clone()));
        let v2 = cons(nat.clone(), succ(zero.clone()), zero.clone(), v1.clone());

        assert!(infer(&ctx, &count(zero.clone(), v0.clone())).is_ok());
        assert_eq!(norm(&sig, &count(zero.clone(), v0)), zero.clone());
        assert_eq!(
            norm(&sig, &count(succ(zero.clone()), v1)),
            succ(zero.clone())
        );
        assert_eq!(
            norm(&sig, &count(succ(succ(zero.clone())), v2)),
            succ(succ(zero.clone()))
        );
    }

    #[test]
    fn indexed_higher_order_recursion_is_rejected() {
        let bad = Rc::new(vec![
            Inductive {
                params: vec![],
                indices: vec![],
                sort: 1,
                constructors: vec![Constructor {
                    args: vec![],
                    index_values: vec![],
                }],
            },
            Inductive {
                params: vec![],
                indices: vec![Term::Ind(0)],
                sort: 1,
                constructors: vec![Constructor {
                    args: vec![pi(Term::Ind(0), app(Term::Ind(1), Term::Constr(0, 0)))],
                    index_values: vec![Term::Constr(0, 0)],
                }],
            },
        ]);
        assert!(check_signature(&bad).is_err());
    }

    fn funext_type() -> Term {
        let id = |a: Term, x: Term, y: Term| app(app(app(Term::Ind(1), a), x), y);
        pi(
            u(0),
            pi(
                pi(v(0), u(0)),
                pi(
                    pi(v(1), app(v(1), v(0))),
                    pi(
                        pi(v(2), app(v(2), v(0))),
                        pi(
                            pi(v(3), id(app(v(3), v(0)), app(v(2), v(0)), app(v(1), v(0)))),
                            id(pi(v(4), app(v(4), v(0))), v(2), v(1)),
                        ),
                    ),
                ),
            ),
        )
    }

    fn propext_type() -> Term {
        pi(
            prop(),
            pi(
                prop(),
                pi(
                    pi(v(1), v(1)),
                    pi(
                        pi(v(1), v(3)),
                        app(app(app(Term::Ind(1), prop()), v(3)), v(2)),
                    ),
                ),
            ),
        )
    }

    #[test]
    fn axiom_must_be_a_proposition() {
        let sig = bool_id_sig();
        let prop_axiom = Rc::new(vec![app(
            app(app(Term::Ind(1), Term::Ind(0)), Term::Constr(0, 1)),
            Term::Constr(0, 1),
        )]);
        assert!(check_axioms(&sig, &prop_axiom).is_ok());
        let type_axiom = Rc::new(vec![Term::Ind(0)]);
        assert!(check_axioms(&sig, &type_axiom).is_err());
    }

    #[test]
    fn funext_and_propext_are_propositions() {
        let sig = bool_id_sig();
        let axioms = Rc::new(vec![funext_type(), propext_type()]);
        assert!(check_axioms(&sig, &axioms).is_ok());
        let ctx = Context::with_sig_and_axioms(sig.clone(), axioms);
        assert_eq!(
            quote(0, &infer(&ctx, &Term::Axiom(0)).unwrap()),
            funext_type()
        );
        assert_eq!(
            quote(0, &infer(&ctx, &Term::Axiom(1)).unwrap()),
            propext_type()
        );
    }

    #[test]
    fn funext_application_is_an_opaque_proof() {
        let sig = bool_id_sig();
        let axioms = Rc::new(vec![funext_type()]);
        let ctx = Context::with_sig_and_axioms(sig.clone(), axioms);

        let booly = Term::Ind(0);
        let b = lam(booly.clone(), booly.clone());
        let idf = lam(booly.clone(), v(0));
        let h = lam(
            booly.clone(),
            app(app(Term::Constr(1, 0), booly.clone()), v(0)),
        );
        let proof = app(
            app(
                app(
                    app(app(Term::Axiom(0), booly.clone()), b.clone()),
                    idf.clone(),
                ),
                idf.clone(),
            ),
            h.clone(),
        );

        let expected_ty = app(
            app(
                app(Term::Ind(1), pi(booly.clone(), booly.clone())),
                idf.clone(),
            ),
            idf.clone(),
        );
        assert_eq!(quote(0, &infer(&ctx, &proof).unwrap()), expected_ty);

        let expected_nf = app(
            app(
                app(app(app(Term::Axiom(0), booly.clone()), b), idf.clone()),
                idf.clone(),
            ),
            h,
        );
        assert_eq!(norm(&sig, &proof), expected_nf);

        let refl_proof = app(
            app(Term::Constr(1, 0), pi(booly.clone(), booly.clone())),
            idf,
        );
        assert!(check(&ctx, &refl_proof, &infer(&ctx, &proof).unwrap()).is_ok());
    }

    #[test]
    fn erase_boxes_types_and_type_schemes() {
        let ctx = Context::new();
        assert_eq!(erase(&ctx, &u(0)).unwrap(), ETerm::Box);
        assert_eq!(erase(&ctx, &prop()).unwrap(), ETerm::Box);
        assert_eq!(erase(&ctx, &pi(u(0), v(0))).unwrap(), ETerm::Box);

        let sig = nat_sig();
        let nctx = Context::with_sig(sig);
        assert_eq!(erase(&nctx, &Term::Ind(0)).unwrap(), ETerm::Box);
        let type_scheme = lam(Term::Ind(0), Term::Ind(0));
        assert_eq!(erase(&nctx, &type_scheme).unwrap(), ETerm::Box);
    }

    #[test]
    fn erase_keeps_informative_skeleton() {
        let ctx = Context::new();
        let poly_id = lam(u(0), lam(v(0), v(0)));
        assert_eq!(
            erase(&ctx, &poly_id).unwrap(),
            ETerm::Lam(Box::new(ETerm::Lam(Box::new(ETerm::Var(0)))))
        );

        let sig = nat_sig();
        let nctx = Context::with_sig(sig);
        let two = app(
            Term::Constr(0, 1),
            app(Term::Constr(0, 1), Term::Constr(0, 0)),
        );
        assert_eq!(
            erase(&nctx, &two).unwrap(),
            ETerm::App(
                Box::new(ETerm::Constr(0, 1)),
                Box::new(ETerm::App(
                    Box::new(ETerm::Constr(0, 1)),
                    Box::new(ETerm::Constr(0, 0))
                ))
            )
        );
    }

    #[test]
    fn erase_boxes_constructor_type_arguments() {
        let sig = vec_sig();
        let ctx = Context::with_sig(sig);
        let nat = Term::Ind(0);
        let zero = Term::Constr(0, 0);
        let nil = app(Term::Constr(1, 0), nat.clone());
        assert_eq!(
            erase(&ctx, &nil).unwrap(),
            ETerm::App(Box::new(ETerm::Constr(1, 0)), Box::new(ETerm::Box))
        );
        let one = app(
            app(
                app(app(Term::Constr(1, 1), nat.clone()), zero.clone()),
                zero.clone(),
            ),
            nil.clone(),
        );
        assert_eq!(
            erase(&ctx, &one).unwrap(),
            ETerm::App(
                Box::new(ETerm::App(
                    Box::new(ETerm::App(
                        Box::new(ETerm::App(
                            Box::new(ETerm::Constr(1, 1)),
                            Box::new(ETerm::Box)
                        )),
                        Box::new(ETerm::Constr(0, 0))
                    )),
                    Box::new(ETerm::Constr(0, 0))
                )),
                Box::new(ETerm::App(
                    Box::new(ETerm::Constr(1, 0)),
                    Box::new(ETerm::Box)
                ))
            )
        );
    }

    #[test]
    fn erase_collapses_prop_proofs_to_box() {
        let sig = bool_id_sig();
        let axioms = Rc::new(vec![funext_type()]);
        let ctx = Context::with_sig_and_axioms(sig.clone(), axioms);
        let booly = Term::Ind(0);
        let b = lam(booly.clone(), booly.clone());
        let idf = lam(booly.clone(), v(0));
        let h = lam(
            booly.clone(),
            app(app(Term::Constr(1, 0), booly.clone()), v(0)),
        );
        let proof = app(
            app(
                app(app(app(Term::Axiom(0), booly.clone()), b), idf.clone()),
                idf.clone(),
            ),
            h,
        );
        assert_eq!(erase(&ctx, &proof).unwrap(), ETerm::Box);

        let refl = app(app(Term::Constr(1, 0), booly.clone()), Term::Constr(0, 1));
        assert_eq!(erase(&ctx, &refl).unwrap(), ETerm::Box);
    }

    #[test]
    fn erasure_preserves_first_order_nat() {
        let sig = nat_sig();
        let ctx = Context::with_sig(sig.clone());
        let zero = Term::Constr(0, 0);
        let succ = |n: Term| app(Term::Constr(0, 1), n);
        let plus = lam(
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
        let prog = app(app(plus, succ(succ(zero.clone()))), succ(zero.clone()));
        let lhs = enorm(&sig, &erase(&ctx, &prog).unwrap());
        let rhs = erase(&ctx, &norm(&sig, &prog)).unwrap();
        assert_eq!(lhs, rhs);
        assert_eq!(lhs, erase(&ctx, &succ(succ(succ(zero)))).unwrap());
    }

    #[test]
    fn erasure_preserves_first_order_list() {
        let sig = nat_list_sig();
        let ctx = Context::with_sig(sig.clone());
        let zero = Term::Constr(0, 0);
        let succ = |n: Term| app(Term::Constr(0, 1), n);
        let nat = Term::Ind(0);
        let nil = |a: Term| app(Term::Constr(1, 0), a);
        let cons = |a: Term, x: Term, xs: Term| app(app(app(Term::Constr(1, 1), a), x), xs);
        let motive = lam(app(Term::Ind(1), v(1)), Term::Ind(0));
        let m_cons = lam(
            v(1),
            lam(app(Term::Ind(1), v(2)), lam(Term::Ind(0), succ(v(0)))),
        );
        let length = lam(
            u(0),
            lam(
                app(Term::Ind(1), v(0)),
                app(
                    app(
                        app(app(app(Term::Rec(1, 1), v(1)), motive), zero.clone()),
                        m_cons,
                    ),
                    v(0),
                ),
            ),
        );
        let one_list = cons(nat.clone(), zero.clone(), nil(nat.clone()));
        let prog = app(app(length, nat.clone()), one_list);
        let lhs = enorm(&sig, &erase(&ctx, &prog).unwrap());
        let rhs = erase(&ctx, &norm(&sig, &prog)).unwrap();
        assert_eq!(lhs, rhs);
        assert_eq!(lhs, erase(&ctx, &succ(zero)).unwrap());
    }

    #[test]
    fn erasure_preserves_first_order_vec() {
        let sig = vec_sig();
        let ctx = Context::with_sig(sig.clone());
        let nat = Term::Ind(0);
        let zero = Term::Constr(0, 0);
        let succ = |n: Term| app(Term::Constr(0, 1), n);
        let nil = |a: Term| app(Term::Constr(1, 0), a);
        let cons = |a: Term, n: Term, x: Term, xs: Term| {
            app(app(app(app(Term::Constr(1, 1), a), n), x), xs)
        };
        let motive = lam(
            nat.clone(),
            lam(app(app(Term::Ind(1), nat.clone()), v(0)), nat.clone()),
        );
        let m_cons = lam(
            nat.clone(),
            lam(
                nat.clone(),
                lam(
                    app(app(Term::Ind(1), nat.clone()), v(1)),
                    lam(nat.clone(), succ(v(0))),
                ),
            ),
        );
        let count = |n: Term, xs: Term| {
            app(
                app(
                    app(
                        app(
                            app(app(Term::Rec(1, 1), nat.clone()), motive.clone()),
                            zero.clone(),
                        ),
                        m_cons.clone(),
                    ),
                    n,
                ),
                xs,
            )
        };
        let v1 = cons(nat.clone(), zero.clone(), zero.clone(), nil(nat.clone()));
        let v2 = cons(nat.clone(), succ(zero.clone()), zero.clone(), v1);
        let prog = count(succ(succ(zero.clone())), v2);
        let lhs = enorm(&sig, &erase(&ctx, &prog).unwrap());
        let rhs = erase(&ctx, &norm(&sig, &prog)).unwrap();
        assert_eq!(lhs, rhs);
        assert_eq!(lhs, erase(&ctx, &succ(succ(zero))).unwrap());
    }

    #[test]
    fn erasure_computes_through_boxed_proof() {
        let sig = bool_id_sig();
        let ctx = Context::with_sig(sig.clone());
        let bool_ty = Term::Ind(0);
        let tru = Term::Constr(0, 1);
        let id = |a: Term, x: Term, y: Term| app(app(app(Term::Ind(1), a), x), y);
        let refl = |a: Term, x: Term| app(app(Term::Constr(1, 0), a), x);
        let motive = lam(
            bool_ty.clone(),
            lam(id(bool_ty.clone(), tru.clone(), v(0)), bool_ty.clone()),
        );
        let prog = app(
            app(
                app(
                    app(
                        app(app(Term::Rec(1, 1), bool_ty.clone()), tru.clone()),
                        motive,
                    ),
                    tru.clone(),
                ),
                tru.clone(),
            ),
            refl(bool_ty.clone(), tru.clone()),
        );
        let erased = erase(&ctx, &prog).unwrap();
        assert_ne!(erased, ETerm::Box);
        let lhs = enorm(&sig, &erased);
        let rhs = erase(&ctx, &norm(&sig, &prog)).unwrap();
        assert_eq!(lhs, rhs);
        assert_eq!(lhs, ETerm::Constr(0, 1));
    }
}
