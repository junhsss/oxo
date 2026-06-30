use oxo_kernel::{check_signature, Constructor, Inductive, Term};
use std::rc::Rc;

fn empty_ind() -> Inductive {
    Inductive {
        params: vec![],
        indices: vec![],
        sort: 1,
        constructors: vec![],
    }
}

fn bad_with_step_arg(step_arg: Term) -> Rc<Vec<Inductive>> {
    Rc::new(vec![
        empty_ind(),
        Inductive {
            params: vec![Term::Universe(0)],
            indices: vec![],
            sort: 1,
            constructors: vec![
                Constructor {
                    args: vec![],
                    index_values: vec![],
                },
                Constructor {
                    args: vec![step_arg],
                    index_values: vec![],
                },
            ],
        },
    ])
}

#[test]
fn a_nonuniform_param_recursive_arg_is_rejected() {
    let sig = bad_with_step_arg(Term::App(Box::new(Term::Ind(1)), Box::new(Term::Ind(0))));
    let r = check_signature(&sig);
    println!("[A] step arg = Bad Empty (NON-UNIFORM param) => {:?}", r);
    assert!(
        r.is_err(),
        "non-uniform recursive parameter must be rejected (ADR-0179)"
    );
}

#[test]
fn b_uniform_param_recursive_arg_is_accepted() {
    let sig = bad_with_step_arg(Term::App(Box::new(Term::Ind(1)), Box::new(Term::Var(0))));
    let r = check_signature(&sig);
    println!("[B] step arg = Bad A   (uniform param)     => {:?}", r);
    assert!(r.is_ok(), "uniform recursive parameter must stay accepted");
}

#[test]
fn c_self_in_param_position_is_rejected() {
    let inner = Term::App(Box::new(Term::Ind(1)), Box::new(Term::Var(0)));
    let sig = bad_with_step_arg(Term::App(Box::new(Term::Ind(1)), Box::new(inner)));
    let r = check_signature(&sig);
    println!("[C] step arg = Bad (Bad A) (self in param)  => {:?}", r);
    assert!(
        r.is_err(),
        "self in parameter position must be rejected (positivity)"
    );
}

#[test]
fn d_negative_occurrence_is_rejected() {
    let dom = Term::App(Box::new(Term::Ind(1)), Box::new(Term::Var(0)));
    let sig = bad_with_step_arg(Term::Pi(Box::new(dom), Box::new(Term::Ind(0))));
    let r = check_signature(&sig);
    println!("[D] step arg = (Bad A -> Empty) (negative)  => {:?}", r);
    assert!(
        r.is_err(),
        "negative occurrence must be rejected (positivity)"
    );
}
