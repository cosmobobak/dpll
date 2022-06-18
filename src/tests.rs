#[cfg(test)]
mod t {

use crate::dpll::{Clause, Formula, Literal, MLiteral, Satisfiability, SolveState, Trail};

fn get_standard_trail() -> Trail {
    let elements = vec![
        (1, false),
        (-2, true),
        (6, false),
        (5, true),
        (-3, false),
        (4, false),
        (-7, true),
    ]
    .into_iter()
    .map(|(var, marked)| (Literal::new(var), marked))
    .map(|(literal, marked)| MLiteral::new(literal, marked))
    .collect();
    Trail::new(elements)
}

#[test]
fn trail_decisions() {
    let trail = get_standard_trail();

    assert_eq!(
        trail.decisions().copied().collect::<Vec<_>>(),
        vec![Literal::new(-2), Literal::new(5), Literal::new(-7),]
    );
}

#[test]
fn trail_last_decision() {
    let trail = get_standard_trail();
    assert_eq!(trail.last_decision(), Some(&Literal::new(-7)));
}

#[test]
fn trail_decisions_to() {
    let trail = get_standard_trail();
    assert_eq!(
        trail
            .decisions_to(Literal::new(4))
            .copied()
            .collect::<Vec<_>>(),
        vec![Literal::new(-2), Literal::new(5),]
    );

    assert_eq!(
        trail
            .decisions_to(Literal::new(-7))
            .copied()
            .collect::<Vec<_>>(),
        vec![Literal::new(-2), Literal::new(5), Literal::new(-7),]
    );
}

#[test]
fn trail_level() {
    let trail = get_standard_trail();
    assert_eq!(trail.level(Literal::new(1)), 0);

    assert_eq!(trail.level(Literal::new(4)), 2);

    assert_eq!(trail.level(Literal::new(-7)), 3);
}

#[test]
fn trail_current_level() {
    let trail = get_standard_trail();
    assert_eq!(trail.current_level(), 3);
}

#[test]
fn trail_prefix_to_level() {
    let trail = get_standard_trail();
    assert_eq!(
        trail.prefix_to_level(1).copied().collect::<Vec<_>>(),
        vec![
            MLiteral::new(Literal::new(1), false),
            MLiteral::new(Literal::new(-2), true),
            MLiteral::new(Literal::new(6), false),
        ]
    );
}

#[test]
fn trail_prefix_before_last_decisions() {
    let trail = get_standard_trail();
    assert_eq!(
        trail
            .prefix_before_last_decision()
            .copied()
            .collect::<Vec<_>>(),
        vec![
            MLiteral::new(Literal::new(1), false),
            MLiteral::new(Literal::new(-2), true),
            MLiteral::new(Literal::new(6), false),
            MLiteral::new(Literal::new(5), true),
            MLiteral::new(Literal::new(-3), false),
            MLiteral::new(Literal::new(4), false),
        ]
    );
}

fn get_standard_clause() -> Clause {
    Clause::new(vec![Literal::new(4), Literal::new(6), Literal::new(-3)])
}

#[test]
fn clause_max_level() {
    let c = get_standard_clause();
    let trail = get_standard_trail();
    assert_eq!(c.max_level(&trail), Some(2));
}

#[test]
fn clause_last_asserted_literal() {
    let c = get_standard_clause();
    let trail = get_standard_trail();
    assert_eq!(c.last_asserted_literal(&trail), Some(Literal::new(4)));
}

#[test]
fn solve() {
    let formula = Formula::new(
        vec![
            vec![-1, 2],
            vec![-3, 4],
            vec![-1, -3, 5],
            vec![-2, -4, -5],
            vec![-2, 3, 5, -6],
            vec![-1, 3, -5, -6],
            vec![1, -6],
            vec![1, 7],
        ]
        .iter()
        .map(|vec| vec.iter().map(|&lit| Literal::new(lit)).collect::<Vec<_>>())
        .map(|clause| Clause::new(clause.to_vec()))
        .collect(),
    );

    let mut solver_state = SolveState::new(formula.clone());

    assert_eq!(solver_state.solve(), Satisfiability::Satisfiable);

    let solution_model = solver_state.get_model().unwrap();

    assert!(solution_model.is_true_formula(&formula));
}
}