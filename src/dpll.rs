use std::{collections::HashSet, fmt::Display, fs::File, io::Read, num::ParseIntError, ops::Neg};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Literal {
    var: i32,
}

impl Neg for Literal {
    type Output = Literal;

    fn neg(self) -> Literal {
        Literal { var: -self.var }
    }
}

const VAR_NAMES: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZ";

impl Literal {

    pub fn new(var: i32) -> Literal {
        Literal { var }
    }

    pub fn abs(self) -> Literal {
        Literal { var: self.var.abs() }
    }

    fn from_str(s: &str) -> Result<Literal, ParseIntError> {
        let var = s.parse()?;
        Ok(Literal { var })
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let var = self.var;
        if var < 0 {
            write!(f, "~{}", VAR_NAMES[(-var) as usize - 1] as char)
        } else {
            write!(f, "{}", VAR_NAMES[var as usize - 1] as char)
        }
    }
}

impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Literal) -> Option<std::cmp::Ordering> {
        self.var.abs().partial_cmp(&other.var.abs())
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Literal) -> std::cmp::Ordering {
        self.var.abs().cmp(&other.var.abs())
    }

    fn max(self, other: Self) -> Self
    where
        Self: Sized,
    {
        std::cmp::max_by(self, other, Ord::cmp)
    }

    fn min(self, other: Self) -> Self
    where
        Self: Sized,
    {
        std::cmp::min_by(self, other, Ord::cmp)
    }

    fn clamp(self, min: Self, max: Self) -> Self
    where
        Self: Sized,
    {
        assert!(min <= max);
        if self < min {
            min
        } else if self > max {
            max
        } else {
            self
        }
    }
}

#[derive(Debug, Clone)]
pub struct Clause {
    literals: Vec<Literal> 
}

impl Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.literals.is_empty() {
            write!(f, "Empty Formula.")?;
        } else {
            write!(f, "({} ", self.literals[0])?;
            let mut idx = 1;
            for clause in self.literals.iter().skip(1) {
                idx += 1;
                // stop one before the last
                if idx < self.literals.len() {
                    write!(f, "| {} ", clause)?;
                }
            }
            write!(f, "| {})", self.literals[self.literals.len()-1])?;
        }
        Ok(())
    }
}

impl Clause {
    pub fn new(literals: Vec<Literal>) -> Clause {
        Clause { literals }
    }

    pub fn contains(&self, lit: Literal) -> bool {
        self.literals.contains(&lit)
    }

    pub fn vars(&self) -> HashSet<Literal> {
        self.literals.iter().map(|l| l.abs()).collect()
    }
    
    pub fn last_asserted_literal(&self, trail: &Trail) -> Option<Literal> {
        self.literals.iter()
            .filter(|l| trail.contains(l))
            .copied()
            .max_by(|l1, l2| trail.index_of(*l1).cmp(&trail.index_of(*l2)))
    }

    pub fn max_level(&self, trail: &Trail) -> Option<usize> {
        self.last_asserted_literal(trail).map(|l| trail.level(l))
    }
}

#[derive(Debug, Clone)]
pub struct Formula {
    clauses: Vec<Clause>,
}

impl Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.clauses.is_empty() {
            write!(f, "Empty Formula.")?;
        } else {
            write!(f, "{} ", self.clauses[0])?;
            let mut idx = 1;
            for clause in self.clauses.iter().skip(1) {
                idx += 1;
                // stop one before the last
                if idx < self.clauses.len() {
                    write!(f, "& {} ", clause)?;
                }
            }
            write!(f, "& {}", self.clauses[self.clauses.len()-1])?;
        }
        Ok(())
    }
}

impl Formula {
    pub fn new(clauses: Vec<Clause>) -> Formula {
        Formula { clauses }
    }

    pub fn contains(&self, lit: Literal) -> bool {
        self.clauses.iter().any(|c| c.literals.contains(&lit))
    }

    pub fn vars(&self) -> HashSet<Literal> {
        self.clauses.iter().flat_map(|c| c.literals.iter()).map(|l| l.abs()).collect()
    }
}

#[derive(Debug)]
pub struct Valuation {
    literals: Vec<Literal>,
}

impl Display for Valuation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        let mut litvec = self.literals.iter().copied().collect::<Vec<_>>();
        litvec.sort_unstable();
        for lit in litvec {
            if !first {
                write!(f, " ")?;
            }
            write!(f, "{}", lit)?;
            first = false;
        }
        Ok(())
    }
}

impl Valuation {
    pub fn new(literals: Vec<Literal>) -> Valuation {
        Valuation { literals }
    }

    pub fn iter(&self) -> impl Iterator<Item = &Literal> {
        self.literals.iter()
    }

    pub fn is_true_literal(&self, lit: Literal) -> bool {
        self.literals.contains(&lit)
    }

    pub fn is_true_clause(&self, clause: &Clause) -> bool {
        clause.literals.iter().any(|&l| self.is_true_literal(l))
    }

    pub fn is_true_formula(&self, formula: &Formula) -> bool {
        formula.clauses.iter().all(|c| self.is_true_clause(c))
    }

    pub fn is_false_literal(&self, lit: Literal) -> bool {
        self.literals.contains(&-lit)
    }

    pub fn is_false_clause(&self, clause: &Clause) -> bool {
        clause.literals.iter().all(|&l| self.is_false_literal(l))
    }

    pub fn is_false_formula(&self, formula: &Formula) -> bool {
        formula.clauses.iter().any(|c| self.is_false_clause(c))
    }

    pub fn is_inconsistent(&self) -> bool {
        self.literals.iter().any(|&l| self.literals.contains(&-l))
    }

    pub fn is_consistent(&self) -> bool {
        !self.is_inconsistent()
    }

    // A model of a formula F is a consistent valuation under which
    // F is true. A formula F is satisfiable, denoted (sat F) iff it has a model i.e.,
    // ∃v. (v.is_consistent()) && v.is_true_formula(F)
}

pub fn is_unit(c: &Clause, l: Literal, v: &Valuation) -> bool {
    // A clause c is unit in a valuation v with a unit literal l, denoted
    // (isUnit c l v) iff l ∈ c, v |/= l, v |/=¬l and v |=¬(c \ l) (i.e., ∀l′. l′ ∈ c ∧ l′ 6= l ⇒ v |=¬l′).
    c.contains(l) &&
    !v.is_true_literal(l) &&
    !v.is_false_literal(l) &&
    c.literals.iter().all(|&l_| l_ == l || v.is_false_literal(l_)) // either l' is l or v |=¬l'
}

pub fn is_reason(c: &Clause, l: Literal, v: &Valuation) -> bool {
    // A clause c is a reason for propagation of literal l in valuation
    // v, denoted (isReason c l v) iff l ∈ c, v  l, v ¬(c \ l), and for each literal l′ ∈ (c \ l), the literal l′ precedes l in v.
    c.contains(l) &&
    v.is_true_literal(l) &&
    c.literals.iter().all(|&l_| l_ == l || v.is_false_literal(l_)) // either l' is l or v |=¬l'
}

pub fn resolvent(c1: &Clause, c2: &Clause, l: Literal) -> Clause {
    // The resolvent of two clauses c1 and c2 with literal l, denoted
    // (resolvent c1 c2 l) is the clause (c1 \ l)@(c2 \ opposite(l))
    Clause {
        literals: c1.literals
            .iter()
            .filter(|&&l_| l_ != l)
            .cloned()
            .chain(c2.literals.iter()
                .filter(|&&l_| l_ != -l)
                .cloned()
            ).collect()
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Satisfiability {
    Satisfiable,
    Unsatisfiable,
    Undefined,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MLiteral {
    literal: Literal,
    marked: bool,
}

impl MLiteral {
    pub fn new(literal: Literal, marked: bool) -> MLiteral {
        MLiteral { literal, marked }
    }
}

#[derive(Debug)]
pub struct Trail {
    elements: Vec<MLiteral>,
}

impl Trail {
    pub fn new(elements: Vec<MLiteral>) -> Trail {
        Trail { elements }
    }

    pub fn contains(&self, lit: &Literal) -> bool {
        self.elements.iter().any(|e| e.literal == *lit)
    }

    pub fn index_of(&self, lit: Literal) -> usize {
        self.elements.iter().position(|e| e.literal == lit).unwrap()
    }

    pub fn decisions(&self)-> impl Iterator<Item=&Literal> {
        self.elements.iter().filter(|e| e.marked).map(|e| &e.literal)
    }

    pub fn last_decision(&self) -> Option<&Literal> {
        self.decisions().last()
    }

    pub fn decisions_to(&self, l: Literal) -> impl Iterator<Item=&Literal> {
        // the list of all marked elements from a trail
        // M that precede the first occurrence of the element l, including l if it is marked.
        let mut seen = false;
        self.elements.iter().take_while(move |MLiteral { literal, marked }| {
            if !seen {
                // if the literal equals l, then we have found it, and only return true if it's marked.
                seen = *literal == l;
                if seen {
                    *marked
                } else {
                    true
                }
            } else {
                false
            }
        }).filter(|e| e.marked).map(|e| &e.literal)
    }

    pub fn current_level(&self) -> usize {
        self.decisions().count()
    }

    pub fn level(&self, l: Literal) -> usize {
        self.decisions_to(l).count()
    }

    pub fn prefix_to_level(&self, level: usize) -> impl Iterator<Item=&MLiteral> {
        let mut level = level + 1;
        self.elements.iter().take_while(move |MLiteral { marked, .. }| {
                if *marked {
                    level -= 1;
                }
                level > 0
            }
        )
    }

    pub fn prefix_before_last_decision(&self) -> impl Iterator<Item=&MLiteral> {
        self.prefix_to_level(self.current_level() - 1)
    }

    pub fn as_valuation(&self) -> Valuation {
        Valuation::new(self.elements.iter().map(|e| e.literal).collect())
    }

    pub fn vars(&self) -> HashSet<Literal> {
        self.elements.iter().map(|MLiteral { literal, marked: _ }| literal.abs()).collect()
    }
}

#[derive(Debug)]
pub struct SolveState {
    sat_flag: Satisfiability,
    formula: Formula,
    trail: Trail,
}

impl SolveState {
    pub fn new(formula: Formula) -> SolveState {
        SolveState {
            sat_flag: Satisfiability::Undefined,
            formula,
            trail: Trail::new(vec![]),
        }
    }

    pub fn solve(&mut self) -> Satisfiability {
        while self.sat_flag == Satisfiability::Undefined {
            // self.exhaustive_unit_propagate();
            if self.trail.as_valuation().is_false_formula(&self.formula) {
                if self.trail.decisions().count() == 0 {
                    self.sat_flag = Satisfiability::Unsatisfiable;
                } else {
                    self.apply_backtrack();
                }
            } else if self.trail.vars() == self.formula.vars() {
                self.sat_flag = Satisfiability::Satisfiable;
            } else {
                self.apply_decide();
            }
        }
        self.sat_flag
    }

    // fn exhaustive_unit_propagate(&mut self) -> bool {
    //     let mut ret;
    //     loop {
    //         ret = self.apply_unit_propagate();
    //         if ret == false || self.trail.as_valuation().is_false_formula(&self.formula) {
    //             break;
    //         }
    //     }
    //     ret
    // }

    // fn apply_unit_propagate(&mut self) -> bool {
    //     if /* ∃c.∃l. c ∈ F0 ∧ (isUnit c l M) */ {
    //         self.assert_literal(l, false);
    //         true
    //     } else {
    //         false
    //     }
    // }

    fn apply_decide(&mut self) {
        let l = self.select_literal();
        self.assert_literal(l, true);
    }

    fn apply_backtrack(&mut self) {
        let &l = self.trail.last_decision().unwrap();
        self.trail = Trail::new(self.trail.prefix_before_last_decision().copied().collect());
        self.assert_literal(-l, false);
    }

    fn assert_literal(&mut self, l: Literal, decision: bool) {
        self.trail.elements.push(
            MLiteral::new(l, decision)
        );
    }

    fn select_literal(&self) -> Literal {
        let t_vars = self.trail.vars();
        *self.formula.vars().iter().find(|v| {
            !t_vars.contains(v)
        }).unwrap()
    }

    pub fn get_model(&self) -> Option<Valuation> {
        match self.sat_flag {
            Satisfiability::Satisfiable => Some(self.trail.as_valuation()),
            _ => None,
        }
    }
}

pub fn parse_cnf(file_path: &str) -> Result<Formula, String> {
    let mut file = File::open(file_path).map_err(|e| e.to_string())?;
    let mut contents = String::new();
    file.read_to_string(&mut contents).map_err(|e| e.to_string())?;
    let lines = contents.lines();
    let mut clauses = vec![];
    for line in lines {
        if line.starts_with("p cnf") || line.starts_with('c') {
            continue;
        } else if line.contains('%') {
            break;
        } else {
            let parts = line.split_whitespace();
            let mut literals = vec![];
            for lit in parts {
                if lit == "0" {
                    break;
                }
                literals.push(Literal::from_str(lit).unwrap());
            }
            clauses.push(Clause::new(literals));
        }
    }
    Ok(Formula::new(clauses))
}