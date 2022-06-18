mod dpll;
mod tests;

fn main() {
    let cnf = dpll::parse_cnf("CNFs/uf20-01.cnf").unwrap();

    let mut solver = dpll::SolveState::new(cnf);
    let start_time = std::time::Instant::now();
    solver.solve();
    let end_time = std::time::Instant::now();
    let model = solver.get_model().unwrap();

    println!("{}", model);
    println!("solved in {} ms", end_time.duration_since(start_time).as_millis());
}
