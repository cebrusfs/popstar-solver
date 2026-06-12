import re

with open("src/advanced_solvers.rs", "r") as f:
    code = f.read()

# Fix playout
old_playout = """            for &((r, c), _) in &moves {
                let w = *policy.get(&(state_key, r, c)).unwrap_or(&0.0);
                let e = w.exp();
                sum_exp += e;
                weights.push((r, c, e));
            }"""

new_playout = """            let max_w = moves.iter().map(|&((r, c), _)| *policy.get(&(state_key, r, c)).unwrap_or(&0.0)).fold(f64::NEG_INFINITY, f64::max);
            for &((r, c), _) in &moves {
                let w = *policy.get(&(state_key, r, c)).unwrap_or(&0.0);
                let e = (w - max_w).exp();
                sum_exp += e;
                weights.push((r, c, e));
            }"""

code = code.replace(old_playout, new_playout)

# Fix adapt
old_adapt = """            for &((mr, mc), _) in &moves {
                let w = *policy.get(&(state_key, mr, mc)).unwrap_or(&0.0);
                let e = w.exp();
                sum_exp += e;
                exps.push(((mr, mc), e));
            }"""

new_adapt = """            let max_w = moves.iter().map(|&((mr, mc), _)| *policy.get(&(state_key, mr, mc)).unwrap_or(&0.0)).fold(f64::NEG_INFINITY, f64::max);
            for &((mr, mc), _) in &moves {
                let w = *policy.get(&(state_key, mr, mc)).unwrap_or(&0.0);
                let e = (w - max_w).exp();
                sum_exp += e;
                exps.push(((mr, mc), e));
            }"""

code = code.replace(old_adapt, new_adapt)

with open("src/advanced_solvers.rs", "w") as f:
    f.write(code)

