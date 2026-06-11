use popstar_solver::engine::{Board, Game};
use popstar_solver::solver::solve_dfs;
use std::time::Instant;

fn main() {
    // We use a small number of seeds and a moderate depth to keep evaluation fast
    let seeds = [123, 456, 789, 101112, 131415];
    let depth_limit = 5;

    let mut total_time = 0;
    let mut total_score = 0;
    let mut total_nodes = 0;

    println!("Starting evaluation (Depth Limit: {})...", depth_limit);
    for &seed in &seeds {
        let board = Board::new_random_with_seed(seed);
        let game = Game::new_with_board(board);

        let start = Instant::now();
        let (solution, nodes) = solve_dfs(&game, depth_limit);
        let duration = start.elapsed();

        let score = solution.map(|s| s.score).unwrap_or(0);

        println!(
            "Seed {:>8}: Score = {:>5}, Nodes = {:>6}, Time = {:?}",
            seed, score, nodes, duration
        );

        total_time += duration.as_millis();
        total_score += score;
        total_nodes += nodes;
    }

    println!("--------------------------------------------------");
    println!("Total Score: {}", total_score);
    println!("Total Nodes: {}", total_nodes);
    println!("Total Time:  {} ms", total_time);
}
