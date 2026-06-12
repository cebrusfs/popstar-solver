use popstar_solver::engine::{Board, Game};
use popstar_solver::solver::solve_dfs;
use rayon::prelude::*;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

fn main() {
    let total_games = 100;
    let seeds: Vec<u64> = (1..=total_games).map(|x| x as u64).collect();
    let depth_limit = 5;

    println!("Starting evaluation (Depth Limit: {}, Games: {})...", depth_limit, total_games);

    let progress = AtomicUsize::new(0);
    let start_all = Instant::now();

    let results: Vec<(u32, u32, std::time::Duration)> = seeds
        .par_iter()
        .map(|&seed| {
            let board = Board::new_random_with_seed(seed);
            let game = Game::new_with_board(board);

            let start = Instant::now();
            let (solution, nodes) = solve_dfs(&game, depth_limit);
            let duration = start.elapsed();

            let score = solution.map(|s| s.score).unwrap_or(0);

            let p = progress.fetch_add(1, Ordering::SeqCst) + 1;
            println!("Completed {}/{} games (Seed: {}, Score: {})...", p, total_games, seed, score);

            (score, nodes, duration)
        })
        .collect();

    let total_time_elapsed = start_all.elapsed().as_millis();
    let total_score: u32 = results.iter().map(|r| r.0).sum();
    let total_nodes: u32 = results.iter().map(|r| r.1).sum();

    let avg_score = total_score as f64 / total_games as f64;
    let max_score = results.iter().map(|r| r.0).max().unwrap_or(0);

    println!("--------------------------------------------------");
    println!("Golden Set ({} seeds) Evaluation:", total_games);
    println!("Average Score: {:.1}", avg_score);
    println!("Max Score: {}", max_score);
    println!("Total Nodes: {}", total_nodes);
    println!("Total Time (Wall-clock): {} ms", total_time_elapsed);
}
