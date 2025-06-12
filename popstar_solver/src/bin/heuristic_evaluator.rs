use popstar_solver::engine::{Board, Game};
use popstar_solver::heuristics::{ // Corrected module path
    choose_move_crp,
    choose_move_lgp,
    choose_move_mis,
    choose_move_misps,
};
use std::collections::HashMap;
// No longer need rand/rand_pcg here if Board::new_random_with_seed is used.

const NUM_RANDOM_BOARDS_FOR_EVALUATION: usize = 20;
const START_SEED: u64 = 0; // Changed to u64 to match Board::new_random_with_seed parameter type

// Define a new trait for strategies to handle varying ScoreTypes
// The choose_move functions now return a single coordinate pair (usize, usize)
trait Strategy {
    fn choose_move(&self, board: &Board) -> Option<(usize, usize)>; // Changed return type
    fn name(&self) -> &str;
}

// Implement the trait for each strategy
struct MisStrategy;
impl Strategy for MisStrategy {
    fn name(&self) -> &str {
        "MIS"
    }
    fn choose_move(&self, board: &Board) -> Option<(usize, usize)> { // Changed return type
        choose_move_mis(board).map(|(_score, coord)| coord) // coord is now (usize, usize)
    }
}

struct LgpStrategy;
impl Strategy for LgpStrategy {
    fn name(&self) -> &str {
        "LGP"
    }
    fn choose_move(&self, board: &Board) -> Option<(usize, usize)> { // Changed return type
        choose_move_lgp(board).map(|(_len, coord)| coord) // coord is now (usize, usize)
    }
}

struct CrpStrategy;
impl Strategy for CrpStrategy {
    fn name(&self) -> &str {
        "CRP"
    }
    fn choose_move(&self, board: &Board) -> Option<(usize, usize)> { // Changed return type
        choose_move_crp(board).map(|(_score_pair, coord)| coord) // coord is now (usize, usize)
    }
}

struct MispsStrategy;
impl Strategy for MispsStrategy {
    fn name(&self) -> &str {
        "MISPS"
    }
    fn choose_move(&self, board: &Board) -> Option<(usize, usize)> { // Changed return type
        choose_move_misps(board).map(|(_heuristic_val, coord)| coord) // coord is now (usize, usize)
    }
}

fn main() {
    // Store strategies as a Vec of Box<dyn Strategy>
    let strategies: Vec<Box<dyn Strategy>> = vec![
        Box::new(MisStrategy),
        Box::new(LgpStrategy),
        Box::new(CrpStrategy),
        Box::new(MispsStrategy),
    ];

    let mut all_scores: HashMap<String, Vec<u32>> = HashMap::new();
    for strategy in &strategies {
        all_scores.insert(strategy.name().to_string(), Vec::new());
    }

    println!(
        "Starting heuristic evaluation for {} boards...",
        NUM_RANDOM_BOARDS_FOR_EVALUATION
    );

    for board_idx in 0..NUM_RANDOM_BOARDS_FOR_EVALUATION {
        let current_seed = START_SEED + board_idx as u64;
        let initial_board = Board::new_random_with_seed(current_seed as u32);

        println!("\nEvaluating Board {} (Seed: {})", board_idx, current_seed);

        for strategy in &strategies {
            let strategy_name = strategy.name();
            let mut game = Game::new_with_board(initial_board.clone());

            loop {
                // Check if game is over (no more groups)
                if game.board().find_all_groups().is_empty() {
                    break;
                }

                // Use the strategy to choose a move
                if let Some(chosen_coord) = strategy.choose_move(game.board()) {
                    // chosen_coord is now Option<(usize, usize)> as per Strategy trait update
                    // No need to check if chosen_coord.is_empty() as it's not a Vec.
                    // The Option wrapping handles "no move".

                    let (r_click, c_click) = chosen_coord; // chosen_coord is (usize, usize)
                    let move_successful = game.process_move(r_click, c_click);

                    if !move_successful {
                        eprintln!(
                            "Error: Strategy {} on board {} (Seed: {}) failed to make a valid move with click point {:?}. Board state:\n{}",
                            strategy_name, board_idx, current_seed, (r_click, c_click), game.board()
                        );
                        break;
                    }
                } else {
                    // Strategy returned None, meaning no move was chosen (e.g., board became empty according to heuristic)
                    // This can be a natural end for a strategy's evaluation path.
                    break;
                }
            }
            let final_score_for_strategy = game.final_score();
            println!(
                "  Strategy: {:<10}, Score: {:<6}, Steps: {}",
                strategy_name,
                final_score_for_strategy,
                game.steps()
            );
            all_scores
                .get_mut(strategy_name)
                .unwrap()
                .push(final_score_for_strategy);
        }
    }

    println!("\n--- Evaluation Complete ---");
    println!(
        "Number of boards evaluated: {}",
        NUM_RANDOM_BOARDS_FOR_EVALUATION
    );
    println!(
        "Strategies evaluated: {}",
        strategies
            .iter()
            .map(|s| s.name())
            .collect::<Vec<&str>>()
            .join(", ")
    );
    println!("\n--- Average Scores ---");

    let mut sorted_avg_scores: Vec<(String, f64)> = Vec::new();

    for (strategy_name_str, scores) in &all_scores {
        if scores.is_empty() {
            println!("Strategy {}: No scores recorded.", strategy_name_str);
            continue;
        }
        let total_score: u32 = scores.iter().sum();
        let avg_score = total_score as f64 / scores.len() as f64;
        sorted_avg_scores.push((strategy_name_str.clone(), avg_score));
    }

    // Sort by average score descending
    sorted_avg_scores.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));

    for (strategy_name, avg_score) in sorted_avg_scores {
        println!(
            "Strategy {:<10}: Average Score = {:.2}",
            strategy_name, avg_score
        );
    }
}
