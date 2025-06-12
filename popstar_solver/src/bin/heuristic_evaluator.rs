use popstar_solver::engine::{Board, Game};
use popstar_solver::{ // Use crate name to access re-exported items
    choose_move_mis,
    choose_move_lgp,
    choose_move_crp,
    choose_move_misps
};
use std::collections::HashMap;
// No longer need rand/rand_pcg here if Board::new_random_with_seed is used.

const NUM_RANDOM_BOARDS_FOR_EVALUATION: usize = 20;
const START_SEED: u64 = 0; // Changed to u64 to match Board::new_random_with_seed parameter type

type StrategyFn = fn(&Board, &Vec<Vec<(usize, usize)>>) -> Vec<(usize, usize)>;

fn main() {
    let strategies: Vec<(&str, StrategyFn)> = vec![
        ("MIS", choose_move_mis),
        ("LGP", choose_move_lgp),
        ("CRP", choose_move_crp),
        ("MISPS", choose_move_misps),
    ];

    let mut all_scores: HashMap<String, Vec<u32>> = HashMap::new();
    for (name, _) in &strategies {
        all_scores.insert(name.to_string(), Vec::new());
    }

    println!("Starting heuristic evaluation for {} boards...", NUM_RANDOM_BOARDS_FOR_EVALUATION);

    for board_idx in 0..NUM_RANDOM_BOARDS_FOR_EVALUATION {
        let current_seed = START_SEED + board_idx as u64;
        // Create a seeded RNG for board generation
        // Using Board::new_random_with_seed which expects a u32 seed
        let initial_board = Board::new_random_with_seed(current_seed as u32);

        println!("\nEvaluating Board {} (Seed: {})", board_idx, current_seed);

        for (strategy_name, strategy_fn) in &strategies {
            let mut game = Game::new_with_board(initial_board.clone());
            // println!("  Testing strategy: {}", strategy_name); // For verbose logging

            loop {
                let available_groups = game.board().find_all_groups();
                if available_groups.is_empty() {
                    // println!("    No more moves for {}. Steps: {}", strategy_name, game.steps());
                    break;
                }

                let chosen_group_coords = strategy_fn(game.board(), &available_groups);

                if chosen_group_coords.is_empty() {
                     eprintln!("Warning: Strategy {} returned an empty group on board {} (Seed: {}). This should not happen if groups were available.", strategy_name, board_idx, current_seed);
                     break;
                }

                let (r_click, c_click) = chosen_group_coords[0]; // Get the first coord as the click point

                // process_move expects a click point and finds the group internally.
                // The strategy functions return the whole group.
                // We need to ensure game.process_move can handle this, or we adapt.
                // game.process_move(r,c) will find the group containing (r,c).
                // So, this is fine.
                let move_successful = game.process_move(r_click, c_click);

                if !move_successful {
                    eprintln!(
                        "Error: Strategy {} on board {} (Seed: {}) failed to make a valid move with click point {:?} derived from group {:?}. Board state:\n{}",
                        strategy_name, board_idx, current_seed, (r_click, c_click), chosen_group_coords, game.board()
                    );
                    break;
                }
            }
            let final_score_for_strategy = game.final_score();
            println!("  Strategy: {:<10}, Score: {:<6}, Steps: {}", strategy_name, final_score_for_strategy, game.steps());
            all_scores.get_mut(*strategy_name).unwrap().push(final_score_for_strategy);
        }
    }

    println!("\n--- Evaluation Complete ---");
    println!("Number of boards evaluated: {}", NUM_RANDOM_BOARDS_FOR_EVALUATION);
    println!("Strategies evaluated: {}", strategies.iter().map(|(name, _)| *name).collect::<Vec<&str>>().join(", "));
    println!("\n--- Average Scores ---");

    let mut sorted_avg_scores: Vec<(&str, f64)> = Vec::new();

    for (strategy_name, scores) in &all_scores {
        if scores.is_empty() {
            println!("Strategy {}: No scores recorded.", strategy_name);
            continue;
        }
        let total_score: u32 = scores.iter().sum();
        let avg_score = total_score as f64 / scores.len() as f64;
        sorted_avg_scores.push((strategy_name, avg_score));
    }

    // Sort by average score descending
    sorted_avg_scores.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));

    for (strategy_name, avg_score) in sorted_avg_scores {
         println!("Strategy {:<10}: Average Score = {:.2}", strategy_name, avg_score);
    }
}
