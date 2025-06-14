use popstar_solver::engine::{Board, Game};
use popstar_solver::heuristics::{
    choose_move_avoid_orphans, choose_move_clear_focus, choose_move_connectivity_focus,
    choose_move_crp, choose_move_lgp, choose_move_mis, choose_move_misps,
    choose_move_misps_clear_tiebreak, // Added new heuristic import
    choose_move_preserve_largest_color_group, choose_move_sgp,
};
use std::collections::HashMap;

const NUM_RANDOM_BOARDS_FOR_EVALUATION: usize = 20;
const START_SEED: u64 = 0;

trait Strategy {
    fn choose_move(&self, board: &Board) -> Option<(usize, usize)>;
    fn name(&self) -> &str;
}

struct MisStrategy;
impl Strategy for MisStrategy {
    fn name(&self) -> &str {
        "MIS"
    }
    fn choose_move(&self, board: &Board) -> Option<(usize, usize)> {
        choose_move_mis(board).map(|(_score, coord)| coord)
    }
}

struct LgpStrategy;
impl Strategy for LgpStrategy {
    fn name(&self) -> &str {
        "LGP"
    }
    fn choose_move(&self, board: &Board) -> Option<(usize, usize)> {
        choose_move_lgp(board).map(|(_len, coord)| coord)
    }
}

struct CrpStrategy;
impl Strategy for CrpStrategy {
    fn name(&self) -> &str {
        "CRP"
    }
    fn choose_move(&self, board: &Board) -> Option<(usize, usize)> {
        choose_move_crp(board).map(|(_score_pair, coord)| coord)
    }
}

struct MispsStrategy;
impl Strategy for MispsStrategy {
    fn name(&self) -> &str {
        "MISPS"
    }
    fn choose_move(&self, board: &Board) -> Option<(usize, usize)> {
        choose_move_misps(board).map(|(_heuristic_val, coord)| coord)
    }
}

struct SgpStrategy;
impl Strategy for SgpStrategy {
    fn name(&self) -> &str {
        "SGP"
    }
    fn choose_move(&self, board: &Board) -> Option<(usize, usize)> {
        choose_move_sgp(board).map(|(_metric, coord)| coord)
    }
}

struct ClearFocusStrategy;
impl Strategy for ClearFocusStrategy {
    fn name(&self) -> &str {
        "ClrFocus"
    }
    fn choose_move(&self, board: &Board) -> Option<(usize, usize)> {
        choose_move_clear_focus(board).map(|(_metric, coord)| coord)
    }
}

struct AvoidOrphansStrategy;
impl Strategy for AvoidOrphansStrategy {
    fn name(&self) -> &str {
        "AvdOrphn"
    }
    fn choose_move(&self, board: &Board) -> Option<(usize, usize)> {
        choose_move_avoid_orphans(board).map(|(_metric, coord)| coord)
    }
}

struct PreserveLrgClrStrategy;
impl Strategy for PreserveLrgClrStrategy {
    fn name(&self) -> &str {
        "PrsrvLrgC"
    }
    fn choose_move(&self, board: &Board) -> Option<(usize, usize)> {
        choose_move_preserve_largest_color_group(board).map(|(_metric, coord)| coord)
    }
}

struct ConnectivityStrategy;
impl Strategy for ConnectivityStrategy {
    fn name(&self) -> &str {
        "CnctFcs"
    }
    fn choose_move(&self, board: &Board) -> Option<(usize, usize)> {
        choose_move_connectivity_focus(board).map(|(_metric, coord)| coord)
    }
}

// New Strategy for MISPS_ClearTieBreak
struct MispsCtbStrategy;
impl Strategy for MispsCtbStrategy {
    fn name(&self) -> &str {
        "MISPS_CTB"
    }
    fn choose_move(&self, board: &Board) -> Option<(usize, usize)> {
        choose_move_misps_clear_tiebreak(board).map(|(_heuristic_val, coord)| coord)
    }
}

fn main() {
    let strategies: Vec<Box<dyn Strategy>> = vec![
        Box::new(MisStrategy),
        Box::new(LgpStrategy),
        Box::new(CrpStrategy),
        Box::new(MispsStrategy),
        Box::new(SgpStrategy),
        Box::new(ClearFocusStrategy),
        Box::new(AvoidOrphansStrategy),
        Box::new(PreserveLrgClrStrategy),
        Box::new(ConnectivityStrategy),
        Box::new(MispsCtbStrategy), // Added new strategy instance
    ];

    let mut all_scores: HashMap<String, Vec<i32>> = HashMap::new();
    let mut win_counts: HashMap<String, u32> = HashMap::new();

    for strategy in &strategies {
        all_scores.insert(strategy.name().to_string(), Vec::new());
        win_counts.insert(strategy.name().to_string(), 0);
    }

    println!(
        "Starting heuristic evaluation for {} boards...",
        NUM_RANDOM_BOARDS_FOR_EVALUATION
    );

    for board_idx in 0..NUM_RANDOM_BOARDS_FOR_EVALUATION {
        let current_seed = START_SEED + board_idx as u64;
        let initial_board = Board::new_random_with_seed(current_seed as u32);

        println!("");
        println!("Evaluating Board {} (Seed: {})", board_idx, current_seed);

        for strategy in &strategies {
            let strategy_name = strategy.name();
            let mut game = Game::new_with_board(initial_board.clone());

            loop {
                if game.board().find_all_groups().is_empty() {
                    break;
                }

                if let Some(chosen_coord) = strategy.choose_move(game.board()) {
                    let (r_click, c_click) = chosen_coord;
                    let move_successful = game.process_move(r_click, c_click);

                    if !move_successful {
                        eprintln!(
                            "Error: Strategy {} on board {} (Seed: {}) failed to make a valid move with click point {:?}. Board state:\n{}",
                            strategy_name, board_idx, current_seed, (r_click, c_click), game.board()
                        );
                        break;
                    }
                } else {
                    break;
                }
            }
            let final_score_for_strategy = game.final_score();
            println!(
                "  Strategy: {:<12}, Score: {:<6}, Steps: {}",
                strategy_name,
                final_score_for_strategy,
                game.steps()
            );
            all_scores
                .get_mut(strategy_name)
                .unwrap()
                .push(final_score_for_strategy);
        }

        let mut current_board_max_score: i32 = i32::MIN;
        let mut first_score_on_board = true;

        for strategy_name_key in strategies.iter().map(|s| s.name()) {
            if let Some(scores_vec) = all_scores.get(strategy_name_key) {
                if let Some(&score) = scores_vec.last() {
                    if first_score_on_board || score > current_board_max_score {
                        current_board_max_score = score;
                        first_score_on_board = false;
                    }
                }
            }
        }

        if !first_score_on_board {
            for strategy_name_key in strategies.iter().map(|s| s.name()) {
                if let Some(scores_vec) = all_scores.get(strategy_name_key) {
                    if let Some(&score) = scores_vec.last() {
                        if score == current_board_max_score {
                            *win_counts.get_mut(strategy_name_key).unwrap() += 1;
                        }
                    }
                }
            }
        }
    }

    println!("");
    println!("--- Evaluation Complete ---");
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
    println!("");
    println!("--- Average Scores ---");

    let mut sorted_avg_scores: Vec<(String, f64)> = Vec::new();

    for (strategy_name_str, scores) in &all_scores {
        if scores.is_empty() {
            println!("Strategy {}: No scores recorded.", strategy_name_str);
            continue;
        }
        let total_score: i32 = scores.iter().sum();
        let avg_score = total_score as f64 / scores.len() as f64;
        sorted_avg_scores.push((strategy_name_str.clone(), avg_score));
    }

    sorted_avg_scores.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));

    for (strategy_name, avg_score) in sorted_avg_scores {
        println!(
            "Strategy {:<12}: Average Score = {:.2}",
            strategy_name, avg_score
        );
    }

    println!("");
    println!("--- Win Counts (Highest Score on a Board) ---");
    let mut sorted_win_counts: Vec<(String, u32)> = win_counts.into_iter().collect();
    sorted_win_counts.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));

    for (strategy_name, wins) in sorted_win_counts {
        println!("Strategy {:<12}: Wins = {}", strategy_name, wins);
    }
}
