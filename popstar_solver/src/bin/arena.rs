use popstar_solver::advanced_solvers::{MctsAgent, SpMctsAgent};
use popstar_solver::engine::{Board, Game, Tile, BOARD_SIZE};
use popstar_solver::heuristics::{
    calculate_admissible_heuristic, calculate_predictive_heuristic, choose_move_misps,
};
use rayon::prelude::*;
use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

trait Agent: Sync + Send {
    fn name(&self) -> &str;
    fn play(&self, initial_board: &Board) -> (i32, f64, usize); // (score, time_in_secs, remaining_tiles)
}

fn count_remaining(board: &Board) -> usize {
    let mut count = 0;
    for r in 0..BOARD_SIZE {
        for c in 0..BOARD_SIZE {
            if board.get_tile(r, c) != Tile::Empty {
                count += 1;
            }
        }
    }
    count
}

struct GreedyAgent;
impl Agent for GreedyAgent {
    fn name(&self) -> &str {
        "Greedy-MISPS"
    }
    fn play(&self, initial_board: &Board) -> (i32, f64, usize) {
        let start = Instant::now();
        let mut game = Game::new_with_board(initial_board.clone());
        while !game.is_game_over() {
            if let Some((_, click)) = choose_move_misps(game.board()) {
                game.process_move(click.0, click.1);
            } else {
                break;
            }
        }
        (game.final_score() as i32, start.elapsed().as_secs_f64(), count_remaining(game.board()))
    }
}

struct BeamSearchAgent {
    name: String,
    beam_width: usize,
    heuristic: fn(&Board) -> i32,
}
impl Agent for BeamSearchAgent {
    fn name(&self) -> &str {
        &self.name
    }
    fn play(&self, initial_board: &Board) -> (i32, f64, usize) {
        let start = Instant::now();

        let mut beam: Vec<(Board, i32)> = vec![(initial_board.clone(), 0)];
        let mut best_final_score = 0;
        let mut min_remaining = usize::MAX;

        loop {
            let mut next_beam: Vec<(Board, i32)> = Vec::new();
            let mut all_game_over = true;

            for (board, score) in beam {
                if board.is_game_over() {
                    let temp = Game::new_with_board(board.clone());
                    let final_score = score + temp.final_score() as i32;
                    if final_score > best_final_score {
                        best_final_score = final_score;
                    }
                    let remaining = count_remaining(&board);
                    if remaining < min_remaining {
                        min_remaining = remaining;
                    }
                    continue;
                }
                all_game_over = false;

                let groups = board.find_all_group_clicks_with_len();
                for ((r, c), len) in groups {
                    let mut next_board = board.clone();
                    next_board.eliminate_group_by_click(r, c);
                    next_board.apply_gravity();
                    next_board.shift_columns();

                    let move_score = (len * len * 5) as i32;
                    let next_score = score + move_score;
                    next_beam.push((next_board, next_score));
                }
            }

            if all_game_over || next_beam.is_empty() {
                break;
            }

            let mut unique_states: HashMap<[u64; 5], (Board, i32)> = HashMap::new();
            for (board, score) in next_beam {
                let key = board.to_packed();
                if let Some(&(_, old_score)) = unique_states.get(&key) {
                    if score > old_score {
                        unique_states.insert(key, (board, score));
                    }
                } else {
                    unique_states.insert(key, (board, score));
                }
            }

            let mut unique_vec: Vec<(Board, i32)> = unique_states.into_values().collect();

            unique_vec.sort_by_cached_key(|(b, s)| {
                let h = (self.heuristic)(b);
                -(s + h)
            });

            unique_vec.truncate(self.beam_width);
            beam = unique_vec;
        }

        (best_final_score as i32, start.elapsed().as_secs_f64(), min_remaining)
    }
}

struct ArenaMctsAgent {
    max_iterations: usize,
    time_budget_ms: u64,
    exploration_c: f64,
}
impl Agent for ArenaMctsAgent {
    fn name(&self) -> &str {
        "MCTS-100ms"
    }
    fn play(&self, initial_board: &Board) -> (i32, f64, usize) {
        let start = Instant::now();
        let mcts = MctsAgent::new(self.max_iterations, self.time_budget_ms, self.exploration_c);
        let mut board = initial_board.clone();
        let mut score = 0;

        while !board.is_game_over() {
            if let Some((_, move_score, next_board)) = mcts.select_move(&board, score) {
                board = next_board;
                score += move_score;
            } else {
                break;
            }
        }
        let final_bonus = Game::new_with_board(board.clone()).final_score() as i32;
        score += final_bonus;

        (score as i32, start.elapsed().as_secs_f64(), count_remaining(&board))
    }
}


struct ArenaSpMctsAgent {
    max_iterations: usize,
    time_budget_ms: u64,
    exploration_c: f64,
}
impl Agent for ArenaSpMctsAgent {
    fn name(&self) -> &str {
        "SP-MCTS-250ms"
    }
    fn play(&self, initial_board: &Board) -> (i32, f64, usize) {
        let start = Instant::now();
        let mcts = SpMctsAgent::new(self.max_iterations, self.time_budget_ms, self.exploration_c);
        let mut board = initial_board.clone();
        let mut score = 0;

        while !board.is_game_over() {
            if let Some((_, move_score, next_board)) = mcts.select_move(&board, score) {
                board = next_board;
                score += move_score;
            } else {
                break;
            }
        }
        let final_bonus = Game::new_with_board(board.clone()).final_score() as i32;
        score += final_bonus;

        (score as i32, start.elapsed().as_secs_f64(), count_remaining(&board))
    }
}

struct BmctsAgent {
    beam_width: usize,
    rollout_count: usize,
}
impl Agent for BmctsAgent {
    fn name(&self) -> &str {
        "BMCTS-W100-N20"
    }
    fn play(&self, initial_board: &Board) -> (i32, f64, usize) {
        let start = Instant::now();

        let mut beam: Vec<(Board, i32)> = vec![(initial_board.clone(), 0)];
        let mut best_final_score = 0;
        let mut min_remaining = usize::MAX;

        loop {
            let mut next_beam: Vec<(Board, i32)> = Vec::new();
            let mut all_game_over = true;

            for (board, score) in beam {
                if board.is_game_over() {
                    let temp = Game::new_with_board(board.clone());
                    let final_score = score + temp.final_score() as i32;
                    if final_score > best_final_score {
                        best_final_score = final_score;
                    }
                    let remaining = count_remaining(&board);
                    if remaining < min_remaining {
                        min_remaining = remaining;
                    }
                    continue;
                }
                all_game_over = false;

                let groups = board.find_all_group_clicks_with_len();
                for ((r, c), len) in groups {
                    let mut next_board = board.clone();
                    next_board.eliminate_group_by_click(r, c);
                    next_board.apply_gravity();
                    next_board.shift_columns();

                    let move_score = (len * len * 5) as i32;
                    let next_score = score + move_score;
                    next_beam.push((next_board, next_score));
                }
            }

            if all_game_over || next_beam.is_empty() {
                break;
            }

            let mut unique_states: HashMap<[u32; 10], (Board, i32)> = HashMap::new();
            for (board, score) in next_beam {
                let mut key = [0u32; 10];
                key.copy_from_slice(board.columns());
                if let Some(&(_, old_score)) = unique_states.get(&key) {
                    if score > old_score {
                        unique_states.insert(key, (board, score));
                    }
                } else {
                    unique_states.insert(key, (board, score));
                }
            }

            let mut unique_vec: Vec<(Board, i32)> = unique_states.into_values().collect();

            unique_vec.sort_by_cached_key(|(b, s)| {
                let mut total_rollout_score = 0;
                for _ in 0..self.rollout_count {
                    let mut rollout_board = b.clone();
                    let mut r_score = 0;
                    while !rollout_board.is_game_over() {
                        let groups = rollout_board.find_all_group_clicks_with_len();
                        if groups.is_empty() { break; }
                        let mut max_len = 0;
                        let mut best_move = (0, 0);
                        for &(pos, len) in &groups {
                            if len > max_len {
                                max_len = len;
                                best_move = pos;
                            }
                        }
                        let move_score = max_len * max_len * 5;
                        r_score += move_score as i32;
                        rollout_board.eliminate_group_by_click(best_move.0, best_move.1);
                        rollout_board.apply_gravity();
                        rollout_board.shift_columns();
                    }
                    let final_bonus = Game::new_with_board(rollout_board).final_score() as i32;
                    total_rollout_score += r_score + final_bonus;
                }
                let avg_rollout_score = total_rollout_score / (self.rollout_count as i32);
                let combined_score = *s + avg_rollout_score;
                
                std::cmp::Reverse(combined_score)
            });

            unique_vec.truncate(self.beam_width);
            beam = unique_vec;
        }

        (best_final_score as i32, start.elapsed().as_secs_f64(), min_remaining)
    }
}

fn main() {
    println!("=== PopStar AI Arena ===");

    let total_games = std::env::var("NUM_GAMES")
        .unwrap_or_else(|_| "10".to_string())
        .parse::<usize>()
        .unwrap_or(10);
    let seeds: Vec<u64> = (1..=total_games).map(|x| x as u64).collect();

    let greedy_agent = GreedyAgent;
    let bmcts_agent = BmctsAgent { beam_width: 100, rollout_count: 20 };
    let beam_agent_50 = BeamSearchAgent { name: "BeamSearch-W50-V2".to_string(), beam_width: 50, heuristic: calculate_predictive_heuristic };
    let beam_agent_500 = BeamSearchAgent { name: "BeamSearch-W500-V2".to_string(), beam_width: 500, heuristic: calculate_predictive_heuristic };
    let beam_agent_5000 = BeamSearchAgent { name: "BeamSearch-W5000-V2".to_string(), beam_width: 5000, heuristic: calculate_predictive_heuristic };
    let sp_mcts_agent = ArenaSpMctsAgent { max_iterations: 20000, time_budget_ms: 250, exploration_c: 500.0 };
    let mcts_agent =
        ArenaMctsAgent { max_iterations: 5000, time_budget_ms: 50, exploration_c: 1000.0 };

    let agents: Vec<&dyn Agent> =
        vec![&bmcts_agent, &beam_agent_5000, &beam_agent_500, &beam_agent_50, &sp_mcts_agent, &mcts_agent, &greedy_agent];

    let agent_names: Vec<&str> = agents.iter().map(|a| a.name()).collect();
    println!("Agents: {}", agent_names.join(", "));
    println!("Running {} games (parallel)...\n", total_games);

    let progress = AtomicUsize::new(0);

    let results: Vec<Vec<(i32, f64, usize)>> = agents
        .par_iter()
        .map(|&agent| {
            let mut agent_results = Vec::new();
            for &seed in &seeds {
                let board = Board::new_random_with_seed(seed);
                let res = agent.play(&board);
                agent_results.push(res);
                let p = progress.fetch_add(1, Ordering::SeqCst) + 1;
                if p % 10 == 0 {
                    println!("Completed {}/{} agent-games...", p, total_games * agents.len());
                }
            }
            agent_results
        })
        .collect();

    println!("\n--- LEADERBOARD ---");
    for (i, agent) in agents.iter().enumerate() {
        let scores: Vec<i32> = results[i].iter().map(|r| r.0).collect();
        let times: Vec<f64> = results[i].iter().map(|r| r.1).collect();
        let clears: usize = results[i].iter().filter(|r| r.2 == 0).count();

        let avg_score: f64 = scores.iter().map(|&x| x as f64).sum::<f64>() / (total_games as f64);
        let max_score = *scores.iter().max().unwrap_or(&0);
        let avg_time = times.iter().sum::<f64>() / (total_games as f64);
        let clear_rate = (clears as f64 / total_games as f64) * 100.0;

        println!("{}. {}", i + 1, agent.name());
        println!(
            "   Avg Score: {:.1} | Max Score: {} | Clear Rate: {:.1}% | Avg Time: {:.4}s",
            avg_score, max_score, clear_rate, avg_time
        );
    }
}
