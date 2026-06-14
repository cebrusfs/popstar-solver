import re

with open('src/bin/arena.rs', 'r') as f:
    content = f.read()

# I will just write a clean script to replace UltimateMetaAgent and TabuRolloutBeamSearchAgent.
# Let's extract everything BEFORE TabuRolloutBeamSearchAgent
parts = content.split("struct TabuRolloutBeamSearchAgent")
prefix = parts[0]

# Everything after fn main
main_parts = content.split("fn main() {")
suffix = "fn main() {" + main_parts[1]

corrected_agents = """
struct TabuRolloutBeamSearchAgent {
    name: String,
    beam_width: usize,
    target_color: u8,
}
impl Agent for TabuRolloutBeamSearchAgent {
    fn name(&self) -> &str {
        &self.name
    }
    fn play(&self, initial_board: &Board) -> (i32, f64, usize) {
        let start = Instant::now();

        let mut beam: Vec<(Board, i32)> = vec![(initial_board.clone(), 0)];
        let mut best_final_score = 0;
        let mut min_remaining = usize::MAX;

        let mut depth = 0;

        loop {
            let mut next_beam: Vec<(Board, i32)> = Vec::new();
            let mut all_game_over = true;
            
            let current_beam_width = if depth < 5 { self.beam_width * 3 } else { self.beam_width };
            depth += 1;

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

            unique_vec.par_sort_by_cached_key(|(b, s)| {
                let mut rollout_board = b.clone();
                let mut r_score = 0;
                let mut r_penalty = 0;
                let mut used_endgame = false;
                
                let mut target_count = 0;
                for r in 0..10 {
                    for c in 0..10 {
                        if rollout_board.color_at(r, c) == self.target_color {
                            target_count += 1;
                        }
                    }
                }
                r_penalty += target_count as i32 * 50; 

                while !rollout_board.is_game_over() {
                    let remaining = count_remaining(&rollout_board);
                    if remaining <= 18 {
                        r_score += popstar_solver::endgame::solve_endgame(&rollout_board);
                        used_endgame = true;
                        break;
                    }

                    let groups = rollout_board.find_all_group_clicks_with_len();
                    if groups.is_empty() { break; }
                    
                    let mut best_move = groups[0].0;
                    let mut best_heuristic = i32::MIN;
                    
                    for &(pos, len) in &groups {
                        let mut temp = rollout_board.clone();
                        let group_color = rollout_board.color_at(pos.0, pos.1);
                        
                        temp.eliminate_group_by_click(pos.0, pos.1);
                        temp.apply_gravity();
                        temp.shift_columns();
                        
                        let move_score = (len * len * 5) as i32;
                        let h = calculate_predictive_heuristic(&temp);
                        
                        let tabu_penalty = if group_color == self.target_color { -2000 } else { 0 };
                        let total_h = move_score + h + tabu_penalty;
                        
                        if total_h > best_heuristic {
                            best_heuristic = total_h;
                            best_move = pos;
                        }
                    }
                    
                    let mut matched_len = 0;
                    let mut matched_color = 0;
                    for &(pos, len) in &groups {
                        if pos == best_move {
                            matched_len = len;
                            matched_color = rollout_board.color_at(pos.0, pos.1);
                            break;
                        }
                    }
                    let tabu_p = if matched_color == self.target_color { -2000 } else { 0 };
                    r_penalty += tabu_p;
                    r_score += (matched_len * matched_len * 5) as i32;
                    rollout_board.eliminate_group_by_click(best_move.0, best_move.1);
                    rollout_board.apply_gravity();
                    rollout_board.shift_columns();
                }

                let final_bonus = if used_endgame { 0 } else { Game::new_with_board(rollout_board).final_score() as i32 };
                let combined_score = *s + r_score + r_penalty + final_bonus;
                
                std::cmp::Reverse(combined_score)
            });

            unique_vec.truncate(current_beam_width);
            beam = unique_vec;
        }

        (best_final_score as i32, start.elapsed().as_secs_f64(), min_remaining)
    }
}

struct UltimateMetaAgent {
    name: String,
    beam_width: usize,
}
impl Agent for UltimateMetaAgent {
    fn name(&self) -> &str {
        &self.name
    }
    fn play(&self, initial_board: &Board) -> (i32, f64, usize) {
        use rayon::prelude::*;
        let start = Instant::now();
        
        let mut agents: Vec<Box<dyn Agent>> = Vec::new();
        agents.push(Box::new(RolloutBeamSearchAgent {
            name: "Baseline".to_string(),
            beam_width: self.beam_width,
        }));
        
        for color in 1..=5 {
            agents.push(Box::new(TabuRolloutBeamSearchAgent {
                name: format!("Tabu-{}", color),
                beam_width: self.beam_width,
                target_color: color,
            }));
        }
        
        let results: Vec<(i32, f64, usize)> = agents.par_iter().map(|agent| agent.play(initial_board)).collect();
        
        let mut best_score = -1;
        let mut best_rem = usize::MAX;
        for (s, _, r) in results {
            if s > best_score || (s == best_score && r < best_rem) {
                best_score = s;
                best_rem = r;
            }
        }
        
        (best_score, start.elapsed().as_secs_f64(), best_rem)
    }
}
"""

with open('src/bin/arena.rs', 'w') as f:
    f.write(prefix + corrected_agents + "\n" + suffix)
