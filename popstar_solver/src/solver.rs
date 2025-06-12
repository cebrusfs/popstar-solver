use crate::engine::{Board, Game, Tile, BOARD_SIZE}; // Add Tile and BOARD_SIZE here
use std::collections::{BinaryHeap, HashMap, HashSet}; // Add HashMap and BinaryHeap here

/// Represents a solution found by the solver.
#[derive(Clone, Debug)]
pub struct Solution {
    /// Sequence of (row, column) clicks representing the moves.
    pub moves: Vec<(usize, usize)>,
    /// The final score achieved after these moves, including any end-game bonus.
    pub score: u32,
    /// The number of moves (eliminations) performed by the solver to reach this solution.
    /// This corresponds to the `steps` in the `Game` struct.
    pub steps_taken: u32,
}

#[derive(Clone, Debug)]
struct AStarNode {
    game_state: Game,
    moves: Vec<(usize, usize)>,
    g_score: u32,
    f_score: i64,
}

// Helper function to count tiles that cannot form a group of 2 or more
fn count_truly_isolated_tiles(board: &Board) -> u32 {
    let mut isolated_count = 0;
    // visited_for_groups tracks tiles that are part of any group of size >= 2
    let mut visited_for_groups = [[false; BOARD_SIZE]; BOARD_SIZE];

    // Mark all tiles that belong to valid groups
    for r_idx in 0..BOARD_SIZE {
        for c_idx in 0..BOARD_SIZE {
            if !visited_for_groups[r_idx][c_idx] && board.get_tile(r_idx, c_idx) != Tile::Empty {
                // find_group will return an empty vec if the tile at (r_idx, c_idx)
                // alone doesn't form a group of >= 2.
                // Or it returns the group members.
                let group = board.find_group(r_idx, c_idx);
                if !group.is_empty() { // group.len() >= 2 implicitly by find_group contract
                    for &(gr, gc) in &group {
                        visited_for_groups[gr][gc] = true;
                    }
                }
            }
        }
    }

    // Count non-empty tiles that were not part of any valid group
    for r_idx in 0..BOARD_SIZE {
        for c_idx in 0..BOARD_SIZE {
            if !visited_for_groups[r_idx][c_idx] && board.get_tile(r_idx, c_idx) != Tile::Empty {
                isolated_count += 1;
            }
        }
    }
    isolated_count
}

impl Ord for AStarNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.f_score.cmp(&self.f_score)
    }
}

impl PartialOrd for AStarNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Eq for AStarNode {}

impl PartialEq for AStarNode {
    fn eq(&self, other: &Self) -> bool {
        self.f_score == other.f_score && self.g_score == other.g_score
    }
}

// Placed before solve_a_star, uses evaluate_with_heuristic from the same module.

// New constant for the penalty factor
const ISOLATED_TILE_PENALTY_FACTOR: u32 = 10; // Value can be tuned

fn calculate_heuristic_a_star(game_state: &Game) -> u32 {
    let mut temp_game_for_heuristic = game_state.clone();
    let estimated_total_score_from_this_state = evaluate_with_heuristic(temp_game_for_heuristic);

    let base_future_score = if estimated_total_score_from_this_state >= game_state.score() {
        estimated_total_score_from_this_state - game_state.score()
    } else {
        0
    };

    let num_isolated = count_truly_isolated_tiles(game_state.board());
    let penalty = num_isolated * ISOLATED_TILE_PENALTY_FACTOR;

    // Apply penalty, ensuring heuristic doesn't go below zero
    if base_future_score >= penalty {
        base_future_score - penalty
    } else {
        0
    }
}

pub fn solve_a_star(initial_game: &Game, iteration_limit: u32) -> (Option<Solution>, u32) { // Changed return type
    let mut open_set = BinaryHeap::new();
    let mut closed_set: HashMap<Board, u32> = HashMap::new();

    let initial_h_score = calculate_heuristic_a_star(initial_game);
    let initial_g_score = initial_game.score();

    open_set.push(AStarNode {
        game_state: initial_game.clone(),
        moves: Vec::new(),
        g_score: initial_g_score,
        f_score: -((initial_g_score + initial_h_score) as i64),
    });

    let mut best_solution_if_game_over: Option<Solution> = None;
    let mut iterations_count: u32 = 0; // Renamed from 'iterations'

    while let Some(current_node) = open_set.pop() {
        iterations_count += 1;
        if iteration_limit > 0 && iterations_count > iteration_limit {
            break;
        }

        let current_board = current_node.game_state.board().clone();
        let current_g_score = current_node.g_score;

        if let Some(&existing_best_g_score) = closed_set.get(&current_board) {
            if current_g_score <= existing_best_g_score {
                continue;
            }
        }
        closed_set.insert(current_board.clone(), current_g_score);

        if current_node.game_state.is_game_over() {
            let final_score_at_game_over = current_node.game_state.final_score();
            if best_solution_if_game_over.is_none() || final_score_at_game_over > best_solution_if_game_over.as_ref().unwrap().score {
                best_solution_if_game_over = Some(Solution {
                    moves: current_node.moves.clone(),
                    score: final_score_at_game_over,
                    steps_taken: current_node.game_state.steps(),
                });
            }
            continue;
        }

        let available_groups = current_node.game_state.board().find_all_groups();

        if available_groups.is_empty() {
             let final_score_at_no_moves = current_node.game_state.final_score();
             if best_solution_if_game_over.is_none() || final_score_at_no_moves > best_solution_if_game_over.as_ref().unwrap().score {
                best_solution_if_game_over = Some(Solution {
                    moves: current_node.moves.clone(),
                    score: final_score_at_no_moves,
                    steps_taken: current_node.game_state.steps(),
                });
            }
            continue;
        }

        for group_to_eliminate in available_groups {
            if group_to_eliminate.is_empty() { continue; }
            let (r_click, c_click) = group_to_eliminate[0];
            let mut neighbor_game_state = current_node.game_state.clone();
            let move_was_valid = neighbor_game_state.process_move(r_click, c_click);

            if !move_was_valid {
                // eprintln!("Warning: A* found a group that process_move deemed invalid."); // Silencing for now
                continue;
            }

            let neighbor_board_key = neighbor_game_state.board().clone();
            let tentative_neighbor_g_score = neighbor_game_state.score();

            if let Some(&existing_g_score_for_neighbor) = closed_set.get(&neighbor_board_key) {
                if tentative_neighbor_g_score <= existing_g_score_for_neighbor {
                    continue;
                }
            }

            let neighbor_h_score = calculate_heuristic_a_star(&neighbor_game_state);
            let neighbor_f_score_val = tentative_neighbor_g_score + neighbor_h_score;
            let mut new_moves_path = current_node.moves.clone();
            new_moves_path.push((r_click, c_click));

            open_set.push(AStarNode {
                game_state: neighbor_game_state,
                moves: new_moves_path,
                g_score: tentative_neighbor_g_score,
                f_score: -(neighbor_f_score_val as i64),
            });
        }
    }
    // Loop finished (open_set empty or iteration_limit reached)
    (best_solution_if_game_over, iterations_count) // Return tuple
}

/// Solves the PopStar game using DFS up to the specified depth limit.
pub fn solve_dfs(initial_game: &Game, depth_limit: u32) -> (Option<Solution>, u32) { // Changed return type
    let mut visited_states = HashSet::new();
    visited_states.insert(initial_game.board().clone());

    // Initial call to the recursive helper
    let mut nodes_explored_dfs: u32 = 0; // Initialize counter for DFS
    let solution_opt = find_best_solution_recursive(
        initial_game.clone(),
        depth_limit,
        &mut visited_states,
        Vec::new(),
        &mut nodes_explored_dfs, // Pass counter to recursive function
    );
    (solution_opt, nodes_explored_dfs) // Return tuple with actual nodes explored
}

fn find_best_solution_recursive(
    current_game_state: Game,
    depth_remaining: u32,
    visited_states: &mut HashSet<Board>,
    current_moves_path: Vec<(usize, usize)>,
    nodes_explored: &mut u32, // New parameter
) -> Option<Solution> {
    *nodes_explored += 1; // Increment counter

    if current_game_state.is_game_over() {
        return Some(Solution {
            moves: current_moves_path,
            score: current_game_state.final_score(),
            steps_taken: current_game_state.steps(),
        });
    }

    if depth_remaining == 0 {
        let steps = current_game_state.steps();
        let heuristic_score = evaluate_with_heuristic(current_game_state);
        return Some(Solution {
            moves: current_moves_path,
            score: heuristic_score,
            steps_taken: steps,
        });
    }

    let mut best_solution_found: Option<Solution> = None;

    let available_groups = current_game_state.board().find_all_groups();

    if available_groups.is_empty() {
        return Some(Solution {
            moves: current_moves_path,
            score: current_game_state.final_score(),
            steps_taken: current_game_state.steps(),
        });
    }

    for group in available_groups {
        assert!(!group.is_empty());

        let (r_click, c_click) = group[0];

        let mut next_game_state = current_game_state.clone();
        let move_was_valid = next_game_state.process_move(r_click, c_click);

        assert!(move_was_valid);

        if visited_states.contains(next_game_state.board()) {
            continue;
        }
        visited_states.insert(next_game_state.board().clone());

        let mut new_moves_path = current_moves_path.clone();
        new_moves_path.push((r_click, c_click));

        if let Some(solution_from_this_path) = find_best_solution_recursive(
            next_game_state,
            depth_remaining - 1,
            visited_states,
            new_moves_path,
            nodes_explored, // Pass counter recursively
        ) {
            if best_solution_found.is_none() || solution_from_this_path.score > best_solution_found.as_ref().unwrap().score {
                best_solution_found = Some(solution_from_this_path);
            }
        }

        // Backtrack: Remove the state from visited_states if we want to allow reaching this state via a *longer* path
        // if it could potentially lead to a better overall score from there.
        // However, typical DFS with visited set for cycle/duplicate prevention keeps it visited.
        // If a state is reached with fewer moves (higher depth_remaining) and lower score, but could lead
        // to a better outcome than a path that reached it with more moves, this needs careful handling.
        // For now, standard duplicate state pruning: once visited, it's done for this search branch.
        // If using A* or similar, visited set might store score-to-reach.
        // For simple DFS max score, if we reach a state, we explore from it. If we reach it again
        // and have already explored it, no need to re-explore.
        // The problem is if path A reaches state S with score X, and path B reaches S with score Y.
        // If X > Y, path A is better to get to S.
        // current_game_state.undo_last_move(); // Not needed as we clone for each path
        // visited_states.remove(next_game_state.board()); // Backtrack: allow this state to be visited by other paths
                                                        // This is important if two different move sequences lead to the same board
                                                        // but we are only pruning based on board state.
                                                        // If we don't remove, we might miss optimal paths that go through this state
                                                        // but were preceded by a different sequence of moves.
                                                        // Consider: Path1 -> StateA (score 100), Path2 -> StateA (score 50).
                                                        // If Path1 is explored first, StateA is marked. Path2 won't explore from StateA.
                                                        // This is generally fine if we assume exploring from StateA always yields same *additional* score.
                                                        // The issue is if the *path length* (depth) matters.
                                                        // Let's stick to common DFS: add when exploring, don't remove for pruning duplicates.
                                                        // If a state is truly identical, the outcome from it should be identical.
                                                        // The `visited_states.insert` before recursion and no removal is typical.
                                                        //
                                                        // Re-evaluating: The C++ version has `hash_table.insert(h)` and no removal inside the loop.
                                                        // So, once a board state (hash) is processed at a certain depth in the DFS tree,
                                                        // it's not re-processed *by that specific parent's recursive call chain*.
                                                        // However, another branch of DFS might re-encounter it.
                                                        // A global visited set for the entire `solve_dfs` call is more effective.
                                                        // The current `visited_states` is passed mutably and accumulates.
                                                        // So, if `visited_states.insert()` returns true (was not already there), we recurse.
                                                        // This is the correct model.
                                                        // The `visited_states.remove()` after the recursive call is for specific types of search
                                                        // where paths to the same state with different costs are important, not typically for this kind of state-space DFS.
                                                        // So, no `visited_states.remove()` here.
    }

    // If no moves were made (e.g., all led to already visited states or were invalid),
    // we should still return a solution based on the current_game_state before trying moves.
    // This could happen if all available_groups lead to already visited states.
    if best_solution_found.is_none() {
        // This means either available_groups was empty (covered by is_game_over),
        // or all moves from here led to already visited states or were somehow invalid.
        // In this scenario, the "solution" from this point is just the current state itself,
        // as no further valid, unvisited moves can be made.
        return Some(Solution {
            moves: current_moves_path,
            score: current_game_state.final_score(),
            steps_taken: current_game_state.steps(),
        });
    }

    best_solution_found
}

fn evaluate_with_heuristic(mut game_state: Game) -> u32 {

    while !game_state.is_game_over() {
        let available_moves_coords = game_state.board().find_all_groups();

        if available_moves_coords.is_empty() {
            break;
        }

        let mut best_move_coord: Option<(usize, usize)> = None;
        let mut max_immediate_score = 0;

        for group in &available_moves_coords {

            let n = group.len() as u32;
            let immediate_score = n * n * 5;

            if immediate_score > max_immediate_score {
                max_immediate_score = immediate_score;
                best_move_coord = Some(group[0]);
            }
        }

        if let Some((r_best, c_best)) = best_move_coord {
            game_state.process_move(r_best, c_best);
        } else {
            break;
        }
    }
    game_state.final_score()
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::board_from_str_array;
    use crate::engine::{Tile, BOARD_SIZE as ENGINE_BOARD_SIZE}; // Renamed to avoid conflict with helper

    // Helper function for test board creation
    fn board_from_minimal_str_array(test_rows: &[&str]) -> Board {
        // Use ENGINE_BOARD_SIZE to refer to the constant from crate::engine
        let mut full_rows_data = Vec::new();
        for r_idx in 0..ENGINE_BOARD_SIZE {
            if r_idx < test_rows.len() {
                let mut row_str = test_rows[r_idx].to_string();
                while row_str.len() < ENGINE_BOARD_SIZE {
                    row_str.push('.'); // Pad columns
                }
                full_rows_data.push(row_str);
            } else {
                full_rows_data.push(".".repeat(ENGINE_BOARD_SIZE)); // Pad rows
            }
        }
        let final_row_strs: Vec<&str> = full_rows_data.iter().map(AsRef::as_ref).collect();
        board_from_str_array(&final_row_strs).expect("Failed to create board from minimal str array for test")
    }


    #[test]
    fn test_count_truly_isolated_tiles_none_isolated() {
        let board = board_from_minimal_str_array(&[
            "RR", // Group
            "GG", // Group
        ]);
        assert_eq!(count_truly_isolated_tiles(&board), 0);
    }

    #[test]
    fn test_count_truly_isolated_tiles_some_isolated() {
        let board = board_from_minimal_str_array(&[
            "R.B", // R, B are isolated
            "G.Y", // G, Y are isolated
            "PP", // PP is a group
        ]);
        assert_eq!(count_truly_isolated_tiles(&board), 4);
    }

    #[test]
    fn test_count_truly_isolated_tiles_all_isolated() {
        let board = board_from_minimal_str_array(&[
            "RGYB",
            "PYGM",
            "RBPY",
        ]); // Assuming no two adjacent are same color
        let expected_isolated = board.get_grid().iter().flatten().filter(|&&t| t != Tile::Empty).count();
        assert_eq!(count_truly_isolated_tiles(&board), expected_isolated as u32);
    }

    #[test]
    fn test_count_truly_isolated_tiles_empty_board() {
        let board = board_from_minimal_str_array(&[]); // All empty
        assert_eq!(count_truly_isolated_tiles(&board), 0);
    }

    #[test]
    fn test_calculate_heuristic_a_star_game_over() {
        let board = board_from_minimal_str_array(&["RGYB"]); // 4 tiles, all isolated
        let game = Game::new_with_board(board.clone());
        assert!(game.is_game_over());

        let expected_bonus = board.calculate_bonus();
        let num_isolated = count_truly_isolated_tiles(&board); // Should be 4
        assert_eq!(num_isolated, 4); // Verify assumption
        let expected_penalty = num_isolated * ISOLATED_TILE_PENALTY_FACTOR;

        let expected_h_score = if expected_bonus >= expected_penalty {
            expected_bonus - expected_penalty
        } else {
            0
        };
        assert_eq!(calculate_heuristic_a_star(&game), expected_h_score);
    }

    #[test]
    fn test_calculate_heuristic_a_star_with_penalty() {
        // Board with one group and one isolated tile
        // RR is a group. B is isolated.
        let board = board_from_minimal_str_array(&["RRB"]);
        let game = Game::new_with_board(board);

        let expected_h_score_without_penalty: u32 = {
            let mut temp_g = game.clone();
            let total_greedy_score = evaluate_with_heuristic(temp_g); // This is total score from state
            if total_greedy_score >= game.score() {
                total_greedy_score - game.score() // This is future score
            } else {
                0
            }
        };
        let num_isolated = count_truly_isolated_tiles(game.board()); // Should be 1 for B
        assert_eq!(num_isolated, 1, "Expected 1 isolated tile (B)");
        let expected_penalty = num_isolated * ISOLATED_TILE_PENALTY_FACTOR;

        let final_expected_h = if expected_h_score_without_penalty >= expected_penalty {
            expected_h_score_without_penalty - expected_penalty
        } else {
            0
        };

        assert_eq!(calculate_heuristic_a_star(&game), final_expected_h);
    }

    #[test]
    fn test_solve_a_star_already_game_over() {
        let board = board_from_minimal_str_array(&["RGYB"]); // No groups
        let game = Game::new_with_board(board.clone());
        assert!(game.is_game_over());

        let (solution_opt, nodes_explored) = solve_a_star(&game, 100); // Small iteration limit
        assert!(nodes_explored >= 1, "Should explore at least the initial node");
        assert!(solution_opt.is_some());
        let sol = solution_opt.unwrap();
        assert!(sol.moves.is_empty());
        assert_eq!(sol.score, game.final_score());
        assert_eq!(sol.steps_taken, 0);
    }

    #[test]
    fn test_solve_a_star_simple_one_move() {
        let board = board_from_minimal_str_array(&["RR"]);
        let game = Game::new_with_board(board);

        let (solution_opt, nodes_explored) = solve_a_star(&game, 1000);
        // println!("Simple one move A* nodes: {}", nodes_explored);
        assert!(solution_opt.is_some(), "Solution not found for simple one move board");
        let sol = solution_opt.unwrap();

        assert_eq!(sol.moves.len(), 1, "Expected one move");
        assert!(
            sol.moves[0] == (0, 0) || sol.moves[0] == (0, 1),
            "Expected move to be (0,0) or (0,1)"
        );

        let mut temp_game = game.clone();
        temp_game.process_move(sol.moves[0].0, sol.moves[0].1);
        assert_eq!(
            sol.score,
            temp_game.final_score(),
            "Score mismatch for one simple move. Expected 2020."
        );
        assert!(temp_game.is_game_over(), "Game should be over after the move");
    }

    #[test]
    fn test_solve_a_star_optimal_complex() {
        let board = board_from_minimal_str_array(&["RGYB....", "RGYB....", "BBGGRRYY"]);
        let game = Game::new_with_board(board);

        let (solution_opt, nodes_explored) = solve_a_star(&game, 20000);
        // println!("Optimal complex A* nodes: {}", nodes_explored);
        assert!(solution_opt.is_some(), "Solution not found for moderately complex board");
        let sol = solution_opt.unwrap();
        assert_eq!(
            sol.score, 2160,
            "Did not find optimal score for the complex board. Got {}",
            sol.score
        );
        assert_eq!(sol.steps_taken, 8, "Should take 8 steps to clear");

        let mut sim_game = game.clone();
        for &(r, c) in &sol.moves {
            assert!(
                sim_game.process_move(r, c),
                "A* suggested an invalid move sequence: ({},{}) on board:\n{}",
                r,
                c,
                sim_game.board()
            );
        }
        assert_eq!(
            sim_game.final_score(),
            sol.score,
            "A* solution moves do not lead to reported score"
        );
        assert!(sim_game.is_game_over(), "Game not over after A* solution moves");
    }

    #[test]
    fn test_solve_a_star_iteration_limit() {
        let board_over = board_from_minimal_str_array(&["RGYBM"]);
        let game_over = Game::new_with_board(board_over.clone());
        assert!(game_over.is_game_over());

        let (sol_opt_0, nodes_0) = solve_a_star(&game_over, 0);
        assert!(sol_opt_0.is_some());
        assert_eq!(sol_opt_0.unwrap().score, game_over.final_score());
        assert!(nodes_0 >= 1);


        let (sol_opt_1, nodes_1) = solve_a_star(&game_over, 1);
        assert!(sol_opt_1.is_some());
        assert_eq!(sol_opt_1.unwrap().score, game_over.final_score());
        assert_eq!(nodes_1, 1, "Expected 1 node for game over with limit 1");


        let board_needs_search = board_from_minimal_str_array(&["RRR", "GGG", "BBB"]);
        let game_needs_search = Game::new_with_board(board_needs_search);

        let (sol_low_iter_opt, nodes_low) = solve_a_star(&game_needs_search, 2);
        // println!("Low iter A* nodes: {}", nodes_low);
        assert!(sol_low_iter_opt.is_none(), "Expected None for very low iteration limit not reaching game over, but got a solution.");
        assert_eq!(nodes_low, 2, "Should stop after 2 iterations");


        let (sol_enough_iter_opt, nodes_enough) = solve_a_star(&game_needs_search, 1000);
        // println!("Enough iter A* nodes: {}", nodes_enough);
        assert!(sol_enough_iter_opt.is_some(), "Solution not found with presumed enough iterations");
        assert_eq!(sol_enough_iter_opt.unwrap().score, 2135, "Score mismatch for 3-group board");
    }

    #[test]
    fn test_solve_dfs_nodes_explored() {
        let board = board_from_minimal_str_array(&["RR"]);
        let game = Game::new_with_board(board);
        let depth_limit = 3; // Small depth limit

        let (_solution_opt, nodes_explored) = solve_dfs(&game, depth_limit);

        // Basic check: Ensure some nodes were explored.
        // The exact number can be tricky to assert if logic changes,
        // but it should be greater than 0 if the function is working.
        assert!(nodes_explored > 0, "Nodes explored should be greater than 0. Got {}", nodes_explored);

        // Deeper assertion:
        // For "RR" and depth 3:
        // 1. Initial call to find_best_solution_recursive (nodes_explored = 1)
        // 2. It finds one group "RR". Clicks it.
        // 3. Recursive call for the empty board (nodes_explored = 2)
        //    - This state is game over, returns.
        // So, expected nodes_explored is 2.
        assert_eq!(nodes_explored, 2, "For 'RR' and depth 3, expected 2 nodes explored. Got {}", nodes_explored);

        // Test with a board that has no moves
        let board_no_moves = board_from_minimal_str_array(&["R"]);
        let game_no_moves = Game::new_with_board(board_no_moves);
        let (_solution_opt_no_moves, nodes_explored_no_moves) = solve_dfs(&game_no_moves, depth_limit);
        // 1. Initial call. Game is over (no groups). Returns.
        assert_eq!(nodes_explored_no_moves, 1, "For 'R' (no moves) and depth 3, expected 1 node explored. Got {}", nodes_explored_no_moves);

        // Test with a board and depth limit 0
        let board_depth_zero = board_from_minimal_str_array(&["RR"]);
        let game_depth_zero = Game::new_with_board(board_depth_zero);
        let (_solution_opt_depth_zero, nodes_explored_depth_zero) = solve_dfs(&game_depth_zero, 0);
        // 1. Initial call. Depth is 0. Returns.
        assert_eq!(nodes_explored_depth_zero, 1, "For 'RR' and depth 0, expected 1 node explored. Got {}", nodes_explored_depth_zero);
    }
}
