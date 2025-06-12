use crate::engine::{Board, Game};
use std::collections::HashSet;

// Re-export the heuristic functions for backward compatibility
pub use crate::heuristics::{
    evaluate_with_heuristic
};

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::{Board, Game, Tile, BOARD_SIZE};
    use crate::count_truly_isolated_tiles;
    
    // Helper function to create a board from a minimal string array
    fn board_from_str_array(rows: &[&str]) -> Board {
        use crate::engine::Tile::*;
        
        let mut grid = [[Tile::Empty; BOARD_SIZE]; BOARD_SIZE];
        
        for (r, &row) in rows.iter().enumerate() {
            if r >= BOARD_SIZE { break; }
            
            for (c, ch) in row.chars().enumerate() {
                if c >= BOARD_SIZE { break; }
                
                let tile = match ch.to_ascii_uppercase() {
                    'R' => Red,
                    'G' => Green,
                    'B' => Blue,
                    'Y' => Yellow,
                    'P' => Purple,
                    _ => Empty,
                };
                grid[r][c] = tile;
            }
        }
        
        Board::from_grid(grid)
    }

    // Helper function for test board creation
    fn board_from_minimal_str_array(test_rows: &[&str]) -> Board {
        board_from_str_array(test_rows)
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
