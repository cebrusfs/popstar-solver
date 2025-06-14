use crate::engine::{Board, Game};
use std::collections::HashMap; // Changed from HashSet to HashMap

// Re-export the heuristic functions for backward compatibility
pub use crate::heuristics::evaluate_with_heuristic;

/// Represents a solution found by the solver.
///
/// A solution consists of a sequence of moves, the final score achieved,
/// and the number of steps (eliminations) taken.
#[derive(Clone, Debug)]
pub struct Solution {
    /// Sequence of (row, column) clicks representing the moves made to achieve this solution.
    /// Each tuple `(r, c)` is a click on the tile at row `r` and column `c`.
    pub moves: Vec<(usize, usize)>,
    /// The final score achieved after these moves. This score includes any end-game bonus
    /// if the game is over, or a heuristic evaluation if the search was cut off by depth limit.
    pub score: i32, // Changed to i32
    /// The number of moves (eliminations) performed by the solver to reach this solution.
    /// This corresponds to the `steps` count in the `Game` struct.
    pub steps_taken: u32,
}

/// Solves the PopStar game using a Depth-First Search (DFS) algorithm up to a specified depth limit.
///
/// The solver explores possible game states by trying out all available moves (eliminating groups).
/// It uses a `HashSet` to keep track of visited board states to avoid redundant computations and cycles.
/// If the `depth_limit` is reached before the game is over, `evaluate_with_heuristic` (from the
/// `heuristics` module, specifically MISPS) is used to estimate the score from that point.
///
/// # Arguments
/// * `initial_game`: A reference to the initial `Game` state from which to start the search.
/// * `depth_limit`: The maximum number of moves (eliminations) the solver will explore down a single path.
///   A `depth_limit` of 0 means only the initial state will be evaluated (or its heuristic score if not game over).
///
/// # Returns
/// A tuple containing:
///   - `Option<Solution>`: The best solution found within the depth limit. `None` if no solution
///     could be found (e.g., if the initial game state itself is problematic, though typically
///     it will at least return a solution representing the initial state evaluated).
///   - `u32`: The total number of game states (nodes) explored during the DFS search.
///
/// # Behavior at Depth Limit
/// When `depth_remaining` in the recursive search reaches 0, the game state at that point is
/// evaluated using `evaluate_with_heuristic`. This provides an estimated score for paths that
/// are cut off by the depth limit, allowing the DFS to still make decisions based on these
/// potentially incomplete game plays.
pub fn solve_dfs(initial_game: &Game, depth_limit: u32) -> (Option<Solution>, u32) {
    let mut visited_states = HashMap::new(); // Changed from HashSet to HashMap
                                             // Insert the initial state with its current score.
                                             // The score for the initial state is initial_game.score() (usually 0).
    visited_states.insert(initial_game.board().clone(), initial_game.score());

    let mut nodes_explored_dfs: u32 = 0;
    let mut game_instance = initial_game.clone();
    let mut moves_path = Vec::new();
    let solution_opt = find_best_solution_recursive(
        &mut game_instance,
        depth_limit,
        &mut visited_states,
        &mut moves_path,
        &mut nodes_explored_dfs,
    );
    (solution_opt, nodes_explored_dfs)
}

/// Recursive helper function for the Depth-First Search (DFS) solver.
///
/// This function explores game states by trying all possible moves from the `current_game_state`.
///
/// # Arguments
/// * `current_game_state`: The current `Game` state being evaluated.
/// * `depth_remaining`: How many more moves (depth) can be explored from this state.
/// * `visited_states`: A mutable reference to a `HashMap` storing `Board` configurations as keys
///   and the maximum score achieved to reach that board state as values.
/// * `current_moves_path`: A `Vec` accumulating the sequence of moves taken to reach the
///   `current_game_state`.
/// * `nodes_explored`: A mutable reference to a counter for the total number of states explored.
///
/// # Returns
/// An `Option<Solution>` representing the best solution found from this state down to the
/// allowed `depth_remaining`. Returns `None` if no valid solution path is found (though typically
/// a solution representing the current state evaluated will be returned).
///
fn find_best_solution_recursive(
    current_game_state: &mut Game,
    depth_remaining: u32,
    visited_states: &mut HashMap<Board, u32>, // Changed type from HashSet<Board>
    current_moves_path: &mut Vec<(usize, usize)>,
    nodes_explored: &mut u32,
) -> Option<Solution> {
    *nodes_explored += 1;

    // Base case: Game is over (no more moves possible).
    if current_game_state.is_game_over() {
        return Some(Solution {
            moves: current_moves_path.clone(),
            score: current_game_state.final_score(),
            steps_taken: current_game_state.steps(),
        });
    }

    // Base case: Depth limit reached.
    // Evaluate the current board using a heuristic if the game is not over.
    if depth_remaining == 0 {
        let steps = current_game_state.steps();
        // The evaluate_with_heuristic function plays out the game from current_game_state
        // using the MISPS heuristic and returns the final score achieved.
        let heuristic_score = evaluate_with_heuristic(current_game_state.clone()); // Clone for owned Game
        return Some(Solution {
            moves: current_moves_path.clone(),
            score: heuristic_score,
            steps_taken: steps,
        });
    }

    let mut best_solution_found: Option<Solution> = None;

    let available_groups = current_game_state.board().find_all_groups();

    // This handles the case where find_all_groups is empty.
    // This is effectively another game-over condition: if no groups can be formed,
    // the game cannot proceed from this state via elimination.
    // This check is similar to current_game_state.is_game_over() but done after the depth check.
    if available_groups.is_empty() {
        return Some(Solution {
            moves: current_moves_path.clone(),
            score: current_game_state.final_score(),
            steps_taken: current_game_state.steps(),
        });
    }

    for group in available_groups {
        assert!(!group.is_empty());
        let (r_click, c_click) = group[0];

        // Apply the move to current_game_state (S -> S')
        let move_was_valid = current_game_state.process_move(r_click, c_click);

        assert!(
            move_was_valid,
            "A group identified by find_all_groups should always be a valid move."
        );

        // Clone the board state *after* the move for checks and visited set.
        let board_after_move = current_game_state.board().clone();
        let current_score_at_board = current_game_state.score();

        // Determine if we should recurse or prune this path.
        match visited_states.get(&board_after_move) {
            Some(&previous_max_score) => {
                if current_score_at_board <= previous_max_score {
                    // This path is worse or equal to a previously found path to the same state, prune it.
                    current_game_state.undo_last_move();
                    continue; // Skip to the next group for this iteration
                }
                // If score is better, update visited_states and proceed to recursion.
                visited_states.insert(board_after_move.clone(), current_score_at_board);
            }
            None => {
                // This board state has not been visited before. Insert and proceed to recursion.
                visited_states.insert(board_after_move.clone(), current_score_at_board);
            }
        }

        // If we haven't 'continued', then this path is worth exploring.
        current_moves_path.push((r_click, c_click));

        // Make the recursive call
        if let Some(solution_from_this_path) = find_best_solution_recursive(
            current_game_state, // Pass mutable S'
            depth_remaining - 1,
            visited_states,
            current_moves_path,
            nodes_explored,
        ) {
            // Update best_solution_found if this path is better
            if best_solution_found.is_none()
                || solution_from_this_path.score > best_solution_found.as_ref().unwrap().score
            {
                best_solution_found = Some(solution_from_this_path);
            }
        }
        // Backtrack: remove the last move from path for the next iteration
        current_moves_path.pop();

        // Crucially, always undo the move at the end of the loop iteration
        // as we are returning from the recursive call for this specific move.
        current_game_state.undo_last_move();
    }
    // Note on visited_states:
    // The current implementation of `visited_states` (now a HashMap) is passed down and accumulates.
    // It stores the max score found so far to reach a given board state.
    // Paths leading to a known board state are only explored if they do so with a higher score.
    // REMOVED EXTRA BRACE HERE

    // Fallback: If no moves were explored (e.g., all led to already visited states with lower/equal scores,
    // or `available_groups` was initially empty and not caught by `is_game_over`),
    // then the "solution" from this point is the current state evaluated as is.
    // This is crucial if `best_solution_found` remains `None` after the loop.
    if best_solution_found.is_none() {
        // This can happen if all moves lead to states already in `visited_states` or if `available_groups` was empty
        // (which should ideally be caught by `is_game_over` or `available_groups.is_empty()` checks earlier).
        return Some(Solution {
            moves: current_moves_path.clone(),
            score: current_game_state.final_score(),
            steps_taken: current_game_state.steps(),
        });
    }

    best_solution_found
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::{Game, Tile};
    use crate::heuristics::count_truly_isolated_tiles; // Corrected path // BOARD_SIZE removed
                                                       // Removed local board_from_str_array and board_from_minimal_str_array

    #[test]
    fn test_count_truly_isolated_tiles_none_isolated() {
        let board = crate::utils::board_from_str_array(&[
            "RR", // Group
            "GG", // Group
        ])
        .unwrap();
        assert_eq!(count_truly_isolated_tiles(&board), 0);
    }

    #[test]
    fn test_count_truly_isolated_tiles_some_isolated() {
        let board = crate::utils::board_from_str_array(&[
            "R.B", // R, B are isolated
            "G.Y", // G, Y are isolated
            "PP",  // PP is a group
        ])
        .unwrap();
        assert_eq!(count_truly_isolated_tiles(&board), 4);
    }

    #[test]
    fn test_count_truly_isolated_tiles_all_isolated() {
        let board = crate::utils::board_from_str_array(&[
            "RGYB", "PYG.", // Changed 'M' to '.'
            "RBPY",
        ])
        .unwrap(); // Assuming no two adjacent are same color
        let expected_isolated = board
            .get_grid()
            .iter()
            .flatten()
            .filter(|&&t| t != Tile::Empty)
            .count();
        assert_eq!(count_truly_isolated_tiles(&board), expected_isolated as u32);
    }

    #[test]
    fn test_count_truly_isolated_tiles_empty_board() {
        let board = crate::utils::board_from_str_array(&[]).unwrap(); // All empty
        assert_eq!(count_truly_isolated_tiles(&board), 0);
    }

    #[test]
    fn test_solve_dfs_nodes_explored() {
        let board = crate::utils::board_from_str_array(&["RR"]).unwrap();
        let game = Game::new_with_board(board);
        let depth_limit = 3; // Small depth limit

        let (_solution_opt, nodes_explored) = solve_dfs(&game, depth_limit);

        // Basic check: Ensure some nodes were explored.
        // The exact number can be tricky to assert if logic changes,
        // but it should be greater than 0 if the function is working.
        assert!(
            nodes_explored > 0,
            "Nodes explored should be greater than 0. Got {}",
            nodes_explored
        );

        // Deeper assertion:
        // For "RR" and depth 3:
        // 1. Initial call to find_best_solution_recursive (nodes_explored = 1)
        // 2. It finds one group "RR". Clicks it.
        // 3. Recursive call for the empty board (nodes_explored = 2)
        //    - This state is game over, returns.
        // So, expected nodes_explored is 2.
        assert_eq!(
            nodes_explored, 2,
            "For 'RR' and depth 3, expected 2 nodes explored. Got {}",
            nodes_explored
        );

        // Test with a board that has no moves
        let board_no_moves = crate::utils::board_from_str_array(&["R"]).unwrap();
        let game_no_moves = Game::new_with_board(board_no_moves);
        let (_solution_opt_no_moves, nodes_explored_no_moves) =
            solve_dfs(&game_no_moves, depth_limit);
        // 1. Initial call. Game is over (no groups). Returns.
        assert_eq!(
            nodes_explored_no_moves, 1,
            "For 'R' (no moves) and depth 3, expected 1 node explored. Got {}",
            nodes_explored_no_moves
        );

        // Test with a board and depth limit 0
        let board_depth_zero = crate::utils::board_from_str_array(&["RR"]).unwrap();
        let game_depth_zero = Game::new_with_board(board_depth_zero);
        let (_solution_opt_depth_zero, nodes_explored_depth_zero) = solve_dfs(&game_depth_zero, 0);
        // 1. Initial call. Depth is 0. Returns.
        assert_eq!(
            nodes_explored_depth_zero, 1,
            "For 'RR' and depth 0, expected 1 node explored. Got {}",
            nodes_explored_depth_zero
        );
    }

    #[test]
    fn test_solve_dfs_simple_one_move_max() {
        // Create a simple board that is not immediately game-over, to ensure
        // evaluate_with_heuristic has something to work on.
        let board_str = [
            "RRR......", // A group of 3 Red
            "G.G......", // Two non-adjacent Green
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
        ];
        let board = crate::utils::board_from_str_array(&board_str).unwrap();
        let initial_game = Game::new_with_board(board);
        let depth_limit = 0;

        // Expected score when depth_limit is 0 is the heuristic evaluation of the initial state.
        let expected_score = evaluate_with_heuristic(initial_game.clone());

        let (solution_opt, nodes_explored) = solve_dfs(&initial_game, depth_limit);

        assert!(solution_opt.is_some(), "Solution should be Some");
        let solution = solution_opt.unwrap();

        assert_eq!(
            solution.score, expected_score,
            "Score at depth 0 should be the heuristic evaluation of the initial state"
        );
        assert!(
            solution.moves.is_empty(),
            "Moves should be empty for depth 0 search from initial state"
        );
        assert_eq!(
            solution.steps_taken,
            initial_game.steps(), // Should be 0 for a fresh game
            "Steps taken should be initial game steps (0) for depth 0 search"
        );
        assert_eq!(
            nodes_explored, 1,
            "Nodes explored should be 1 for depth 0 search"
        );
    }
}
