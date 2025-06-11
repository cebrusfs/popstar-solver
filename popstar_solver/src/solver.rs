use crate::engine::{Game, Board};
use std::collections::HashSet;

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
pub fn solve_dfs(initial_game: &Game, depth_limit: u32) -> Option<Solution> {
    let mut visited_states = HashSet::new();
    visited_states.insert(initial_game.board().clone());
    find_best_solution_recursive(
        initial_game.clone(),
        depth_limit,
        &mut visited_states,
        Vec::new(),
    )
}

fn find_best_solution_recursive(
    current_game_state: Game,
    depth_remaining: u32,
    visited_states: &mut HashSet<Board>,
    current_moves_path: Vec<(usize, usize)>,
) -> Option<Solution> {

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
    use crate::engine::Tile;

    #[test]
    fn test_solve_dfs_game_already_over() {
        let board = board_from_str_array(&[
            "RBY.......", // No groups
            "GPR.......",
            "RBY.......", // No groups
            "GPR.......",
            "YBG.......",
        ]).unwrap(); // Use .unwrap() for tests, or handle error
        let game = Game::new_with_board(board.clone());
        assert!(game.is_game_over());

        let solution = solve_dfs(&game, 5);
        assert!(solution.is_some());
        let sol = solution.unwrap();
        assert!(sol.moves.is_empty());
        assert_eq!(sol.score, game.final_score());
        assert_eq!(sol.steps_taken, 0);
    }

    #[test]
    fn test_solve_dfs_depth_zero() {
        let board = board_from_str_array(&[
            "RR.......", // Red group
            "GG.......", // Green group
        ]).unwrap();
        let game = Game::new_with_board(board.clone());

        let solution = solve_dfs(&game, 0);
        assert!(solution.is_some());
        let sol = solution.unwrap();
        assert!(sol.moves.is_empty(), "Moves should be empty at depth 0");
        assert_eq!(sol.score, game.final_score());
        assert_eq!(sol.steps_taken, 0);
    }

    #[test]
    fn test_solve_dfs_simple_one_move_max() {
        // TODO: fix the tests by considering the heuristic function involved, should we change the test way?
        let board = board_from_str_array(&[
            "G.........",
            "RR........",
            "BBB.......",
        ]).unwrap();
        let game = Game::new_with_board(board);

        let solution = solve_dfs(&game, 1);
        assert!(solution.is_some());
        let sol = solution.unwrap();

        assert_eq!(sol.moves.len(), 1, "Expected one move at depth 1");
        assert_eq!(sol.moves[0], (2,0), "Expected move should be (2,0) for BBB group");

        let mut temp_game = game.clone();
        temp_game.process_move(2,0);
        assert_eq!(sol.score, temp_game.final_score());
    }

    #[test]
    fn test_solve_dfs_forced_sequence() {
        let board = board_from_str_array(&[
            "RR........",
            "..........", // Empty row
            "GG........",
        ]).unwrap();
        let game = Game::new_with_board(board);

        let solution = solve_dfs(&game, 2);
        assert!(solution.is_some());
        let sol = solution.unwrap();

        assert_eq!(sol.moves.len(), 2, "Expected two moves");
        assert_eq!(sol.moves[0], (0,0), "First move should be (0,0) for RR");

        let mut sim_game = game.clone();
        sim_game.process_move(sol.moves[0].0, sol.moves[0].1);
        let green_groups = sim_game.board().find_all_groups().into_iter().find(|g| sim_game.board().get_tile(g[0].0, g[0].1) == Tile::Green);
        assert!(green_groups.is_some(), "Green group should exist after first move");
        let (g_r, g_c) = green_groups.unwrap()[0];
        assert_eq!(sol.moves[1], (g_r, g_c), "Second move did not target the green group correctly");

        sim_game.process_move(sol.moves[1].0, sol.moves[1].1);
        assert_eq!(sol.score, sim_game.final_score(), "Final score of sequence mismatch");
        assert!(sim_game.is_game_over(), "Game should be over after the two moves");
    }

    #[test]
    fn test_solve_dfs_visited_states_pruning() {
        let board = board_from_str_array(&[
            "RRG.......",
            "RRG.......",
            "..G.......",
        ]).unwrap();
        let game = Game::new_with_board(board);

        let solution = solve_dfs(&game, 3); // Depth 3: (click R), (click G)
        assert!(solution.is_some());
        let sol = solution.unwrap();
        assert_eq!(sol.moves.len(), 2);

        let mut sim_game = game.clone();
        sim_game.process_move(sol.moves[0].0, sol.moves[0].1);
        sim_game.process_move(sol.moves[1].0, sol.moves[1].1);
        assert_eq!(sol.score, sim_game.final_score());
        assert!(sim_game.is_game_over());
    }
}
