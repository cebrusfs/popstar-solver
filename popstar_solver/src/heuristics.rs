use crate::engine::{Board, Game, Tile, BOARD_SIZE};
use std::collections::HashSet;

/// Calculates the number of unique tile colors currently present on the board.
///
/// Empty tiles are not counted as a color.
///
/// # Arguments
/// * `board`: A reference to the `Board` to analyze.
///
/// # Returns
/// The count of unique tile colors (e.g., Red, Green, Blue) as `usize`.
pub fn count_unique_colors(board: &Board) -> usize {
    let mut unique_tiles = HashSet::new();
    for r in 0..BOARD_SIZE {
        for c in 0..BOARD_SIZE {
            let tile = board.get_tile(r, c);
            if tile != Tile::Empty {
                unique_tiles.insert(tile); // HashSet ensures uniqueness
            }
        }
    }
    unique_tiles.len()
}

/// Counts the number of "truly isolated" tiles on the board.
///
/// A tile is considered truly isolated if it is not `Tile::Empty` and it cannot form a
/// group of 2 or more same-colored adjacent (horizontally or vertically) tiles.
/// This function iterates through all tiles, and for each unvisited non-empty tile,
/// it attempts to find a group. If no group (size < 2) is formed, the tile is counted
/// as isolated. If a group is formed, all tiles in that group are marked as visited
/// and are not counted as isolated.
///
/// # Arguments
/// * `board`: A reference to the `Board` to analyze.
///
/// # Returns
/// The total count of truly isolated tiles as `u32`.
pub fn count_truly_isolated_tiles(board: &Board) -> u32 {
    let mut isolated_count = 0;
    let mut visited = [[false; BOARD_SIZE]; BOARD_SIZE]; // To avoid processing tiles multiple times

    for r_idx in 0..BOARD_SIZE {
        for c_idx in 0..BOARD_SIZE {
            if !visited[r_idx][c_idx] && board.get_tile(r_idx, c_idx) != Tile::Empty {
                let group = board.find_group(r_idx, c_idx);
                if group.len() >= 2 {
                    // This tile is part of a group, mark all tiles in the group as visited.
                    for &(r, c) in &group {
                        visited[r][c] = true;
                    }
                } else {
                    // This tile is a singleton (group length is 1, or 0 if find_group had issues).
                    // Mark as visited and count as isolated.
                    visited[r_idx][c_idx] = true;
                    isolated_count += 1;
                }
            }
        }
    }

    isolated_count
}

/// Chooses a move based on the Maximize Immediate Score (MIS) strategy.
///
/// This strategy selects the group of tiles that, when eliminated, yields the highest
/// immediate score. The score for eliminating a group of `n` tiles is `n * n * 5`.
/// If multiple groups yield the same maximum score, the one with more tiles is preferred.
///
/// # Arguments
/// * `current_board`: A reference to the current `Board` state.
///
/// # Returns
/// An `Option` containing a tuple:
///   - `usize`: The score that would be obtained by eliminating the chosen group.
///   - `Vec<(usize, usize)>`: The coordinates of the tiles in the chosen group.
/// Returns `None` if no groups are available on the board.
pub fn choose_move_mis(current_board: &Board) -> Option<(usize, Vec<(usize, usize)>)> {
    let available_groups = current_board.find_all_groups();

    if available_groups.is_empty() {
        return None;
    }

    // Initialize with the first group's data
    let first_group = &available_groups[0];
    let mut max_score = first_group.len() * first_group.len() * 5;
    let mut best_group = first_group.clone();

    // Iterate starting from the second group
    for group in available_groups.iter().skip(1) {
        let score = group.len() * group.len() * 5;
        if score > max_score {
            max_score = score;
            best_group = group.clone();
        } else if score == max_score && group.len() > best_group.len() {
            // Tie-breaking: prefer larger group if scores are equal
            best_group = group.clone();
        }
    }
    Some((max_score, best_group))
}

/// Chooses a move based on the Largest Group Priority (LGP) strategy.
///
/// This strategy selects the group containing the largest number of tiles.
/// The actual score obtained is secondary to the size of the group.
/// If multiple groups have the same maximal size, the one encountered first (based on
/// `find_all_groups` iteration order) is chosen.
///
/// # Arguments
/// * `current_board`: A reference to the current `Board` state.
///
/// # Returns
/// An `Option` containing a tuple:
///   - `usize`: The number of tiles in the chosen group (its length).
///   - `Vec<(usize, usize)>`: The coordinates of the tiles in the chosen group.
/// Returns `None` if no groups are available on the board.
pub fn choose_move_lgp(current_board: &Board) -> Option<(usize, Vec<(usize, usize)>)> {
    let available_groups = current_board.find_all_groups();

    if available_groups.is_empty() {
        return None;
    }

    // Find the group with the maximum length.
    // The call to unwrap() is safe because we've checked that available_groups is not empty.
    let best_group = available_groups
        .iter()
        .max_by_key(|g| g.len())
        .unwrap()
        .clone();
    Some((best_group.len(), best_group))
}

/// Chooses a move based on the Color Reduction Priority (CRP) strategy.
///
/// This strategy simulates eliminating each available group and chooses the one that results
/// in the minimum number of unique colors remaining on the board.
/// If multiple groups lead to the same minimum number of resulting colors, the one
/// whose elimination also involves removing a larger group of tiles is preferred as a tie-breaker.
///
/// # Arguments
/// * `current_board`: A reference to the current `Board` state.
///
/// # Returns
/// An `Option` containing a tuple:
///   - `(usize, usize)`: A pair representing `(resulting_colors, group_size)` for the chosen move.
///     `resulting_colors` is the number of unique colors on the board *after* the chosen group is eliminated.
///     `group_size` is the number of tiles in the chosen group.
///   - `Vec<(usize, usize)>`: The coordinates of the tiles in the chosen group.
/// Returns `None` if no groups are available on the board.
pub fn choose_move_crp(current_board: &Board) -> Option<((usize, usize), Vec<(usize, usize)>)> {
    let available_groups = current_board.find_all_groups();

    if available_groups.is_empty() {
        return None;
    }

    // Initialize with the first group's simulated result
    let first_group = &available_groups[0];
    // PERFORMANCE: Cloning the board here for initialization.
    let mut initial_temp_board = current_board.clone();
    initial_temp_board.eliminate_group(first_group);
    initial_temp_board.apply_gravity();
    initial_temp_board.shift_columns();
    let mut min_resulting_colors = count_unique_colors(&initial_temp_board);
    let mut max_size_at_min_colors = first_group.len();
    let mut best_group_choice = first_group.clone();

    // Iterate starting from the second group
    for group_candidate in available_groups.iter().skip(1) {
        // PERFORMANCE: Cloning the board for each candidate group to simulate the move can be
        // computationally intensive, especially with a large number of available groups.
        let mut temp_board_sim = current_board.clone();
        temp_board_sim.eliminate_group(group_candidate);
        temp_board_sim.apply_gravity();
        temp_board_sim.shift_columns();

        let resulting_colors = count_unique_colors(&temp_board_sim);
        let current_candidate_size = group_candidate.len();

        if resulting_colors < min_resulting_colors {
            min_resulting_colors = resulting_colors;
            max_size_at_min_colors = current_candidate_size;
            best_group_choice = group_candidate.clone();
        } else if resulting_colors == min_resulting_colors {
            if current_candidate_size > max_size_at_min_colors {
                max_size_at_min_colors = current_candidate_size;
                best_group_choice = group_candidate.clone();
            }
        }
    }
    Some((
        (min_resulting_colors, max_size_at_min_colors),
        best_group_choice,
    ))
}

/// Chooses a move based on the Maximize Immediate Score & Penalize Singletons (MISPS) strategy.
///
/// This strategy calculates a heuristic value for eliminating each available group.
/// The heuristic value is `immediate_score - (number_of_resulting_singletons * penalty_factor)`.
///   - `immediate_score` is `n * n * 5` for eliminating `n` tiles.
///   - `number_of_resulting_singletons` is the count of truly isolated tiles after the group
///     is eliminated and the board settles.
///   - `penalty_factor` is a constant (`SINGLETON_PENALTY_FACTOR`).
/// The strategy chooses the group that maximizes this heuristic value.
/// If multiple groups yield the same maximum heuristic value, the one with more tiles is preferred.
///
/// # Arguments
/// * `current_board`: A reference to the current `Board` state.
///
/// # Returns
/// An `Option` containing a tuple:
///   - `i32`: The calculated heuristic value for the chosen move.
///   - `Vec<(usize, usize)>`: The coordinates of the tiles in the chosen group.
/// Returns `None` if no groups are available on the board.
pub fn choose_move_misps(current_board: &Board) -> Option<(i32, Vec<(usize, usize)>)> {
    let available_groups = current_board.find_all_groups();

    if available_groups.is_empty() {
        return None;
    }

    const SINGLETON_PENALTY_FACTOR: i32 = 50;

    // Initialize with the first group's simulated result
    let first_group = &available_groups[0];
    let first_immediate_score = (first_group.len() * first_group.len() * 5) as i32;
    // PERFORMANCE: Cloning the board here for initialization.
    let mut initial_temp_board = current_board.clone();
    initial_temp_board.eliminate_group(first_group);
    initial_temp_board.apply_gravity();
    initial_temp_board.shift_columns();
    let first_num_singletons = count_truly_isolated_tiles(&initial_temp_board);
    let mut max_heuristic_value =
        first_immediate_score - (first_num_singletons as i32 * SINGLETON_PENALTY_FACTOR);
    let mut max_group_size_at_max_heuristic = first_group.len();
    let mut best_group_choice = first_group.clone();

    // Iterate starting from the second group
    for group_candidate in available_groups.iter().skip(1) {
        let immediate_score = (group_candidate.len() * group_candidate.len() * 5) as i32;

        // PERFORMANCE: Cloning the board for each candidate group to simulate the move can be
        // computationally intensive, especially with a large number of available groups.
        let mut temp_board_sim = current_board.clone();
        temp_board_sim.eliminate_group(group_candidate);
        temp_board_sim.apply_gravity();
        temp_board_sim.shift_columns();

        let num_singletons = count_truly_isolated_tiles(&temp_board_sim);
        let heuristic_value = immediate_score - (num_singletons as i32 * SINGLETON_PENALTY_FACTOR);
        let current_candidate_size = group_candidate.len();

        if heuristic_value > max_heuristic_value {
            max_heuristic_value = heuristic_value;
            max_group_size_at_max_heuristic = current_candidate_size;
            best_group_choice = group_candidate.clone();
        } else if heuristic_value == max_heuristic_value {
            if current_candidate_size > max_group_size_at_max_heuristic {
                max_group_size_at_max_heuristic = current_candidate_size;
                best_group_choice = group_candidate.clone();
            }
        }
    }
    Some((max_heuristic_value, best_group_choice))
}

/// Evaluates a game state by playing it out until the end using a specified heuristic strategy.
///
/// This function takes a `Game` state and repeatedly chooses and processes moves
/// using the `choose_move_misps` heuristic until the game is over (no more moves can be made).
/// It's used by the DFS solver when the depth limit is reached to get an estimated score
/// for an incomplete game.
///
/// # Arguments
/// * `game_state`: The `Game` state to start evaluating from. This state will be modified
///   as moves are played.
///
/// # Returns
/// The final score (`u32`) achieved after playing the game to completion using the
/// `choose_move_misps` heuristic. This score includes any end-game bonus.
///
/// # Warnings
/// This function prints warnings to `eprintln!` if `choose_move_misps` returns an empty group
/// (which should not happen for a valid board with groups) or if `process_move` fails for a
/// chosen group (which also indicates an inconsistency).
pub fn evaluate_with_heuristic(mut game_state: Game) -> u32 {
    while !game_state.is_game_over() {
        // Use MISPS to choose the next move.
        if let Some((_heuristic_value, chosen_group)) = choose_move_misps(game_state.board()) {
            // Ensure the chosen group is not empty before trying to get click coordinates.
            // This check is a safeguard; choose_move_misps should return None if no valid groups exist.
            if chosen_group.is_empty() {
                // This case should ideally not happen if choose_move_misps only returns Some for non-empty groups,
                // or returns None if available_groups was empty.
                eprintln!(
                    "Warning: evaluate_with_heuristic detected choose_move_misps returned an empty group. Board:\n{}",
                    game_state.board()
                );
                break;
            }
            let (r_click, c_click) = chosen_group[0]; // Get coordinates from the first tile in the group.

            // Process the chosen move.
            if !game_state.process_move(r_click, c_click) {
                // This warning indicates a potential issue if a move chosen by the heuristic
                // cannot be processed by the game engine.
                eprintln!(
                    "Warning: evaluate_with_heuristic using MISPS chose group {:?} starting at ({},{}) but process_move failed. Board:\n{}",
                    chosen_group, r_click, c_click, game_state.board()
                );
                break; // Stop evaluation if a move fails.
            }
        } else {
            // No more moves available according to the heuristic, so the game simulation part ends.
            break;
        }
    }
    // Return the final score of the game state after all heuristic moves are made.
    game_state.final_score()
}
