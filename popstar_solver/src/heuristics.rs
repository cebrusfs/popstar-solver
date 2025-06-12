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
///   - `(usize, usize)`: The coordinate of a representative tile (e.g., the first tile) from the chosen group, used as the click point.
/// Returns `None` if no groups are available on the board.
// TODO: Consider aligning all choose_move_* functions to a common return signature like `(actual_score_of_move, Option<(usize,usize)>)` as per Issue Comment #2.
pub fn choose_move_mis(current_board: &Board) -> Option<(usize, (usize, usize))> {
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
    Some((max_score, best_group[0]))
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
///   - `(usize, usize)`: The coordinate of a representative tile from the chosen group.
/// Returns `None` if no groups are available on the board.
pub fn choose_move_lgp(current_board: &Board) -> Option<(usize, (usize, usize))> {
    let available_groups = current_board.find_all_groups();

    if available_groups.is_empty() {
        return None;
    }

    // Find the group with the maximum length.
    // The call to unwrap() is safe because we've checked that available_groups is not empty.
    let best_group = available_groups.iter().max_by_key(|g| g.len()).unwrap(); // .clone() is not needed if we only take one tile coord
    Some((best_group.len(), best_group[0]))
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
///   - `(usize, usize)`: The coordinate of a representative tile from the chosen group.
/// Returns `None` if no groups are available on the board.
pub fn choose_move_crp(current_board: &Board) -> Option<((usize, usize), (usize, usize))> {
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
        } else if resulting_colors == min_resulting_colors && current_candidate_size > max_size_at_min_colors {
            max_size_at_min_colors = current_candidate_size;
            best_group_choice = group_candidate.clone();
        }
    }
    Some((
        (min_resulting_colors, max_size_at_min_colors),
        best_group_choice[0],
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
///   - `(usize, usize)`: The coordinate of a representative tile from the chosen group.
/// Returns `None` if no groups are available on the board.
pub fn choose_move_misps(current_board: &Board) -> Option<(i32, (usize, usize))> {
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
        } else if heuristic_value == max_heuristic_value && current_candidate_size > max_group_size_at_max_heuristic {
            max_group_size_at_max_heuristic = current_candidate_size;
            best_group_choice = group_candidate.clone();
        }
    }
    Some((max_heuristic_value, best_group_choice[0]))
}

/// Evaluates a game state by playing it out until the end using a specified heuristic strategy.
///
/// This function takes a `Game` state and repeatedly chooses and processes moves
/// using the `choose_move_misps` heuristic until the game is over (no more moves can be made).
/// It's used by the DFS solver when the depth limit is reached to get an estimated score
/// for an incomplete game. The score returned by this function is based on a greedy playout
/// using the MISPS heuristic. As such, it typically represents a **lower bound** estimate
/// compared to the true optimal score achievable from the given game state if played perfectly.
/// It is not an upper bound on the optimal score.
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
        if let Some((_heuristic_value, chosen_group_coord)) = choose_move_misps(game_state.board()) {
            // Ensure the chosen group is not empty before trying to get click coordinates.
            // This check is a safeguard; choose_move_misps should return None if no valid groups exist.
            // Since choose_move_misps now returns a single coordinate, chosen_group_coord is (r_click, c_click)
            // The chosen_group (full list of coords) is not returned by choose_move_misps anymore.
            // The process_move function in Game engine uses a single (r,c) to identify a group.
            let (r_click, c_click) = chosen_group_coord;

            // Process the chosen move.
            if !game_state.process_move(r_click, c_click) {
                // This warning indicates a potential issue if a move chosen by the heuristic
                // cannot be processed by the game engine.
                eprintln!(
                    "Warning: evaluate_with_heuristic using MISPS chose click ({},{}) but process_move failed. Board:\n{}",
                    r_click, c_click, game_state.board()
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

/// Calculates an admissible heuristic for a given board state.
///
/// An admissible heuristic must never underestimate the true cost (or in this case, score)
/// to reach the goal from the current state. This heuristic calculates an optimistic
/// upper bound on the score achievable from the current board configuration.
///
/// The calculation is as follows:
/// 1. For each distinct tile color `C` on the board, count the total number of tiles `k_C`.
/// 2. For each color, calculate a potential score as if all tiles of that color could be
///    cleared in a single group: `k_C * k_C * 5`.
/// 3. Sum these potential scores for all colors.
/// 4. Add the maximum possible end-game bonus (2000 points for clearing the board).
///
/// This heuristic is an upper bound because:
/// - It assumes all tiles of a single color can form one large group, which is the
///   most optimistic scoring scenario for those tiles.
/// - It includes the maximum possible end-game bonus, regardless of whether the board
///   can actually be cleared.
///
/// # Arguments
/// * `board`: A reference to the `Board` to evaluate.
///
/// # Returns
/// An `u32` representing the calculated admissible heuristic score.
pub fn calculate_admissible_heuristic(board: &Board) -> u32 {
    let mut color_counts = std::collections::HashMap::new();

    for r in 0..BOARD_SIZE {
        for c in 0..BOARD_SIZE {
            let tile = board.get_tile(r, c);
            if tile != Tile::Empty {
                *color_counts.entry(tile).or_insert(0u32) += 1;
            }
        }
    }

    let mut heuristic_score = 0;
    for count in color_counts.values() {
        heuristic_score += count * count * 5;
    }

    // Add the maximum possible end-game bonus
    heuristic_score += 2000;

    heuristic_score
}

#[cfg(test)]
mod tests {
    use super::*;
    // BOARD_SIZE is already in scope via super::*
    // Board and Tile are not directly used, board_from_str_array handles Tile parsing.
    use crate::utils::board_from_str_array;

    #[test]
    fn test_admissible_heuristic_calculation() {
        // Test case 1: Empty board
        // Expect: 0 (for tiles) + 2000 (bonus) = 2000
        let empty_board_arr: [&str; 0] = [];
        let board_empty = board_from_str_array(&empty_board_arr).unwrap();
        assert_eq!(
            calculate_admissible_heuristic(&board_empty),
            2000,
            "Empty board heuristic"
        );

        // Test case 2: Board with a few tiles of mixed colors (no groups)
        // R: 1, G: 1, B: 1, Y: 1
        // Score: (1*1*5 for R) + (1*1*5 for G) + (1*1*5 for B) + (1*1*5 for Y) + 2000
        // Score: 5 + 5 + 5 + 5 + 2000 = 2020
        let board_mixed_no_groups = board_from_str_array(&[
            "R B", //
            "Y G", //
        ])
        .unwrap();
        assert_eq!(
            calculate_admissible_heuristic(&board_mixed_no_groups),
            5 * 4 + 2000,
            "Mixed colors, no groups"
        );

        // Test case 3: Board with some potential groups
        // R: 3, G: 1, B: 2
        // Score: (3*3*5 for R) + (1*1*5 for G) + (2*2*5 for B) + 2000
        // Score: (9*5) + (1*5) + (4*5) + 2000
        // Score: 45 + 5 + 20 + 2000 = 2070
        let board_potential_groups = board_from_str_array(&[
            "R R R G", // R=3, G=1
            "B B . .", // B=2
        ])
        .unwrap();
        assert_eq!(
            calculate_admissible_heuristic(&board_potential_groups),
            (3 * 3 * 5) + 5 + (2 * 2 * 5) + 2000,
            "Potential groups"
        );

        // Test case 4: Board full of one color (e.g., all Red on a 2x2 part of board for simplicity)
        // Assuming a 2x2 board area for this test, filled with Red. R: 4
        // Score: (4*4*5 for R) + 2000
        // Score: (16*5) + 2000 = 80 + 2000 = 2080
        // Note: board_from_str_array creates a board of BOARD_SIZE, filling unspecified with Empty.
        // If BOARD_SIZE is 10, then a 2x2 "RR", "RR" input means 4 Red tiles, 96 Empty.
        // Let's use a small example that board_from_str_array can handle well.
        let board_all_red_small = board_from_str_array(&[
            "R R", // R=2
            "R R", // R=2 -> total R=4
        ])
        .unwrap();
        assert_eq!(
            calculate_admissible_heuristic(&board_all_red_small),
            (4 * 4 * 5) + 2000,
            "All Red (4 tiles)"
        );

        // Test with a larger number of one color, spanning more of a default 10x10 board
        // Let's say 25 Red tiles.
        // Score: (25*25*5 for R) + 2000
        // Score: (625*5) + 2000 = 3125 + 2000 = 5125
        let red_tiles_rows = vec!["R R R R R"; 5]; // 5 rows, each with 5 Red tiles
        // This creates a 5x5 block of Red tiles. Total 25 Red tiles.
        let board_many_red =
            board_from_str_array(&red_tiles_rows) // Pass slice directly
                .unwrap();
        assert_eq!(
            calculate_admissible_heuristic(&board_many_red),
            (25 * 25 * 5) + 2000,
            "Many Red tiles (25 tiles)"
        );

        // Test with mixed colors, including some empty tiles from parsing
        let board_mixed_with_empty = board_from_str_array(&[
            "R . B", // R=1, B=1
            ". G .", // G=1
            "Y . P", // Y=1, P=1
        ])
        .unwrap();
        // R=1, B=1, G=1, Y=1, P=1. Each 1*1*5 = 5. Total 5*5 = 25.
        // Score = 25 + 2000 = 2025
        assert_eq!(
            calculate_admissible_heuristic(&board_mixed_with_empty),
            5 * 5 + 2000,
            "Mixed with empty"
        );
    }
}
