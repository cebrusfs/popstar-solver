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
                unique_tiles.insert(tile);
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
    let mut visited = [[false; BOARD_SIZE]; BOARD_SIZE];

    for r_idx in 0..BOARD_SIZE {
        for c_idx in 0..BOARD_SIZE {
            if !visited[r_idx][c_idx] && board.get_tile(r_idx, c_idx) != Tile::Empty {
                let group = board.find_group(r_idx, c_idx);
                if group.len() >= 2 {
                    for &(r, c) in &group {
                        visited[r][c] = true;
                    }
                } else {
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
///   - `f64`: The score that would be obtained by eliminating the chosen group.
///   - `(usize, usize)`: The coordinate of a representative tile (e.g., the first tile) from the chosen group, used as the click point.
/// Returns `None` if no groups are available on the board.
// TODO: Consider aligning all choose_move_* functions to a common return signature like `(actual_score_of_move, Option<(usize,usize)>)` as per Issue Comment #2.
pub fn choose_move_mis(current_board: &Board) -> Option<(f64, (usize, usize))> {
    let available_groups = current_board.find_all_groups();

    if available_groups.is_empty() {
        return None;
    }

    let first_group = &available_groups[0];
    let mut max_score = first_group.len() * first_group.len() * 5;
    let mut best_group = first_group.clone();

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
    Some((max_score as f64, best_group[0]))
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
///   - `f64`: The number of tiles in the chosen group (its length).
///   - `(usize, usize)`: The coordinate of a representative tile from the chosen group.
/// Returns `None` if no groups are available on the board.
pub fn choose_move_lgp(current_board: &Board) -> Option<(f64, (usize, usize))> {
    let available_groups = current_board.find_all_groups();

    if available_groups.is_empty() {
        return None;
    }

    // The call to unwrap() is safe because we've checked that available_groups is not empty.
    let best_group = available_groups.iter().max_by_key(|g| g.len()).unwrap();
    Some((best_group.len() as f64, best_group[0]))
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
///   - `f64`: The number of unique colors on the board *after* the chosen group is eliminated.
///   - `(usize, usize)`: The coordinate of a representative tile from the chosen group.
/// Returns `None` if no groups are available on the board.
pub fn choose_move_crp(current_board: &Board) -> Option<(f64, (usize, usize))> {
    let available_groups = current_board.find_all_groups();

    if available_groups.is_empty() {
        return None;
    }

    let first_group = &available_groups[0];
    // PERFORMANCE: Cloning the board here for initialization.
    let mut initial_temp_board = current_board.clone();
    initial_temp_board.eliminate_group(first_group);
    initial_temp_board.apply_gravity();
    initial_temp_board.shift_columns();
    let mut min_resulting_colors = count_unique_colors(&initial_temp_board);
    let mut max_size_at_min_colors = first_group.len();
    let mut best_group_choice = first_group.clone();

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
        } else if resulting_colors == min_resulting_colors
            && current_candidate_size > max_size_at_min_colors
        {
            max_size_at_min_colors = current_candidate_size;
            best_group_choice = group_candidate.clone();
        }
    }
    Some((min_resulting_colors as f64, best_group_choice[0]))
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
///   - `f64`: The calculated heuristic value for the chosen move.
///   - `(usize, usize)`: The coordinate of a representative tile from the chosen group.
/// Returns `None` if no groups are available on the board.
pub fn choose_move_misps(current_board: &Board) -> Option<(f64, (usize, usize))> {
    let available_groups = current_board.find_all_groups();

    if available_groups.is_empty() {
        return None;
    }

    const SINGLETON_PENALTY_FACTOR: i32 = 75; // Increased from 50 to 75

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
        } else if heuristic_value == max_heuristic_value
            && current_candidate_size > max_group_size_at_max_heuristic
        {
            max_group_size_at_max_heuristic = current_candidate_size;
            best_group_choice = group_candidate.clone();
        }
    }
    Some((max_heuristic_value as f64, best_group_choice[0]))
}

/// Chooses a move based on MISPS, with ClearFocus as a tie-breaker.
///
/// 1. Calculates MISPS value for all available groups.
/// 2. Finds the maximum MISPS value.
/// 3. Filters for candidate groups whose MISPS value is within a threshold (e.g., 90%)
///    of the maximum MISPS value (if max is positive), or equal to max MISPS if max is non-positive.
/// 4. Among these candidates, applies ClearFocus logic:
///    - Simulates eliminating each candidate group.
///    - Counts total remaining tiles on the resulting board.
///    - Chooses the move leading to the minimum remaining tiles.
///    - Tie-breaks further by the size of the original group eliminated (larger is better).
/// The returned f64 is the actual MISPS score of the chosen group.
pub fn choose_move_misps_clear_tiebreak(
    current_board: &Board,
) -> Option<(f64, (usize, usize))> {
    let available_groups = current_board.find_all_groups();

    if available_groups.is_empty() {
        return None;
    }

    const SINGLETON_PENALTY_FACTOR: i32 = 75; // Same as in MISPS
    let mut misps_scored_groups: Vec<(Vec<(usize, usize)>, i32)> = Vec::new();

    // 1. Calculate MISPS value for all groups
    for group_candidate_ref in &available_groups {
        let group_candidate = group_candidate_ref.clone();
        let immediate_score = (group_candidate.len() * group_candidate.len() * 5) as i32;

        let mut temp_board_sim = current_board.clone();
        temp_board_sim.eliminate_group(&group_candidate);
        temp_board_sim.apply_gravity();
        temp_board_sim.shift_columns();
        let num_singletons = count_truly_isolated_tiles(&temp_board_sim);
        let misps_value = immediate_score - (num_singletons as i32 * SINGLETON_PENALTY_FACTOR);
        misps_scored_groups.push((group_candidate, misps_value));
    }

    if misps_scored_groups.is_empty() {
        return None;
    }

    // 2. Find max_misps_value
    let max_misps_value = misps_scored_groups.iter().map(|(_, val)| *val).max().unwrap_or(i32::MIN);

    // 3. Modify candidate selection using threshold
    const THRESHOLD_RATIO: f64 = 0.90;
    let candidates_for_tiebreak: Vec<(Vec<(usize, usize)>, i32)>;

    if max_misps_value > 0 {
        let misps_threshold = (max_misps_value as f64 * THRESHOLD_RATIO) as i32;
        candidates_for_tiebreak = misps_scored_groups
            .into_iter() // Consumes misps_scored_groups
            .filter(|(_, val)| *val >= misps_threshold)
            .collect();
    } else {
        candidates_for_tiebreak = misps_scored_groups
            .into_iter() // Consumes misps_scored_groups
            .filter(|(_, val)| *val == max_misps_value)
            .collect();
    }

    // Fallback: If thresholding resulted in an empty list,
    // it means available_groups was empty, which is caught at the start.
    // Or, if max_misps_value was positive but all candidates were below the threshold
    // (e.g. max=10, threshold=9, all others are 5). In this case, the list will still contain the max_misps_value items.
    // So, candidates_for_tiebreak should not be empty if available_groups was not empty.
    if candidates_for_tiebreak.is_empty() {
        return None;
    }

    // 4. Apply ClearFocus tie-breaking
    let mut min_remaining_tiles = usize::MAX;
    let mut best_group_info: Option<(Vec<(usize, usize)>, i32)> = None;
    let mut tie_break_original_group_size = 0;

    for (group_to_tiebreak, misps_score_of_this_candidate) in candidates_for_tiebreak {
        let mut temp_board_sim = current_board.clone();
        temp_board_sim.eliminate_group(&group_to_tiebreak);
        temp_board_sim.apply_gravity();
        temp_board_sim.shift_columns();

        let mut current_remaining_tiles = 0;
        for r in 0..BOARD_SIZE {
            for c in 0..BOARD_SIZE {
                if temp_board_sim.get_tile(r, c) != Tile::Empty {
                    current_remaining_tiles += 1;
                }
            }
        }

        let current_candidate_original_size = group_to_tiebreak.len();

        if best_group_info.is_none() || current_remaining_tiles < min_remaining_tiles {
            min_remaining_tiles = current_remaining_tiles;
            tie_break_original_group_size = current_candidate_original_size;
            best_group_info = Some((group_to_tiebreak, misps_score_of_this_candidate));
        } else if current_remaining_tiles == min_remaining_tiles {
            if current_candidate_original_size > tie_break_original_group_size {
                tie_break_original_group_size = current_candidate_original_size;
                best_group_info = Some((group_to_tiebreak, misps_score_of_this_candidate));
            }
        }
    }

    // 5. Return the result with the actual MISPS score of the chosen group
    best_group_info.map(|(chosen_group, misps_score)| (misps_score as f64, chosen_group[0]))
}


/// Chooses a move based on the Smallest Group Priority (SGP) strategy.
///
/// This strategy selects the group containing the smallest number of tiles.
/// If multiple groups have the same minimal size, the one encountered first (based on
/// `find_all_groups` iteration order) is chosen.
///
/// # Arguments
/// * `current_board`: A reference to the current `Board` state.
///
/// # Returns
/// An `Option` containing a tuple:
///   - `f64`: The number of tiles in the chosen group (its length).
///   - `(usize, usize)`: The coordinate of a representative tile from the chosen group.
/// Returns `None` if no groups are available on the board.
pub fn choose_move_sgp(current_board: &Board) -> Option<(f64, (usize, usize))> {
    let available_groups = current_board.find_all_groups();

    if available_groups.is_empty() {
        return None;
    }

    // The call to unwrap() is safe because we've checked that available_groups is not empty.
    let best_group = available_groups.iter().min_by_key(|g| g.len()).unwrap();
    Some((best_group.len() as f64, best_group[0]))
}

/// Chooses a move based on the Clear Focus strategy.
///
/// This strategy simulates eliminating each available group and chooses the one that results
/// in the minimum number of total tiles remaining on the board.
/// If multiple moves result in the same minimum number of remaining tiles, the one
/// that involves eliminating a larger original group is preferred. If still tied,
/// the one encountered first is chosen.
///
/// # Arguments
/// * `current_board`: A reference to the current `Board` state.
///
/// # Returns
/// An `Option` containing a tuple:
///   - `f64`: The minimum number of tiles remaining on the board after the chosen move.
///   - `(usize, usize)`: The coordinate of a representative tile from the chosen group.
/// Returns `None` if no groups are available on the board.
pub fn choose_move_clear_focus(current_board: &Board) -> Option<(f64, (usize, usize))> {
    let available_groups = current_board.find_all_groups();

    if available_groups.is_empty() {
        return None;
    }

    let mut min_remaining_tiles = usize::MAX;
    let mut max_original_group_size_at_min = 0;
    let mut best_group_choice: Option<Vec<(usize, usize)>> = None;

    for group_candidate in available_groups {
        // PERFORMANCE: Cloning the board for each candidate group.
        let mut temp_board_sim = current_board.clone();
        temp_board_sim.eliminate_group(&group_candidate); // Pass as slice
        temp_board_sim.apply_gravity();
        temp_board_sim.shift_columns();

        let mut remaining_tiles_count = 0;
        for r in 0..BOARD_SIZE {
            for c in 0..BOARD_SIZE {
                if temp_board_sim.get_tile(r, c) != Tile::Empty {
                    remaining_tiles_count += 1;
                }
            }
        }

        let current_candidate_original_size = group_candidate.len();

        if best_group_choice.is_none() || remaining_tiles_count < min_remaining_tiles {
            min_remaining_tiles = remaining_tiles_count;
            max_original_group_size_at_min = current_candidate_original_size;
            best_group_choice = Some(group_candidate);
        } else if remaining_tiles_count == min_remaining_tiles {
            if current_candidate_original_size > max_original_group_size_at_min { // Corrected variable name
                max_original_group_size_at_min = current_candidate_original_size;
                best_group_choice = Some(group_candidate);
            }
        }
    }

    best_group_choice.map(|group| (min_remaining_tiles as f64, group[0]))
}

/// Chooses a move based on the Avoid Orphans strategy.
///
/// This strategy primarily aims to maximize the immediate score (like MIS) but
/// heavily penalizes moves that result in "orphan" tiles (a single tile of a
/// specific color remaining after the move).
/// The heuristic value for a move is `(immediate_score) - penalty`.
/// `penalty` is a large value if orphans are created, `0.0` otherwise.
///
/// # Arguments
/// * `current_board`: A reference to the current `Board` state.
///
/// # Returns
/// An `Option` containing a tuple:
///   - `f64`: The calculated (potentially penalized) heuristic value for the chosen move.
///   - `(usize, usize)`: The coordinate of a representative tile from the chosen group.
/// Returns `None` if no groups are available on the board.
pub fn choose_move_avoid_orphans(current_board: &Board) -> Option<(f64, (usize, usize))> {
    let available_groups = current_board.find_all_groups();

    if available_groups.is_empty() {
        return None;
    }

    const ORPHAN_PENALTY: f64 = 10000.0;
    let mut max_heuristic_value = -f64::INFINITY; // Initialize with a very small value
    let mut max_group_size_at_max_heuristic = 0;
    let mut best_group_choice: Option<Vec<(usize, usize)>> = None;

    for group_candidate in available_groups {
        let immediate_score = (group_candidate.len() * group_candidate.len() * 5) as f64;

        // PERFORMANCE: Cloning the board for each candidate group.
        let mut temp_board_sim = current_board.clone();
        temp_board_sim.eliminate_group(&group_candidate); // Pass as slice
        temp_board_sim.apply_gravity();
        temp_board_sim.shift_columns();

        let mut color_counts = std::collections::HashMap::new();
        for r in 0..BOARD_SIZE {
            for c in 0..BOARD_SIZE {
                let tile = temp_board_sim.get_tile(r, c);
                if tile != Tile::Empty {
                    *color_counts.entry(tile).or_insert(0u32) += 1;
                }
            }
        }

        let mut creates_orphan = false;
        for count in color_counts.values() {
            if *count == 1 {
                creates_orphan = true;
                break;
            }
        }

        let penalty = if creates_orphan { ORPHAN_PENALTY } else { 0.0 };
        let heuristic_value = immediate_score - penalty;
        let current_candidate_original_size = group_candidate.len();

        if best_group_choice.is_none() || heuristic_value > max_heuristic_value {
            max_heuristic_value = heuristic_value;
            max_group_size_at_max_heuristic = current_candidate_original_size;
            best_group_choice = Some(group_candidate);
        } else if heuristic_value == max_heuristic_value {
            if current_candidate_original_size > max_group_size_at_max_heuristic {
                max_group_size_at_max_heuristic = current_candidate_original_size;
                best_group_choice = Some(group_candidate);
            }
        }
    }

    best_group_choice.map(|group| (max_heuristic_value, group[0]))
}

/// Chooses a move based on preserving the largest color group ("Color Reservation").
///
/// This strategy identifies the color of the largest group currently on the board.
/// It then scores moves that eliminate groups of other colors by their size,
/// while moves that eliminate groups of the "preserved" color are scored as 0.
/// The goal is to clear other colors, allowing the preserved color to consolidate.
///
/// # Arguments
/// * `current_board`: A reference to the current `Board` state.
///
/// # Returns
/// An `Option` containing a tuple:
///   - `f64`: The calculated score for the chosen move (group size or 0).
///   - `(usize, usize)`: The coordinate of a representative tile from the chosen group.
/// Returns `None` if no groups are available on the board.
pub fn choose_move_preserve_largest_color_group(
    current_board: &Board,
) -> Option<(f64, (usize, usize))> {
    let available_groups = current_board.find_all_groups();

    if available_groups.is_empty() {
        return None;
    }

    // Identify the color of the largest group (C_L)
    let largest_group_on_board = available_groups.iter().max_by_key(|g| g.len());
    let color_to_preserve: Option<Tile> = largest_group_on_board.map(|lg| {
        // Get the color of the first tile in the largest group
        // lg[0] is (row, col). We need to get the tile at this coordinate.
        let (r, c) = lg[0];
        current_board.get_tile(r, c)
    });

    if color_to_preserve.is_none() || color_to_preserve == Some(Tile::Empty) {
        // Fallback if no largest group or it's somehow empty (should not happen with find_all_groups)
        // Or if the largest group's color is Empty (shouldn't happen)
        // In this case, behave like LGP to just pick the largest available group.
        return choose_move_lgp(current_board);
    }
    let c_l = color_to_preserve.unwrap();

    let mut max_score = -1.0f64; // Scores are non-negative (0.0 or group.len())
    let mut best_group_choice: Option<Vec<(usize, usize)>> = None;
    let mut tie_break_original_size = 0;

    for group_candidate in available_groups {
        let (r_cand, c_cand) = group_candidate[0];
        let candidate_color = current_board.get_tile(r_cand, c_cand);
        let current_candidate_original_size = group_candidate.len();

        let score = if candidate_color == c_l {
            0.0 // Discourage removing the preserved color
        } else {
            current_candidate_original_size as f64
        };

        if best_group_choice.is_none() || score > max_score {
            max_score = score;
            tie_break_original_size = current_candidate_original_size;
            best_group_choice = Some(group_candidate);
        } else if score == max_score {
            if current_candidate_original_size > tie_break_original_size {
                tie_break_original_size = current_candidate_original_size;
                best_group_choice = Some(group_candidate);
            }
        }
    }

    best_group_choice.map(|group| (max_score, group[0]))
}

/// Chooses a move based on maximizing the size of the largest group on the *next* board state.
///
/// This "Connectivity/Consolidation Focus" strategy simulates eliminating each available group (`G1`).
/// For each simulation, it finds all groups on the resulting board and identifies the
/// size of the largest one (`max_next_group_size`). The strategy chooses to eliminate the
/// initial group `G1` that leads to the board state with the largest `max_next_group_size`.
///
/// # Arguments
/// * `current_board`: A reference to the current `Board` state.
///
/// # Returns
/// An `Option` containing a tuple:
///   - `f64`: The size of the largest group on the board *after* the chosen move.
///   - `(usize, usize)`: The coordinate of a representative tile from the chosen initial group.
/// Returns `None` if no groups are available on the initial board.
pub fn choose_move_connectivity_focus(current_board: &Board) -> Option<(f64, (usize, usize))> {
    let available_groups = current_board.find_all_groups();

    if available_groups.is_empty() {
        return None;
    }

    let mut max_future_group_size = 0.0f64;
    let mut best_original_group_size = 0;
    let mut best_group_choice: Option<Vec<(usize, usize)>> = None;

    for group_g1_candidate in available_groups {
        // PERFORMANCE: Cloning the board for each candidate group.
        let mut temp_board_sim = current_board.clone();
        temp_board_sim.eliminate_group(&group_g1_candidate); // Pass as slice
        temp_board_sim.apply_gravity();
        temp_board_sim.shift_columns();

        let groups_on_sim_board = temp_board_sim.find_all_groups();
        let current_max_next_group_size = if groups_on_sim_board.is_empty() {
            0
        } else {
            groups_on_sim_board
                .iter()
                .map(|g| g.len())
                .max()
                .unwrap_or(0)
        };

        let current_g1_original_size = group_g1_candidate.len();

        if best_group_choice.is_none()
            || (current_max_next_group_size as f64) > max_future_group_size
        {
            max_future_group_size = current_max_next_group_size as f64;
            best_original_group_size = current_g1_original_size;
            best_group_choice = Some(group_g1_candidate);
        } else if (current_max_next_group_size as f64) == max_future_group_size {
            if current_g1_original_size > best_original_group_size {
                best_original_group_size = current_g1_original_size;
                best_group_choice = Some(group_g1_candidate);
            }
        }
    }

    best_group_choice.map(|group| (max_future_group_size, group[0]))
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
/// The final score (`i32`) achieved after playing the game to completion using the
/// `choose_move_misps` heuristic. This score includes any end-game bonus and can be negative.
///
/// # Warnings
/// This function prints warnings to `eprintln!` if `choose_move_misps` returns an empty group
/// (which should not happen for a valid board with groups) or if `process_move` fails for a
/// chosen group (which also indicates an inconsistency).
pub fn evaluate_with_heuristic(mut game_state: Game) -> i32 {
    // Changed to i32
    while !game_state.is_game_over() {
        if let Some((_heuristic_value, chosen_group_coord)) = choose_move_misps(game_state.board())
        {
            let (r_click, c_click) = chosen_group_coord;

            if !game_state.process_move(r_click, c_click) {
                eprintln!(
                    "Warning: evaluate_with_heuristic using MISPS chose click ({},{}) but process_move failed. Board:\n{}",
                    r_click, c_click, game_state.board()
                );
                break;
            }
        } else {
            break;
        }
    }
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
        let empty_board_arr: [&str; 0] = [];
        let board_empty = board_from_str_array(&empty_board_arr).unwrap();
        assert_eq!(
            calculate_admissible_heuristic(&board_empty),
            2000,
            "Empty board heuristic"
        );

        let board_mixed_no_groups = board_from_str_array(&["RB", "YG"]).unwrap();
        assert_eq!(
            calculate_admissible_heuristic(&board_mixed_no_groups),
            5 * 4 + 2000,
            "Mixed colors, no groups"
        );

        let board_potential_groups = board_from_str_array(&["RRRG", "BB.."]).unwrap();
        assert_eq!(
            calculate_admissible_heuristic(&board_potential_groups),
            (3 * 3 * 5) + 5 + (2 * 2 * 5) + 2000,
            "Potential groups"
        );

        let board_all_red_small = board_from_str_array(&["RR", "RR"]).unwrap();
        assert_eq!(
            calculate_admissible_heuristic(&board_all_red_small),
            (4 * 4 * 5) + 2000,
            "All Red (4 tiles)"
        );

        let red_tiles_rows = vec!["RRRRR"; 5];
        let board_many_red = board_from_str_array(&red_tiles_rows).unwrap();
        assert_eq!(
            calculate_admissible_heuristic(&board_many_red),
            (25 * 25 * 5) + 2000,
            "Many Red tiles (25 tiles)"
        );

        let board_mixed_with_empty = board_from_str_array(&["R.B", ".G.", "Y.P"]).unwrap();
        assert_eq!(
            calculate_admissible_heuristic(&board_mixed_with_empty),
            5 * 5 + 2000,
            "Mixed with empty"
        );
    }
}
