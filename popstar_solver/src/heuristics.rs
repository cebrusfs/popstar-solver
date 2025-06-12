use crate::engine::{Board, Game, Tile, BOARD_SIZE};
use std::collections::HashSet;

// Helper function to count unique colors on the board
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

// Helper function to count tiles that cannot form a group of 2 or more
pub fn count_truly_isolated_tiles(board: &Board) -> u32 {
    let mut isolated_count = 0;
    let mut visited = [[false; BOARD_SIZE]; BOARD_SIZE];

    for r_idx in 0..BOARD_SIZE {
        for c_idx in 0..BOARD_SIZE {
            if !visited[r_idx][c_idx] && board.get_tile(r_idx, c_idx) != Tile::Empty {
                let group = board.find_group(r_idx, c_idx);
                if group.len() >= 2 {
                    // Mark all tiles in the group as visited
                    for &(r, c) in &group {
                        visited[r][c] = true;
                    }
                } else {
                    // Single tile, mark as visited and count as isolated
                    visited[r_idx][c_idx] = true;
                    isolated_count += 1;
                }
            }
        }
    }
    
    isolated_count
}

// Strategy: Maximize Immediate Score (MIS)
pub fn choose_move_mis(
    _current_board: &Board,
    available_groups: &Vec<Vec<(usize, usize)>>,
) -> Vec<(usize, usize)> {
    assert!(!available_groups.is_empty(), "choose_move_mis called with no available groups");

    let mut best_group: Vec<(usize, usize)> = available_groups[0].clone();
    let mut max_score = 0;

    if !available_groups.is_empty() {
        let first_group = &available_groups[0];
        max_score = first_group.len() * first_group.len() * 5;
    } else {
        return Vec::new();
    }

    for group in available_groups.iter() {
        let score = group.len() * group.len() * 5;
        if score > max_score {
            max_score = score;
            best_group = group.clone();
        } else if score == max_score && group.len() > best_group.len() {
            best_group = group.clone();
        }
    }
    best_group
}

// Strategy: Largest Group Priority (LGP)
pub fn choose_move_lgp(
    _current_board: &Board,
    available_groups: &Vec<Vec<(usize, usize)>>,
) -> Vec<(usize, usize)> {
    assert!(!available_groups.is_empty(), "choose_move_lgp called with no available groups");
    available_groups.iter().max_by_key(|g| g.len()).unwrap().clone()
}

// Strategy: Color Reduction Priority (CRP)
pub fn choose_move_crp(
    current_board: &Board,
    available_groups: &Vec<Vec<(usize, usize)>>,
) -> Vec<(usize, usize)> {
    assert!(!available_groups.is_empty(), "choose_move_crp called with no available groups");

    let mut best_group_choice = available_groups[0].clone();
    let mut min_resulting_colors = usize::MAX;
    let mut max_size_at_min_colors = 0;

    // Initialize with the first group's simulated result
    let mut initial_temp_board = current_board.clone();
    initial_temp_board.eliminate_group(&available_groups[0]);
    initial_temp_board.apply_gravity();
    initial_temp_board.shift_columns();
    min_resulting_colors = count_unique_colors(&initial_temp_board);
    max_size_at_min_colors = available_groups[0].len();

    for group_candidate in available_groups.iter() {
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
    best_group_choice
}

// Strategy: Maximize Immediate Score & Penalize Singletons (MISPS)
pub fn choose_move_misps(
    current_board: &Board,
    available_groups: &Vec<Vec<(usize, usize)>>,
) -> Vec<(usize, usize)> {
    assert!(!available_groups.is_empty(), "choose_move_misps called with no available groups");

    const SINGLETON_PENALTY_FACTOR: i32 = 50;

    let mut best_group_choice = available_groups[0].clone();
    let mut max_heuristic_value = i32::MIN;
    let mut max_group_size_at_max_heuristic = 0;

    // Initialize with the first group's simulated result
    let first_group = &available_groups[0];
    let first_immediate_score = (first_group.len() * first_group.len() * 5) as i32;
    let mut initial_temp_board = current_board.clone();
    initial_temp_board.eliminate_group(first_group);
    initial_temp_board.apply_gravity();
    initial_temp_board.shift_columns();
    let first_num_singletons = count_truly_isolated_tiles(&initial_temp_board);
    max_heuristic_value = first_immediate_score - (first_num_singletons as i32 * SINGLETON_PENALTY_FACTOR);
    max_group_size_at_max_heuristic = first_group.len();

    for group_candidate in available_groups.iter() {
        let immediate_score = (group_candidate.len() * group_candidate.len() * 5) as i32;

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
    best_group_choice
}

// Evaluates a game state using the MISPS strategy
pub fn evaluate_with_heuristic(mut game_state: Game) -> u32 {
    while !game_state.is_game_over() {
        let available_groups = game_state.board().find_all_groups();

        if available_groups.is_empty() {
            break;
        }

        // Use MISPS to choose the next move
        let chosen_group = choose_move_misps(game_state.board(), &available_groups);
        let (r_click, c_click) = chosen_group[0];

        if !game_state.process_move(r_click, c_click) {
            eprintln!(
                "Warning: evaluate_with_heuristic using MISPS chose group {:?} starting at ({},{}) but process_move failed. Board:\n{}",
                chosen_group, r_click, c_click, game_state.board()
            );
            break;
        }
    }
    game_state.final_score()
}
