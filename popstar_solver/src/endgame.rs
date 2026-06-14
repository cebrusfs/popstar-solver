use crate::engine::Board;
use std::collections::HashMap;

pub fn solve_endgame(board: &Board) -> i32 {
    let mut memo = HashMap::new();
    dfs(board, &mut memo)
}

fn dfs(board: &Board, memo: &mut HashMap<[u32; 10], i32>) -> i32 {
    let mut key = [0u32; 10];
    key.copy_from_slice(board.columns());
    if let Some(&score) = memo.get(&key) {
        return score;
    }

    let groups = board.find_all_group_clicks_with_len();
    if groups.is_empty() {
        let final_score = crate::engine::Game::new_with_board(board.clone()).final_score() as i32;
        memo.insert(key, final_score);
        return final_score;
    }

    let mut max_score = i32::MIN;
    for &(pos, len) in &groups {
        let mut next_board = board.clone();
        next_board.eliminate_group_by_click(pos.0, pos.1);
        next_board.apply_gravity();
        next_board.shift_columns();
        
        let move_score = (len * len * 5) as i32;
        let score = move_score + dfs(&next_board, memo);
        if score > max_score {
            max_score = score;
        }
    }
    
    memo.insert(key, max_score);
    max_score
}
