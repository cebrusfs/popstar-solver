use std::collections::HashMap;
use crate::engine::{Board, Game};
use crate::heuristics::choose_move_misps;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use std::time::{Duration, Instant};

pub struct MctsNode {
    pub board: Board,
    pub move_made: Option<((usize, usize), i32)>, // ((r, c), move_score)
    pub score_so_far: i32,
    pub visits: u32,
    pub total_score: f64,
    pub children: Vec<usize>,
    pub untried_moves: Vec<((usize, usize), i32, Board)>,
    pub is_terminal: bool,
}

pub struct MctsAgent {
    pub max_iterations: usize,
    pub time_budget_ms: u64,
    pub exploration_c: f64,
}

impl MctsAgent {
    pub fn new(max_iterations: usize, time_budget_ms: u64, exploration_c: f64) -> Self {
        Self { max_iterations, time_budget_ms, exploration_c }
    }

    pub fn select_move(
        &self,
        current_board: &Board,
        current_score: i32,
    ) -> Option<((usize, usize), i32, Board)> {
        let mut tree = Vec::new();

        let groups = current_board.find_all_group_clicks_with_len();
        if groups.is_empty() {
            return None;
        }

        let mut root_untried = Vec::new();
        for ((r, c), len) in groups {
            let mut next_board = current_board.clone();
            next_board.eliminate_group_by_click(r, c);
            next_board.apply_gravity();
            next_board.shift_columns();
            let move_score = (len * len * 5) as i32;
            root_untried.push(((r, c), move_score, next_board));
        }

        tree.push(MctsNode {
            board: current_board.clone(),
            move_made: None,
            score_so_far: current_score,
            visits: 0,
            total_score: 0.0,
            children: Vec::new(),
            untried_moves: root_untried,
            is_terminal: false,
        });

        let mut rng = SmallRng::from_entropy();
        let start_time = Instant::now();
        let budget = Duration::from_millis(self.time_budget_ms);

        let mut iterations = 0;
        while iterations < self.max_iterations && start_time.elapsed() < budget {
            iterations += 1;

            // 1. Selection
            let mut node_idx = 0;
            let mut path = vec![0];

            while tree[node_idx].untried_moves.is_empty() && !tree[node_idx].children.is_empty() {
                // Select best child using UCB1
                let parent_visits = tree[node_idx].visits as f64;
                let mut best_score = -1.0;
                let mut best_child = 0;

                for &child_idx in &tree[node_idx].children {
                    let child = &tree[child_idx];
                    let v = child.visits as f64;
                    // normalize score? Scores can be up to 4000. So we might need to tune exploration_c.
                    // For now let's just use raw score as reward.
                    let avg_score = child.total_score / v;
                    let ucb = avg_score + self.exploration_c * (parent_visits.ln() / v).sqrt();
                    if ucb > best_score {
                        best_score = ucb;
                        best_child = child_idx;
                    }
                }
                node_idx = best_child;
                path.push(node_idx);
            }

            // 2. Expansion
            if !tree[node_idx].untried_moves.is_empty() {
                let untried_idx = rng.gen_range(0..tree[node_idx].untried_moves.len());
                let move_info = tree[node_idx].untried_moves.swap_remove(untried_idx);
                let move_pos = move_info.0;
                let move_score = move_info.1;
                let next_score = tree[node_idx].score_so_far + move_score;

                let groups = move_info.2.find_all_group_clicks_with_len();
                let is_terminal = groups.is_empty();

                let mut untried = Vec::new();
                for ((r, c), len) in groups {
                    let mut next_board = move_info.2.clone();
                    next_board.eliminate_group_by_click(r, c);
                    next_board.apply_gravity();
                    next_board.shift_columns();
                    untried.push(((r, c), (len * len * 5) as i32, next_board));
                }

                let child_node = MctsNode {
                    board: move_info.2.clone(),
                    move_made: Some((move_pos, move_score)),
                    score_so_far: next_score,
                    visits: 0,
                    total_score: 0.0,
                    children: Vec::new(),
                    untried_moves: untried,
                    is_terminal,
                };

                let child_idx = tree.len();
                tree.push(child_node);
                tree[node_idx].children.push(child_idx);
                node_idx = child_idx;
                path.push(node_idx);
            }

            // 3. Rollout
            let mut rollout_board = tree[node_idx].board.clone();
            let mut rollout_score = tree[node_idx].score_so_far;

            if !tree[node_idx].is_terminal {
                loop {
                    if let Some((_, (r, c))) = choose_move_misps(&rollout_board) {
                        let len = rollout_board.find_group(r, c).len();
                        rollout_board.eliminate_group_by_click(r, c);
                        rollout_board.apply_gravity();
                        rollout_board.shift_columns();
                        rollout_score += (len * len * 5) as i32;
                    } else {
                        break;
                    }
                }
            }

            let final_bonus = Game::new_with_board(rollout_board).final_score() as i32;
            rollout_score += final_bonus;

            // 4. Backpropagation
            let simulated_score = rollout_score as f64;
            for idx in path {
                tree[idx].visits += 1;
                tree[idx].total_score += simulated_score;
            }
        }

        if tree[0].children.is_empty() {
            return None;
        }

        let mut best_child = 0;
        let mut most_visits = 0;
        for &child_idx in &tree[0].children {
            if tree[child_idx].visits > most_visits {
                most_visits = tree[child_idx].visits;
                best_child = child_idx;
            }
        }

        let best_node = &tree[best_child];
        let move_made = best_node.move_made.unwrap();
        Some((move_made.0, move_made.1, best_node.board.clone()))
    }
}


pub struct SpMctsNode {
    pub board: Board,
    pub move_made: Option<((usize, usize), i32)>, // ((r, c), move_score)
    pub score_so_far: i32,
    pub visits: u32,
    pub max_score: f64,
    pub sum_squared_score: f64,
    pub sum_score: f64,
    pub children: Vec<usize>,
    pub untried_moves: Vec<((usize, usize), i32, Board)>,
    pub is_terminal: bool,
}

pub struct SpMctsAgent {
    pub max_iterations: usize,
    pub time_budget_ms: u64,
    pub exploration_c: f64,
}

impl SpMctsAgent {
    pub fn new(max_iterations: usize, time_budget_ms: u64, exploration_c: f64) -> Self {
        Self { max_iterations, time_budget_ms, exploration_c }
    }

    pub fn select_move(
        &self,
        current_board: &Board,
        current_score: i32,
    ) -> Option<((usize, usize), i32, Board)> {
        let mut tree = Vec::new();

        let groups = current_board.find_all_group_clicks_with_len();
        if groups.is_empty() {
            return None;
        }

        let mut root_untried = Vec::new();
        for ((r, c), len) in groups {
            let mut next_board = current_board.clone();
            next_board.eliminate_group_by_click(r, c);
            next_board.apply_gravity();
            next_board.shift_columns();
            let move_score = (len * len * 5) as i32;
            root_untried.push(((r, c), move_score, next_board));
        }

        tree.push(SpMctsNode {
            board: current_board.clone(),
            move_made: None,
            score_so_far: current_score,
            visits: 0,
            max_score: 0.0,
            sum_squared_score: 0.0,
            sum_score: 0.0,
            children: Vec::new(),
            untried_moves: root_untried,
            is_terminal: false,
        });

        let mut rng = SmallRng::from_entropy();
        let start_time = Instant::now();
        let budget = Duration::from_millis(self.time_budget_ms);

        let mut iterations = 0;
        while iterations < self.max_iterations && start_time.elapsed() < budget {
            iterations += 1;

            // 1. Selection
            let mut node_idx = 0;
            let mut path = vec![0];

            while tree[node_idx].untried_moves.is_empty() && !tree[node_idx].children.is_empty() {
                // Select best child using UCB1
                let parent_visits = tree[node_idx].visits as f64;
                let mut best_score = -1.0;
                let mut best_child = 0;

                for &child_idx in &tree[node_idx].children {
                    let child = &tree[child_idx];
                    let v = child.visits as f64;
                    // normalize score? Scores can be up to 4000. So we might need to tune exploration_c.
                    // For now let's just use raw score as reward.
                    let score_term = child.max_score;
                    let ucb = score_term + self.exploration_c * (parent_visits.ln() / v).sqrt();
                    if ucb > best_score {
                        best_score = ucb;
                        best_child = child_idx;
                    }
                }
                node_idx = best_child;
                path.push(node_idx);
            }

            // 2. Expansion
            if !tree[node_idx].untried_moves.is_empty() {
                let untried_idx = rng.gen_range(0..tree[node_idx].untried_moves.len());
                let move_info = tree[node_idx].untried_moves.swap_remove(untried_idx);
                let move_pos = move_info.0;
                let move_score = move_info.1;
                let next_score = tree[node_idx].score_so_far + move_score;

                let groups = move_info.2.find_all_group_clicks_with_len();
                let is_terminal = groups.is_empty();

                let mut untried = Vec::new();
                for ((r, c), len) in groups {
                    let mut next_board = move_info.2.clone();
                    next_board.eliminate_group_by_click(r, c);
                    next_board.apply_gravity();
                    next_board.shift_columns();
                    untried.push(((r, c), (len * len * 5) as i32, next_board));
                }

                let child_node = SpMctsNode {
                    board: move_info.2.clone(),
                    move_made: Some((move_pos, move_score)),
                    score_so_far: next_score,
                    visits: 0,
                    max_score: 0.0,
            sum_squared_score: 0.0,
            sum_score: 0.0,
                    children: Vec::new(),
                    untried_moves: untried,
                    is_terminal,
                };

                let child_idx = tree.len();
                tree.push(child_node);
                tree[node_idx].children.push(child_idx);
                node_idx = child_idx;
                path.push(node_idx);
            }

            // 3. Rollout
            let mut rollout_board = tree[node_idx].board.clone();
            let mut rollout_score = tree[node_idx].score_so_far;

            if !tree[node_idx].is_terminal {
                loop {
                    if let Some((_, (r, c))) = choose_move_misps(&rollout_board) {
                        let len = rollout_board.find_group(r, c).len();
                        rollout_board.eliminate_group_by_click(r, c);
                        rollout_board.apply_gravity();
                        rollout_board.shift_columns();
                        rollout_score += (len * len * 5) as i32;
                    } else {
                        break;
                    }
                }
            }

            let final_bonus = Game::new_with_board(rollout_board).final_score() as i32;
            rollout_score += final_bonus;

            // 4. Backpropagation
            let simulated_score = rollout_score as f64;
            for idx in path {
                tree[idx].visits += 1;
                tree[idx].sum_score += simulated_score;
                tree[idx].sum_squared_score += simulated_score * simulated_score;
                if simulated_score > tree[idx].max_score {
                    tree[idx].max_score = simulated_score;
                }
            }
        }

        if tree[0].children.is_empty() {
            return None;
        }

        let mut best_child = 0;
        let mut most_visits = 0;
        for &child_idx in &tree[0].children {
            if tree[child_idx].visits > most_visits {
                most_visits = tree[child_idx].visits;
                best_child = child_idx;
            }
        }

        let best_node = &tree[best_child];
        let move_made = best_node.move_made.unwrap();
        Some((move_made.0, move_made.1, best_node.board.clone()))
    }
}

// I will patch the relevant parts later.

pub struct NrpaAgent {
    pub level: usize,
    pub iterations: usize,
    pub alpha: f64,
}

impl NrpaAgent {
    pub fn new(level: usize, iterations: usize, alpha: f64) -> Self {
        Self { level, iterations, alpha }
    }

    pub fn play(&self, initial_board: &Board) -> (i32, Vec<(usize, usize)>) {
        let mut policy = [0.0; 500];
        let mut rng = SmallRng::from_entropy();
        self.nrpa(self.level, initial_board, &mut policy, &mut rng)
    }

    fn nrpa(
        &self,
        level: usize,
        state: &Board,
        policy: &mut [f64; 500],
        rng: &mut SmallRng,
    ) -> (i32, Vec<(usize, usize)>) {
        if level == 0 {
            return self.playout(state, policy, rng);
        }

        let mut best_score = -1;
        let mut best_seq = Vec::new();

        for _ in 0..self.iterations {
            let mut next_policy = *policy;
            let (score, seq) = self.nrpa(level - 1, state, &mut next_policy, rng);
            if score >= best_score {
                best_score = score;
                best_seq = seq.clone();
            }
            self.adapt(policy, &best_seq, state);
        }

        (best_score, best_seq)
    }

    fn playout(
        &self,
        state: &Board,
        policy: &[f64; 500],
        rng: &mut SmallRng,
    ) -> (i32, Vec<(usize, usize)>) {
        let mut current_state = state.clone();
        let mut seq = Vec::new();
        let mut total_score = 0;

        loop {
            let moves = current_state.find_all_group_clicks_with_len();
            if moves.is_empty() {
                break;
            }

            let mut sum_exp = 0.0;
            let mut weights = Vec::with_capacity(moves.len());

            let mut max_w = f64::NEG_INFINITY;
            for &((r, c), len) in &moves {
                let color_idx = match current_state.get_tile(r, c) {
                    crate::engine::Tile::Red => 0,
                    crate::engine::Tile::Green => 1,
                    crate::engine::Tile::Blue => 2,
                    crate::engine::Tile::Yellow => 3,
                    crate::engine::Tile::Purple => 4,
                    _ => 0,
                };
                let w = policy[color_idx * 100 + len.min(99)];
                if w > max_w { max_w = w; }
            }
            
            for &((r, c), len) in &moves {
                let color_idx = match current_state.get_tile(r, c) {
                    crate::engine::Tile::Red => 0,
                    crate::engine::Tile::Green => 1,
                    crate::engine::Tile::Blue => 2,
                    crate::engine::Tile::Yellow => 3,
                    crate::engine::Tile::Purple => 4,
                    _ => 0,
                };
                let w = policy[color_idx * 100 + len.min(99)];
                let e = (w - max_w).exp();
                sum_exp += e;
                weights.push((r, c, e));
            }

            let mut r_val = rng.gen::<f64>() * sum_exp;
            let mut chosen = weights.last().unwrap();
            for w in &weights {
                r_val -= w.2;
                if r_val <= 0.0 {
                    chosen = w;
                    break;
                }
            }

            let (r, c) = (chosen.0, chosen.1);
            seq.push((r, c));

            let len = moves.iter().find(|m| m.0 == (r, c)).unwrap().1;
            total_score += (len * len * 5) as i32;

            current_state.eliminate_group_by_click(r, c);
            current_state.apply_gravity();
            current_state.shift_columns();
        }

        let final_bonus = Game::new_with_board(current_state).final_score() as i32;
        total_score += final_bonus;

        (total_score, seq)
    }

    fn adapt(
        &self,
        policy: &mut [f64; 500],
        best_seq: &[(usize, usize)],
        state: &Board,
    ) {
        let mut current_state = state.clone();
        for &(r, c) in best_seq {
            let moves = current_state.find_all_group_clicks_with_len();

            let mut sum_exp = 0.0;
            let mut exps = Vec::with_capacity(moves.len());

            let mut max_w = f64::NEG_INFINITY;
            for &((mr, mc), len) in &moves {
                let color_idx = match current_state.get_tile(mr, mc) {
                    crate::engine::Tile::Red => 0,
                    crate::engine::Tile::Green => 1,
                    crate::engine::Tile::Blue => 2,
                    crate::engine::Tile::Yellow => 3,
                    crate::engine::Tile::Purple => 4,
                    _ => 0,
                };
                let w = policy[color_idx * 100 + len.min(99)];
                if w > max_w { max_w = w; }
            }
            
            for &((mr, mc), len) in &moves {
                let color_idx = match current_state.get_tile(mr, mc) {
                    crate::engine::Tile::Red => 0,
                    crate::engine::Tile::Green => 1,
                    crate::engine::Tile::Blue => 2,
                    crate::engine::Tile::Yellow => 3,
                    crate::engine::Tile::Purple => 4,
                    _ => 0,
                };
                let w = policy[color_idx * 100 + len.min(99)];
                let e = (w - max_w).exp();
                sum_exp += e;
                exps.push(((mr, mc, len), e));
            }

            let best_len = moves.iter().find(|m| m.0 == (r, c)).unwrap().1;
            let best_color_idx = match current_state.get_tile(r, c) {
                crate::engine::Tile::Red => 0,
                crate::engine::Tile::Green => 1,
                crate::engine::Tile::Blue => 2,
                crate::engine::Tile::Yellow => 3,
                crate::engine::Tile::Purple => 4,
                _ => 0,
            };
            policy[best_color_idx * 100 + best_len.min(99)] += self.alpha;

            for ((mr, mc, mlen), e) in exps {
                let prob = e / sum_exp;
                let color_idx = match current_state.get_tile(mr, mc) {
                    crate::engine::Tile::Red => 0,
                    crate::engine::Tile::Green => 1,
                    crate::engine::Tile::Blue => 2,
                    crate::engine::Tile::Yellow => 3,
                    crate::engine::Tile::Purple => 4,
                    _ => 0,
                };
                policy[color_idx * 100 + mlen.min(99)] -= self.alpha * prob;
            }

            current_state.eliminate_group_by_click(r, c);
            current_state.apply_gravity();
            current_state.shift_columns();
        }
    }
}
