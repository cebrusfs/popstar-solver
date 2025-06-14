# PopStar Solver Analysis

## 1. Game Rules Summary

PopStar is played on a grid of colored blocks. Players click groups of two or more same-colored adjacent blocks to eliminate them, scoring `n*n*5` points for `n` blocks. Remaining blocks fall, and empty columns are consolidated by shifting columns to the left. The game ends when no valid groups remain. A bonus (up to 2000 points) is awarded based on the number of blocks left, with the maximum for a clear board.

## 2. Key Challenges for Solvers

Developing an effective PopStar solver faces several challenges:

*   **Vast Search Space:** The number of possible game states is extremely large, making exhaustive search infeasible.
*   **Complex Scoring & Lookahead:** Optimal play requires considering not just immediate points but also how moves affect future possibilities and the end-game bonus. This necessitates deep lookahead or sophisticated evaluation.
*   **High Branching Factor:** Numerous moves can be available from any given state, quickly expanding the search tree.
*   **Heuristic Design:** Crafting heuristics that accurately guide the search towards high-scoring states without excessive computation is critical and complex.

## 3. Depth-First Search (DFS)

Depth-First Search (DFS) is a fundamental algorithm for traversing the game's state space. The implemented DFS solver explores game states by recursively trying all available moves. To prevent re-exploring identical board configurations and avoid cycles, it maintains a `HashSet` of visited board states. If a pre-defined `depth_limit` (maximum number of moves down a single path) is reached before the game ends, the solver uses `evaluate_with_heuristic` (a greedy playout using the MISPS strategy) to estimate the score from that point.

### DFS Implementation Details (Current)

*   **State Management:** The current DFS implementation passes game states (`Game` objects) and move paths (`Vec<(usize, usize)>`) by value. This results in cloning the `Game` state and the path vector for each recursive step.
*   **Move Simulation:** Moves are simulated by calling `current_game_state.clone().process_move(...)`.
*   **Visited States:** The `visited_states` set stores `Board` objects, which are cloned from the game state after a move is simulated.

### Potential DFS Performance Optimization (Future Refactoring)

The current cloning approach in DFS can be a performance bottleneck, especially for deep searches. A significant optimization involves:

1.  **Mutable Game State Reference:** Change `current_game_state: Game` to `current_game_state: &mut Game`.
2.  **Mutable Path Reference:** Change `current_moves_path: Vec<(usize, usize)>` to `current_moves_path: &mut Vec<(usize, usize)>`.
3.  **In-Place Move and Backtracking:**
    *   Call `current_game_state.process_move(r, c)` directly on the mutable state.
    *   `push` the move to `current_moves_path`.
    *   After the recursive call returns, use `current_game_state.undo_last_move()` to revert the board, score, and steps.
    *   `pop` the move from `current_moves_path`.
This approach avoids frequent allocations and copies, improving performance.

### Fixed-Depth DFS for Look-ahead Move Evaluation

A common application of DFS is for look-ahead move evaluation. Instead of solving the entire game, this technique uses a shallow DFS to assess the quality of potential immediate moves.

*   **Concept:** For each currently available move, the solver "looks ahead" a few steps (e.g., 1-3 moves deep) by performing a limited DFS.
*   **Evaluation:** The game state at the leaves of this shallow search is evaluated using a heuristic (e.g., `evaluate_with_heuristic` or a simpler board score). This provides a more informed heuristic score for the initial move being considered, compared to just its immediate score.
*   **Use Case:** This can be integrated into a primary search algorithm (like a main DFS or Monte Carlo Tree Search) to make better decisions at each step, or used by simpler heuristic strategies to enhance their choice.

#### Implementation Details for Look-ahead DFS

*   **State Management:** Typically involves cloning the game state for each branch of the look-ahead to explore different short-term sequences independently. If the main DFS is refactored to use `&mut Game` and `undo_last_move`, a look-ahead function could also leverage this for efficiency within its local scope.
*   **Heuristics:** A heuristic is applied at the maximum depth of the look-ahead. This might be the same heuristic used for deeper search (`evaluate_with_heuristic`) or a faster, possibly less accurate, one.

## 4. Heuristic Strategies

Heuristics guide the search or decision-making process by estimating the desirability of game states or moves.

*   **`choose_move_mis` (Maximize Immediate Score):** Selects the move that yields the highest score for the current turn.
*   **`choose_move_lgp` (Largest Group Priority):** Prefers eliminating the largest available group of tiles.
*   **`choose_move_crp` (Color Reduction Priority):** Chooses the move that results in the fewest unique colors remaining on the board.
*   **`choose_move_misps` (Maximize Immediate Score & Penalize Singletons):** Balances immediate score with a penalty for creating isolated single tiles.
*   **`evaluate_with_heuristic`:** Simulates a full game playout from the current state using the MISPS strategy. This provides an estimated score for a game state, typically acting as a **lower bound** on the true optimal score.
*   **`calculate_admissible_heuristic`:** Calculates an **upper bound** on the score achievable from a given board state. This is crucial for algorithms like A*.
    *   **Calculation:** It sums `k_C * k_C * 5` for each color `C` (where `k_C` is the total count of blocks of that color), then adds the maximum end-game bonus (2000 points).
    *   **Admissibility:** This is an upper bound because it assumes all tiles of a color can form one large group (optimistic scoring) and that the board will be cleared entirely (maximum bonus).

## 5. Solver Performance and Optimizations

(This section would discuss general performance aspects, results of optimizations like the mutable DFS, impact of heuristics, etc. For now, it remains a placeholder for further details based on actual benchmark_results and implementation choices.)

*   **Impact of `visited_states`:** Using a `HashSet` to store visited board configurations is crucial for pruning the search space and avoiding infinite loops, significantly improving performance over a naive DFS.
*   **Cloning vs. Mutable Operations:** As discussed in the DFS section, moving from cloning game states at each step to using mutable references and an undo mechanism is a key optimization for deeper searches.
*   **Heuristic Quality vs. Computation Cost:** More complex heuristics (like MISPS or CRP) involve more computation per node (e.g., simulating moves or board states) than simpler ones (MIS, LGP). The trade-off between heuristic accuracy and evaluation speed is critical.
*   **Bitboards:** For further optimization, representing the board using bitboards could speed up group finding, gravity, and other board operations, though it would increase implementation complexity.
