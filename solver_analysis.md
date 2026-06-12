# PopStar Solver Analysis

## 1. Game Rules & Mathematical Equivalence

PopStar is played on a 10x10 grid of colored blocks. Players click groups of two or more same-colored adjacent blocks to eliminate them, scoring `n*n*5` points for `n` blocks. Remaining blocks fall (gravity), and empty columns are consolidated by shifting columns to the left. The game ends when no valid groups remain. A bonus (up to 2000 points) is awarded based on the number of blocks left, with the maximum for a clear board.

**Mathematical Equivalence:** 
PopStar is mathematically equivalent to the well-known computer science problem **SameGame** (or Clickomania). 
In 2001, Biedl et al. proved in *"The Complexity of Clickomania"* that determining whether a given board can be completely cleared is **NP-Complete**. Because of this, it is mathematically proven that no polynomial-time algorithm exists to find the absolute perfect score for a 10x10 board (unless P=NP). This necessitates the use of heuristic and approximation algorithms (like Beam Search or MCTS) for full-board solving, while exact algorithms (like DFS) are limited to shallow depths or smaller sub-problems.

## 2. Exact Search: Depth-First Search (DFS) & Branch and Bound

For exact optimization at shallow depths, we employ Depth-First Search (DFS). To make this feasible, several critical optimizations are necessary:

### Branch and Bound Pruning
We prune sub-optimal branches early by comparing the current score plus an **Admissible Heuristic** (Upper Bound) against the best known score.
*   **Admissible Heuristic `calculate_admissible_heuristic`:** Calculates an optimistic upper bound. It sums `k_C * k_C * 5` for each color `C` (where `k_C` is the total count of blocks of that color), then adds the maximum end-game bonus (2000 points). Since mathematically $(A+B)^2 > A^2 + B^2$, assuming all tiles of one color can be cleared simultaneously is the strict theoretical maximum score. This guarantees we never mistakenly prune the optimal path.

### Zero-Allocation Engine (Extreme Performance)
The core bottleneck in DFS tree traversal is memory allocation (GC/Heap churn). We implemented extreme exact optimizations to achieve ~400% speedups:
*   **Zero-Allocation Group Finding & Elimination:** Instead of allocating `Vec<Vec<(usize, usize)>>` to find groups, we use in-place, stack-allocated arrays (`[(0,0); 100]`) for flood-fills (`eliminate_group_by_click`).
*   **O(N) Game Over Check:** Replaced full-board group identification with a lightweight adjacency check (only verifying the Right and Down neighbors of each tile).
*   **Zero-Allocation Heuristic Playouts:** When `depth_limit` is reached, `evaluate_with_heuristic` simulates the rest of the game. Instead of cloning the heavy `Game` struct (which tracks a `history` vector of moves), we only clone the 100-byte `Board` array, completely eradicating heap allocations in the hot loop.
*   **Packed Bitboard Hashing:** State deduplication `visited_states` relies on `HashMap`. By compressing the 100 3-bit tiles into a `[u64; 5]` array (`to_packed()`), we drastically shrink memory usage and speed up equality checks.

## 3. Heuristic Strategies (Greedy Baselines)

Several single-step greedy heuristics have been implemented as baselines. They estimate the desirability of game states or moves but are fundamentally limited because they don't look ahead beyond one step:

*   **`choose_move_mis` (Maximize Immediate Score):** Selects the move yielding the highest immediate score.
*   **`choose_move_lgp` (Largest Group Priority):** Prefers eliminating the largest available group.
*   **`choose_move_crp` (Color Reduction Priority):** Chooses the move resulting in the fewest unique colors remaining.
*   **`choose_move_misps` (Maximize Immediate Score & Penalize Singletons):** Balances immediate score with a penalty for creating isolated single tiles. (Currently used for our fast playout evaluations).
*   **`choose_move_clear_focus` & `choose_move_connectivity_focus`:** Focus on minimizing remaining tiles or maximizing future connectivity.

## 4. Advanced Algorithms & AI Arena

Because exact DFS cannot solve the 10x10 board, we shifted to advanced AI approximation algorithms. To test them, we built the **AI Arena** (`src/bin/arena.rs`), an automated benchmark platform that evaluates agents across a **Golden Set of 100 random seeds (Seeds 1~100)** using Rayon for multithreading.

### AI Algorithms Implemented:
1.  **Beam Search:** Instead of keeping all branches (DFS), Beam Search keeps only the top $K$ most promising states at each depth level. Using `K=5000`, we are able to look ahead all the way to the end of the game in under 2 seconds.
2.  **Monte Carlo Tree Search (MCTS):** Uses our ultra-fast zero-allocation engine to perform rapid playouts (using UCB1 selection and MISPS rollouts). We grant it a fixed time budget per move (e.g., 100ms).

### Golden Set Benchmark (100 Seeds)

| 排名 | 演算法 (Agent) | 平均分數 | 最高分 | 完美通關率 | 每局平均耗時 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 🥇 | **BeamSearch (W=5000)** | **4703.9** | **8295** | **55.0%** | **1.94s** |
| 🥈 | **DFS Depth 5 (舊版 main)** | 4467.8 | 5735 | N/A | 0.54s |
| 🥉 | **MCTS (100ms/move)** | 4223.9 | 6730 | 26.0% | 1.04s |
| 4 | **BeamSearch (W=500)** | 3937.6 | 8180 | 19.0% | 0.20s |
| 5 | **BeamSearch (W=50)** | 3081.0 | 6290 | 4.0% | 0.02s |
| 6 | **Greedy (MISPS)** | 2324.7 | 4495 | 0.0% | 0.0002s |

Beam Search (W=5000) achieves a breathtaking **55% Clear Rate** and shatters the 8000 point limit, thoroughly outclassing depth-limited DFS in both speed and capability.

## 5. Future Directions & Improvement Loop

1. **強化 Heuristic (Beam Search)**: The current admissible heuristic assumes all blocks can be perfectly cleared. By replacing this with a more realistic predictive heuristic (e.g. evaluating connectivity or using a small neural net), Beam Search can select its 5000 branches more accurately.
2. **強化 MCTS (Rollout Strategy)**: MCTS currently uses the greedy `MISPS` strategy for rollouts. We can tune exploration constants, add domain-specific rules (like preserving vertical matches), or increase the time budget to unlock its massive parallel-scaling potential.
