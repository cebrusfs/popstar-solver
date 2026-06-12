# PopStar Solver Analysis & AI Agent Guide

This document contains the latest benchmark data for the advanced AI solvers and serves as the **Agentic Improvement Loop** protocol for future AI agents to continue improving the solver.
For foundational knowledge on the game rules, NP-Complete mathematical equivalence, exact search optimization (DFS), and basic greedy heuristics, please see [`ARCHITECTURE.md`](./ARCHITECTURE.md).

## 1. Advanced Algorithms & AI Arena

Because exact DFS cannot solve the 10x10 board, we shifted to advanced AI approximation algorithms. To test them, we built the **AI Arena** (`src/bin/arena.rs`), an automated benchmark platform that evaluates agents across a **Golden Set of 100 random seeds (Seeds 1~100)** using Rayon for multithreading.

### AI Algorithms Implemented:
1.  **Beam Search:** Instead of keeping all branches (DFS), Beam Search keeps only the top $K$ most promising states at each depth level. Using `K=5000`, we are able to look ahead all the way to the end of the game in under 1.5 seconds.
2.  **Monte Carlo Tree Search (MCTS) & SP-MCTS:** Uses our ultra-fast zero-allocation bitboard engine to perform rapid playouts (using UCB1 selection and MISPS rollouts). We grant it a fixed time budget per move (e.g., 100ms or 250ms).

### Golden Set Benchmark (100 Seeds)

| Rank | Algorithm | Avg Score | Max Score | Clear Rate | Avg Time |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 🥇 | **BeamSearch (W=5000) [Predictive Heuristic + Orphan Penalty]** | **5161.4** | **8340** | **89.0%** | **1.32s** |
| 🥈 | **BeamSearch (W=500) [Predictive Heuristic + Orphan Penalty]** | 4706.9 | 7915 | 65.0% | 0.13s |
| 🥉 | **SP-MCTS (250ms/move)** | 4537.8 | 6035 | 20.0% | 3.66s |
| 4 | **DFS Depth 5 (Baseline)** | 4467.8 | 5735 | N/A | 0.54s |
| 5 | **MCTS (100ms/move)** | 4160.9 | 5980 | 23.0% | 1.04s |
| 6 | **BeamSearch (W=50) [Predictive Heuristic + Orphan Penalty]** | 3999.5 | 7390 | 28.0% | 0.01s |
| 7 | **Greedy (MISPS)** | 2324.7 | 4495 | 0.0% | 0.0002s |

Beam Search (W=5000) with the explicit **-5000 Orphan Penalty** and native Bitboard evaluation achieves a breathtaking **89% Clear Rate** and shatters the 5000 point barrier on average!

## 2. Agentic Improvement Loop (Protocol for Autonomous AI)

This section contains exact instructions for future AI agents to continue improving the solver autonomously without requiring user intervention. Future AI agents must strictly follow this step-by-step loop.

### Objective
Your goal is to beat the current top average score and perfect clear rate on the **Golden Set Benchmark (100 Seeds)**. Currently, the target to beat is the 🥇 **BeamSearch (W=5000)** baseline (89% clear rate).

### Step-by-Step Execution Protocol

1.  **Ideation & Implementation:**
    *   Formulate a specific algorithmic hypothesis. Examples:
        *   **Heuristics Enhancement:** Improve the evaluation heuristic used in Beam Search to select the top $K$ branches. E.g., introduce connectivity-based evaluation or prioritize keeping colors grouped together instead of assuming the optimistic `calculate_admissible_heuristic`.
        *   **MCTS Rollout Strategy:** Replace the greedy `MISPS` rollout in MCTS with a more domain-aware rule (e.g., preserving vertical matches). Tune exploration constants (`UCT`), add Progressive Widening, or integrate RAVE.
        *   **Engine Optimization:** Profile and optimize memory/CPU hot-paths to enable more iterations/deeper searches per second.
    *   Implement your new feature in the source code (typically under `src/agents/`, `src/evaluator.rs`, or `src/board.rs`). Ensure you test it logically before benchmarking.
    *   Integrate your agent/heuristic into the Arena. Open `src/bin/arena.rs` and add an entry to the `agents` vector for your new implementation, clearly labeling it (e.g., `"MCTS_Tuned"`, `"BeamSearch_ConnectedHeuristic"`).

2.  **Benchmark Execution:**
    *   Compile and run the Arena benchmarker locally over the Golden Set (100 random seeds):
        ```bash
        cd popstar_solver
        NUM_GAMES=100 cargo run --release --bin arena
        ```
    *   *Note:* The `--release` flag is critically important. Debug builds are too slow. Default `cargo run --release --bin arena` runs only 10 seeds for fast iterations.

3.  **Evaluation & Verification:**
    *   Analyze the console output of the Arena run.
    *   Compare the **Average Score**, **Perfect Clear Rate**, and **Average Time** of your new agent against the baseline table listed in Section 1.
    *   **Success Criteria:** An implementation is considered a "Win" if it either:
        *   Increases the Average Score and/or Perfect Clear Rate with reasonable performance overhead.
        *   Achieves comparable scores but operates significantly faster.

4.  **Documentation & Persistence:**
    *   **If the benchmark fails or scores are worse:** Use `jj undo` to revert the code, or modify the logic and repeat step 1. Do NOT commit regressions.
    *   **If the benchmark succeeds:** 
        1.  Update the **Golden Set Benchmark (100 Seeds)** table in Section 1 of this file (`solver_analysis.md`) with the new rankings, scores, and clear rates.
        2.  Write a brief summary of the successful strategy below the table.
        3.  Ensure the working directory is clean (`jj status`), fix up the code styling (`cargo fmt`), and persist the change:
            ```bash
            jj new -m "feat: <describe your algorithm optimization>"
            ```
5.  **Iteration:**
    *   Once a new baseline is established, repeat the entire loop. Keep pushing the theoretical limits of the 10x10 PopStar board!

## 3. Academic Literature & Future Improvement Directions

Based on research into solving the **SameGame** / **Clickomania** NP-Complete problem, academic literature highlights several state-of-the-art algorithms that future agents should attempt to implement to break current records:

1.  **Single-Player MCTS (SP-MCTS):**
    Traditional MCTS (like UCT) is designed for adversarial games to maximize win rates. For single-player puzzles, SP-MCTS modifies the Selection and Backpropagation phases to optimize for the **Max Score** rather than a win probability, often propagating the maximum score found in a subtree rather than the average.
2.  **NRPA (Nested Rollout Policy Adaptation):**
    A record-breaking algorithm in the SameGame domain. Instead of relying on random or static greedy rollouts (like our `MISPS`), NRPA learns an online rollout policy during the search. It adjusts the probability of choosing certain colors/moves based on the sequences that previously yielded high scores, making the Monte Carlo simulations progressively smarter.
3.  **BMCTS (Beam Monte-Carlo Tree Search):**
    A hybrid approach. It uses Beam Search to prune the tree (keeping only the top $K$ nodes per depth), but instead of using a static heuristic to rank the nodes, it uses MCTS rollouts to evaluate their true potential. This combines the narrow-and-deep focus of Beam Search with the accurate dynamic evaluation of MCTS.
4.  **RAVE (Rapid Action Value Estimation):**
    An enhancement for MCTS that shares the value of actions (moves) across different branches of the tree. If eliminating a specific green block proves highly valuable in one branch, RAVE biases the search to try that same elimination early in other branches, drastically speeding up convergence in the early stages of the search.
