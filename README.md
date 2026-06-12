# PopStar (SameGame / Clickomania) AI Solver

This project implements the PopStar puzzle game (mathematically known as **SameGame** or **Clickomania**), and a high-performance AI solver for it, in Rust.

## Game Rules

1.  **Board:** The game is played on a 10x10 grid. Cells can be one of 5 kinds of tiles or empty.
2.  **Objective:** Maximize your score by strategically eliminating groups of same-colored tiles.
3.  **Elimination:**
    *   A "group" consists of at least two adjacent (horizontally or vertically) tiles of the same kind.
    *   When a group is selected, all tiles in that group are removed.
4.  **Gravity:**
    *   After tiles are eliminated, tiles above them fall down to fill the empty spaces in their respective columns.
6.  **Column Shifting:**
    *   If a column becomes entirely empty after elimination and gravity, all columns to its right shift to the left to fill the empty column.
7.  **Scoring:**
    *   Eliminating a group of `n` tiles gives `n * n * 5` points.
8.  **Game End:** The game ends when there are no more groups of two or more same-kind tiles that can be eliminated.
9.  **Final Bonus:**
    *   At the end of the game, a bonus is awarded based on the number of remaining tiles (`m`).
    *   Bonus = `max(0, 2000 - m * m * 20)`. Maximum bonus is 2000, minus square of remaining tile count times 20.

## Project Structure

*   `popstar_solver/`: Contains the Rust implementation.
    *   `src/lib.rs`: The library crate for the game engine and solver.
    *   `src/engine.rs`: Core game logic (board, tiles, game mechanics) featuring a zero-allocation engine.
    *   `src/solver.rs`: DFS-based puzzle solver and Branch-and-Bound implementations.
    *   `src/heuristics.rs`: Predictive and admissible heuristics.
    *   `src/advanced_solvers.rs`: Contains the MCTS (Monte Carlo Tree Search) agent.
    *   `src/bin/`: Contains the executables.
        *   `human_player.rs`: For interactive gameplay.
        *   `ai_solver.rs`: For solving a given board state using DFS.
        *   `evaluator.rs`: Legacy DFS benchmark.
        *   `arena.rs`: **The AI Arena**, a parallel benchmarking platform evaluating Beam Search, MCTS, and Greedy agents against a Golden Set of random seeds.

## Advanced Solvers & Orthogonal Architecture

Because PopStar is mathematically equivalent to the NP-Complete *SameGame*, exact optimization (DFS) struggles to clear a 10x10 board. To push the limits, we built the **AI Arena** to test advanced approximation algorithms.

We use an **$N \times M$ Orthogonal Architecture** to evaluate these agents. In `arena.rs`, we decoupled **Search Algorithms** (BeamSearch, DFS, MCTS) from **Heuristics** (Admissible, Predictive V1 Orphan Penalty, Predictive V2 Component Split Penalty) using generic function pointers. This allows us to rapidly experiment with combinations like `BeamSearch` + `Predictive V2` or `MCTS` + `Predictive V1`.

*   **Beam Search (W=5000)**: Our current state-of-the-art solver. By maintaining 5000 parallel universes and using a predictive heuristic that penalizes isolated blocks and orphan colors, it achieves a **92% Perfect Clear Rate** and an average score of **~5405** on our 100-seed Golden Set.
*   **MCTS**: Uses UCB1 selection and rapid heuristic rollouts.

For a deep dive into the architecture, please see [`ARCHITECTURE.md`](./ARCHITECTURE.md).
For the *Agentic Improvement Loop* protocol and detailed benchmarks, please see [`solver_analysis.md`](./solver_analysis.md).

## Building and Running

The project is built using Cargo, the Rust package manager.

### Prerequisites
- Install Rust and Cargo: [https://www.rust-lang.org/tools/install](https://www.rust-lang.org/tools/install)

### Building the Project
Navigate to the `popstar_solver` directory and run:
```bash
cargo build --release
```

### Running the AI Arena (Benchmark)
To evaluate the latest AI agents (Beam Search, MCTS, Greedy):
```bash
# Run a quick 10-game evaluation (Default)
cargo run --release --bin arena

# Run the full Golden Set 100-game evaluation
NUM_GAMES=100 cargo run --release --bin arena
```

### Running the Interactive Player
```bash
cargo run --bin human_player
```

### Running the Exact DFS AI Solver
The DFS solver takes a depth limit and an optional board file.
```bash
cargo run --release --bin ai_solver -- 5
```
