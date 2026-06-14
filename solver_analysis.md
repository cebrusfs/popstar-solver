# PopStar AI Solver Analysis & Leaderboard

## 1. Golden 100-Game Leaderboard (MODE=full-eval)
This is the definitive benchmark running on 100 fixed random seeds (`MODE=full-eval`).

| Rank | Agent | Avg Score | Max Score | Clear Rate | Avg Time/Game | Notes |
|---|---|---|---|---|---|---|
| 🥇 | **RolloutBeam-W2000** | **5779.9** | 8400 | **100.0%** | **1.91s** | Deterministic Rollout Beam Search (W=2000). Best overall. |
| 🥈 | **RolloutBeam-W500** | 5666.4 | 8400 | 92.0% | 1.35s | Same as above but slightly narrower beam. Extremely fast. |
| 🥉 | **BMCTS-W100-N20-V2** | 5528.1 | 8400 | 73.0% | 1.68s | Previous SOTA. Replaced by RolloutBeam due to N20 redundancy. |
| 4 | **RolloutBeam-W100** | 5531.1 | 8400 | 71.0% | 0.97s | Ultra-fast Rollout Beam. |
| 5 | **BeamSearch-W5000-V2** | 5406.6 | 8340 | 92.0% | 3.14s | Pure static heuristic (Predictive V2). Very strong clear rate. |
| 6 | **BeamSearch-W500-V2** | 5012.1 | 8325 | 67.0% | 0.43s | Lightweight static heuristic beam search. |
| 7 | **SP-MCTS-250ms** | 4616.6 | 6700 | 27.0% | 3.71s | Single-Player Monte Carlo Tree Search with UCT. |
| 8 | **NRPA-L2-I100** | 4462.8 | 7640 | 14.0% | 1.03s | Nested Rollout Policy Adaptation. |
| 9 | **NMCS-L3** | ~4220.0 | ~4950 | 0.0% | ~1.9s | Nested Monte-Carlo Search. (Estimated from 10-game eval) |
| 10 | **Greedy-MISPS** | 2324.7 | 4495 | 0.0% | 0.00s | Baseline greedy solver. |


## 2. Algorithm Evolutions & Architecture
Our solver has evolved through multiple iterations:

1. **Greedy & DFS**: The original approach. DFS was too slow, Greedy was too weak.
2. **Beam Search with Predictive Heuristics**: 
   - Introduced `BeamSearch-W5000`. We developed `predictive_heuristic_v2` which statically evaluates a board by clustering components and heavily penalizing "split" components of the same color. This achieved 5400+ scores.
3. **MCTS & NRPA**:
   - Tried traditional UCT-based MCTS and NRPA (Nested Rollout Policy Adaptation). Both struggled to beat Beam Search because pure random rollouts in PopStar are highly deceptive.
4. **BMCTS (Beam Monte Carlo Tree Search)**:
   - Combined Beam Search (to keep top K branches) with MCTS (running N rollouts per node). 
   - **Crucial Discovery**: Using the `predictive_heuristic_v2` to guide the rollouts instead of random play massively boosted performance to 5500+.
5. **RolloutBeamSearch (The Breakthrough)**:
   - We realized that `predictive_heuristic_v2` rollouts are completely *deterministic*. The `N=20` loop in BMCTS was evaluating the exact same sequence 20 times!
   - By removing the redundant loop, we collapsed `BMCTS` into `RolloutBeamSearch`, effectively speeding it up by 20x. We reinvested this time into expanding the Beam Width from `W=100` to `W=2000`, achieving a staggering **100% Clear Rate** and **~5786** score.

## 3. Agentic Improvement Loop Protocol

For future AI Agents working on this project autonomously, follow this protocol to continuously improve the solver:

1. **Ideation**: Read `solver_analysis.md` to understand the current SOTA (`RolloutBeam-W2000`). Formulate a new hypothesis (e.g. PUCT for Beam Search, Endgame Exact Solver, better rollout heuristics).
2. **Isolation & Checkpoint**: Use `jj new -m "feat: your idea"` to create a safe commit BEFORE touching code.
3. **Implementation**: Edit `src/advanced_solvers.rs` or `src/bin/arena.rs`. If creating a new algorithm, decouple it so it implements the `Agent` trait and add it to the `arena.rs` agent list.
4. **Rapid Tuning (10 Games)**: Run `MODE=research-eval cargo run --release --bin arena`. This runs the AI on seeds 1001-1010 (10 games). Iterate on your hyperparameters until your algorithm beats the baseline or looks promising.
5. **Full Evaluation (100 Games)**: Once tuned, run `MODE=full-eval cargo run --release --bin arena` (seeds 1-100). If it takes a long time, use `schedule` or check logs.
6. **Decision**:
   - **Success**: Update the Leaderboard in this document, summarize the breakthrough, and keep the commit.
   - **Failure**: Abandon the commit (`jj abandon`) to keep the codebase clean, document the failure here, and loop back to step 1.
