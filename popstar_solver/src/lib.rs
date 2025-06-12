//! # PopStar Solver Library
//!
//! This library provides the core game logic for the PopStar puzzle game
//! and a Depth First Search (DFS) solver to find optimal solutions.
//!
//! It is used by two binaries:
//! - `human_player`: Allows interactive gameplay via the command line.
//! - `ai_solver`: Takes a board configuration and a depth limit, then
//!   outputs a sequence of moves to achieve the best possible score.
//!
//! The library also provides various heuristic strategies for move selection
//! in the `heuristics` module.
//!
//! ## Modules
//! - `engine`: Contains the game board representation (`Board`), tile types (`Tile`),
//!   game state management (`Game`), and all game mechanics (elimination, gravity, scoring).
//! - `solver`: Provides the `solve_dfs` function for finding solutions to PopStar puzzles.
//! - `heuristics`: Defines various strategies and helper functions for choosing moves or evaluating board states.
//! - `utils`: Provides utility functions, such as parsing board configurations from strings.

pub mod engine;
pub mod heuristics;
pub mod solver;
pub mod utils;

// Items from sub-modules like `heuristics`, `engine`, etc., if public,
// should be accessed via their full path, e.g., `popstar_solver::heuristics::choose_move_mis()`.
// This keeps the top-level library namespace cleaner.
