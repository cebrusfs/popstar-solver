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
//! ## Modules
//! - `engine`: Contains the game board representation (`Board`), tile types (`Tile`),
//!   game state management (`Game`), and all game mechanics (elimination, gravity, scoring).
//! - `solver`: Provides the `solve_dfs` function for finding solutions to PopStar puzzles.

pub mod engine;
pub mod solver;
pub mod utils;
