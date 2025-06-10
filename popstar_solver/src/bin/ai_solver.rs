use clap::Parser;
use popstar_solver::engine::Game;
use popstar_solver::solver::solve_dfs;
use popstar_solver::utils::board_from_str_array;
use std::fs;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Depth limit for the DFS solver
    #[clap(short, long)]
    depth: u32,

    /// Path to the board file (10x10 grid format)
    board_file: PathBuf,
}

fn read_board_file(path: &PathBuf) -> Result<Game, String> {
    let content = fs::read_to_string(path)
        .map_err(|e| format!("Failed to read file: {}", e))?;

    let lines: Vec<&str> = content.lines()
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .collect();

    if lines.len() != 10 {
        return Err(format!("Expected 10 lines in board file, found {}", lines.len()));
    }

    for (i, line) in lines.iter().enumerate() {
        if line.len() != 10 {
            return Err(format!("Line {} has {} characters (expected 10)", i + 1, line.len()));
        }
    }

    board_from_str_array(&lines)
        .map_err(|e| format!("Invalid board format: {}", e))
        .map(|board| Game::new_with_board(board))
}

fn main() {
    let args = Args::parse();

    let game = read_board_file(&args.board_file).expect(&format!("Failed to read board from file: {}", args.board_file.display()));
    println!("Loaded board from {}\n", args.board_file.display());
    println!("Initial board state:\n{}\n", game.board());
    println!("Searching for solution with depth limit {}...\n", args.depth);

    if let Some(solution) = solve_dfs(&game, args.depth) {
        println!("Solution found:\n");
        println!("Moves ({}):", solution.steps_taken);
        if solution.moves.is_empty() {
            println!("  No moves made.");
        } else {
            for (i, (r, c)) in solution.moves.iter().enumerate() {
                println!("  Move {}: ({}, {})", i + 1, r, c);
            }
        }
        println!("Final score: {}\n", solution.score);
        println!("Final board state:\n{}\n", solution.final_board_state);
    } else {
        println!("No solution found.\n");
    }
}
