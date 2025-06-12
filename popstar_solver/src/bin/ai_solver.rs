use clap::Parser;
use popstar_solver::engine::Game;
use popstar_solver::solver::{solve_dfs, Solution};
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
    println!("Searching for solution with depth limit {}...", args.depth);

    let mut game = read_board_file(&args.board_file).expect(&format!("Failed to read board from file: {}", args.board_file.display()));
    println!("Loaded board from {}", args.board_file.display());
    println!("{}", game.board());

    let mut known_best_solution = Solution {
        moves: Vec::new(),
        score: 0,
        steps_taken: 0,
    };
    let mut step = 1;
    while !game.is_game_over() {
        println!("Step {}", step);
        println!("Known best score: {}", known_best_solution.score);

        let (solution_opt, _iterations) = solve_dfs(&game, args.depth);
        if let Some(solution) = solution_opt {
            // Store the best solution found so far and compared with the current solution
            // if the current solution is better, then update the best solution
            if solution.score >= known_best_solution.score {
                known_best_solution = solution;
            }

            let best_move = known_best_solution.moves.remove(0);
            println!("{}", game.board().to_string_with_highlight(Some(best_move)));

            game.process_move(best_move.0, best_move.1);
            println!("Score: --> {}", game.score());
            println!("");
        } else {
            println!("No solution found.");
            break;
        }
        step += 1;
    }
    println!("Steps: {}", step);
    println!("{}", game.board());
    println!("Score: --> {}", game.final_score());
}
