use clap::Parser;
use popstar_solver::engine::Game; // Board, Tile, BOARD_SIZE no longer directly needed here
use popstar_solver::solver::solve_dfs;
use popstar_solver::utils::board_from_str_array;

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    board: Vec<String>,
    #[clap(short, long)]
    depth: u32,
}

fn main() {
    let args = Args::parse();

    match board_from_str_array(&args.board.iter().map(AsRef::as_ref).collect::<Vec<&str>>()) {
        Ok(initial_board) => {
            let game = Game::new_with_board(initial_board);

            if let Some(solution) = solve_dfs(&game, args.depth) {
                println!("Solution found:");
                println!("Moves ({}):", solution.steps_taken);
                if solution.moves.is_empty() {
                    println!("  No moves made.");
                } else {
                    for (i, (r, c)) in solution.moves.iter().enumerate() {
                        println!("  Move {}: ({}, {})", i + 1, r, c);
                    }
                }
                println!("Final score: {}", solution.score);
                println!("Final board state:\n{}", solution.final_board_state);
            } else {
                // solve_dfs is designed to always return Some, but handle defensively
                println!("No solution found (this is unexpected).");
            }
        }
        Err(e) => {
            eprintln!("Error parsing board: {}", e);
        }
    }
}
