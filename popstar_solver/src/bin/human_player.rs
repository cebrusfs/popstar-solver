use popstar_solver::engine::{Game, BOARD_SIZE}; // Assuming Game and BOARD_SIZE are pub from engine
use std::io::{self, Write}; // For input/output

fn main() {
    let mut game = Game::new(); // Initialize a new game (uses random board by default)
    println!("Welcome to PopStar!");

    loop {
        println!("---------------------");
        println!("Steps: {}, Score: {}", game.steps(), game.score());
        println!("{}", game.board()); // Display the board

        if game.is_game_over() {
            println!("");
            println!("---------------------");
            println!("🎉 GAME OVER! 🎉");
            println!("Final Score: {}", game.final_score());
            println!("Total Steps: {}", game.steps());
            println!("---------------------");
            break;
        }

        print!("Enter your move (row col), or 'u' to undo, 'q' to quit: ");
        io::stdout().flush().unwrap(); // Ensure prompt is shown before input

        let mut input = String::new();
        if io::stdin().read_line(&mut input).is_err() {
            println!("Error reading input. Please try again.");
            continue;
        }

        let trimmed_input = input.trim();

        if trimmed_input == "q" {
            println!("Thanks for playing!");
            break;
        }

        if trimmed_input == "u" {
            if game.undo_last_move() {
                println!("Move undone.");
            } else {
                println!("Cannot undo further (already at initial state or no moves made).");
            }
            continue;
        }

        // Try to parse as coordinates
        let parts: Vec<&str> = trimmed_input.split_whitespace().collect();
        if parts.len() == 2 {
            if let (Ok(r), Ok(c)) = (parts[0].parse::<usize>(), parts[1].parse::<usize>()) {
                if r < BOARD_SIZE && c < BOARD_SIZE {
                    if game.process_move(r, c) {
                        println!("Move processed.");
                    } else {
                        // process_move returns false if no group or invalid click
                        println!("Invalid move: No group of 2 or more found at ({}, {}), or tile is empty.", r, c);
                    }
                } else {
                    println!("Invalid coordinates: Row and column must be between 0 and {}.", BOARD_SIZE - 1);
                }
            } else {
                println!("Invalid input: Please enter numbers for row and column (e.g., '3 4'), 'u', or 'q'.");
            }
        } else {
            println!("Invalid input format. Use 'row col', 'u', or 'q'.");
        }
    }
}
