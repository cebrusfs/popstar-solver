# PopStar Puzzle Game and Solver

This project implements the PopStar puzzle game, and a solver for it, in Rust.

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

*   `cpp/`: Contains the original C++ implementation. Deprecating.
*   `popstar_solver/`: Contains the Rust implementation.
    *   `src/lib.rs`: The library crate for the game engine and solver.
    *   `src/engine.rs`: Core game logic (board, tiles, game mechanics).
    *   `src/solver.rs`: DFS-based puzzle solver.
    *   `src/bin/`: Contains the executables.
        *   `human_player.rs`: For interactive gameplay.
        *   `ai_solver.rs`: For solving a given board state.

## Building and Running

The project is built using Cargo, the Rust package manager.

### Prerequisites
- Install Rust and Cargo: [https://www.rust-lang.org/tools/install](https://www.rust-lang.org/tools/install)

### Building the Project
Navigate to the `popstar_solver` directory and run:
```bash
cargo build
```
For a release build (optimized):
```bash
cargo build --release
```
The binaries will be located in `popstar_solver/target/debug/` or `popstar_solver/target/release/`.

### Running the Interactive Player
```bash
cargo run --bin human_player
```
Or, after building:
```bash
./popstar_solver/target/debug/human_player
```
(Use `popstar_solver\target\debug\human_player.exe` on Windows)


### Running the AI Solver
The AI solver requires a depth limit and can take an optional board file. If no file is provided, it reads the board from stdin.

**Arguments:**
`ai_solver <depth_limit> [board_file]`

**Board File Format:**
The board file should contain 10 lines, each with 10 characters representing the tiles (R, G, B, Y, P, or . for empty), without spaces.
The board should represent a stable state: tiles must have settled under gravity (i.e., no tiles floating above empty cells within the same column).

For example, a board with some empty cells in the top-right might look like this in the file:
```
RGYBPRG...
BPRGYBP...
YRGYBPG...
GYBPMRGYBP
PMRGYBPMRG
RGYBPRGYBP
BPRGYBPMRG
YRGYBPGRBP
GYBPMRGYPM
PMRGYBPMRG
```

**Examples:**

1.  Run with a board file and depth limit 5:
    ```bash
To create a board file (e.g., `my_board.txt`), you can use a text editor or the following `cat` command in your terminal:
```bash
cat << EOF > my_board.txt
RGYBPRGYBP
BPRGYBPMRG
YRGYBPGRBP
GYBPMRGYPM
PMRGYBPMRG
RGYBPRGYBP
BPRGYBPMRG
YRGYBPGRBP
GYBPMRGYPM
PMRGYBPMRG
EOF
```
This will create `my_board.txt` with the specified content.

    cargo run --bin ai_solver -- 5 ./my_board.txt
    ```
    (Note: `--` is used to pass arguments to the binary when using `cargo run`. The path to `my_board.txt` should be relative to the `popstar_solver` directory, or an absolute path.)

2.  Run with stdin input and depth limit 3:
    ```bash
    cargo run --bin ai_solver -- 3
    ```
    (The program will then wait for you to paste/type the 10 lines of the board, followed by EOF (Ctrl+D on Linux/macOS, Ctrl+Z then Enter on Windows)).
```
