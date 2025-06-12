//! Core game engine for the PopStar puzzle.
//!
//! This module defines the game's fundamental components:
//! - `Tile`: Represents the different types of tiles on the board.
//! - `Board`: Represents the game board and includes methods for tile manipulation,
//!   group finding, gravity, column shifting, and bonus calculation.
//! - `Game`: Manages the overall game state, including score, steps, history (for undo),
//!   and processing player moves.
// TODO: Consider caching the results of find_all_groups if performance analysis indicates this is a bottleneck, especially if called multiple times on an unchanged board.
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use std::collections::VecDeque;
use std::fmt;

/// Represents the type of a tile on the game board.
///
/// Each variant corresponds to a specific color or an empty state.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Tile {
    /// Represents an empty space on the board.
    Empty,
    /// Represents a red tile.
    Red,
    /// Represents a green tile.
    Green,
    /// Represents a blue tile.
    Blue,
    /// Represents a yellow tile.
    Yellow,
    /// Represents a purple tile.
    Purple,
}

// New private helper function for generating random tile colors.
// This function is used internally by `Board::new_random` and `Board::new_random_with_seed`
// to ensure that generated boards only contain colored tiles (not `Tile::Empty`).
fn generate_random_tile_color(rng: &mut impl Rng) -> Tile {
    match rng.gen_range(0..5u8) {
        0 => Tile::Red,
        1 => Tile::Green,
        2 => Tile::Blue,
        3 => Tile::Yellow,
        4 => Tile::Purple,
        _ => unreachable!("Generated value out of range"),
    }
}

impl Tile {
    // Removed Tile::random_color(rng: &mut u32)

    /// Converts the tile to its character representation.
    ///
    /// This is primarily used for text-based display or serialization of the board.
    ///
    /// # Examples
    ///
    /// ```
    /// use popstar_solver::engine::Tile;
    /// assert_eq!(Tile::Red.to_char(), 'R');
    /// assert_eq!(Tile::Empty.to_char(), '.');
    /// ```
    pub fn to_char(&self) -> char {
        match self {
            Tile::Empty => '.',
            Tile::Red => 'R',
            Tile::Green => 'G',
            Tile::Blue => 'B',
            Tile::Yellow => 'Y',
            Tile::Purple => 'P',
        }
    }

    /// Returns the ANSI color code string for terminal output.
    fn to_ansi_color_code(&self) -> &'static str {
        match self {
            Tile::Empty => "40",
            Tile::Red => "41",
            Tile::Green => "42",
            Tile::Yellow => "43",
            Tile::Blue => "44",
            Tile::Purple => "45",
        }
    }
}

/// Defines the size of the game board (width and height).
/// The board is always square. For example, a `BOARD_SIZE` of 10 means a 10x10 grid.
pub const BOARD_SIZE: usize = 10;

/// Represents the game board as a 2D grid of `Tile`s.
///
/// The board stores the state of each cell (tile type) and provides
/// methods for game mechanics like finding groups, eliminating tiles,
/// applying gravity, and shifting columns.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Board {
    grid: [[Tile; BOARD_SIZE]; BOARD_SIZE],
}

impl Board {
    /// Creates a new empty game board with all tiles set to `Tile::Empty`.
    ///
    /// # Returns
    /// A `Board` instance where every cell is `Tile::Empty`.
    ///
    /// # Examples
    /// ```
    /// use popstar_solver::engine::{Board, Tile, BOARD_SIZE};
    /// let board = Board::new_empty();
    /// assert_eq!(board.get_tile(0, 0), Tile::Empty);
    /// ```
    pub fn new_empty() -> Self {
        Board {
            grid: [[Tile::Empty; BOARD_SIZE]; BOARD_SIZE],
        }
    }

    /// Creates a new game board with randomly assigned, non-empty colors for each tile.
    ///
    /// This method uses a fixed internal seed (`514514`) for the random number generator
    /// to ensure that calls to `new_random()` are deterministic and produce the same
    /// board if called multiple times. This is useful for consistent testing or specific game scenarios.
    /// All tiles will be one of the five colors; no `Tile::Empty` will be generated here.
    ///
    /// # Returns
    /// A `Board` instance filled with randomly chosen `Tile` colors.
    pub fn new_random() -> Self {
        let mut grid = [[Tile::Empty; BOARD_SIZE]; BOARD_SIZE];
        let mut rng = SmallRng::seed_from_u64(514514); // Use SmallRng for deterministic generation

        for r in 0..BOARD_SIZE {
            for c in 0..BOARD_SIZE {
                grid[r][c] = generate_random_tile_color(&mut rng); // Use new helper
            }
        }
        Board { grid }
    }

    /// Creates a new game board with randomly assigned, non-empty colors using a provided seed.
    ///
    /// This allows for reproducible random boards. Different seeds will produce
    /// different board configurations, but the same seed will always produce the same board.
    /// All tiles will be one of the five colors; no `Tile::Empty` will be generated here.
    ///
    /// # Arguments
    /// * `seed`: A `u32` value used to seed the random number generator.
    ///
    /// # Returns
    /// A `Board` instance filled with randomly chosen `Tile` colors based on the given seed.
    pub fn new_random_with_seed(seed: u32) -> Self {
        let mut grid = [[Tile::Empty; BOARD_SIZE]; BOARD_SIZE];
        let mut rng = SmallRng::seed_from_u64(seed as u64); // Use SmallRng seeded with the provided value

        for r in 0..BOARD_SIZE {
            for c in 0..BOARD_SIZE {
                grid[r][c] = generate_random_tile_color(&mut rng); // Use new helper
            }
        }
        Board { grid }
    }

    /// Creates a new board from a predefined grid configuration.
    ///
    /// This is useful for testing or setting up specific game scenarios.
    ///
    /// # Arguments
    /// * `initial_grid`: A 2D array of `Tile`s representing the desired board state.
    ///   The dimensions must match `BOARD_SIZE`.
    ///
    /// # Returns
    /// A `Board` instance initialized with the provided `initial_grid`.
    pub fn from_grid(initial_grid: [[Tile; BOARD_SIZE]; BOARD_SIZE]) -> Self {
        Board { grid: initial_grid }
    }

    /// Returns the tile at the specified row (`r`) and column (`c`).
    ///
    /// # Arguments
    /// * `r`: The row index (0-based).
    /// * `c`: The column index (0-based).
    ///
    /// # Panics
    /// Panics if `r` or `c` are outside the board dimensions (`0 <= r < BOARD_SIZE`, `0 <= c < BOARD_SIZE`).
    pub fn get_tile(&self, r: usize, c: usize) -> Tile {
        self.grid[r][c]
    }

    /// Sets the tile at the specified row (`r`) and column (`c`) to the given `tile` type.
    ///
    /// # Arguments
    /// * `r`: The row index (0-based).
    /// * `c`: The column index (0-based).
    /// * `tile`: The `Tile` to place at the specified coordinates.
    ///
    /// # Panics
    /// Panics if `r` or `c` are outside the board dimensions.
    pub fn set_tile(&mut self, r: usize, c: usize, tile: Tile) {
        self.grid[r][c] = tile;
    }

    /// Returns a mutable reference to the underlying 2D grid of tiles.
    ///
    /// This allows direct manipulation of the board's grid, which should be used with caution
    /// as it can lead to inconsistent board states if not handled properly (e.g., by not
    /// applying gravity or shifting columns afterwards when tiles are cleared).
    ///
    /// # Returns
    /// A mutable reference to the `[[Tile; BOARD_SIZE]; BOARD_SIZE]` grid.
    pub fn get_grid_mut(&mut self) -> &mut [[Tile; BOARD_SIZE]; BOARD_SIZE] {
        &mut self.grid
    }

    /// Returns an immutable reference to the underlying 2D grid of tiles.
    ///
    /// This is useful for reading the board state directly without modification.
    ///
    /// # Returns
    /// An immutable reference to the `[[Tile; BOARD_SIZE]; BOARD_SIZE]` grid.
    pub fn get_grid(&self) -> &[[Tile; BOARD_SIZE]; BOARD_SIZE] {
        &self.grid
    }

    /// Generates a string representation of the board with an optional highlighted position.
    ///
    /// The output includes row and column numbers and uses ANSI escape codes for tile colors
    /// in a terminal environment. If `pos` is `Some((r, c))`, the tile at that position
    /// will be highlighted (e.g., by showing `..` instead of empty space for colored tiles).
    ///
    /// # Arguments
    /// * `pos`: An `Option<(usize, usize)>` specifying the (row, column) of the tile to highlight.
    ///   If `None`, no tile is highlighted.
    ///
    /// # Returns
    /// A `String` containing the formatted board representation suitable for terminal output.
    // NOTE: Naming reviewed: current name is clear.
    pub fn to_string_with_highlight(&self, pos: Option<(usize, usize)>) -> String {
        let mut output = String::new();

        output.push_str("  ");
        for c_idx in 0..BOARD_SIZE {
            output.push_str(&format!("{:<2}", c_idx));
        }
        output.push('\n');

        for r_idx in 0..BOARD_SIZE {
            output.push_str(&format!("{:<2}", r_idx));

            for c_idx in 0..BOARD_SIZE {
                let is_highlight = pos.map_or(false, |p| p.0 == r_idx && p.1 == c_idx);
                let color_code = self.grid[r_idx][c_idx].to_ansi_color_code();
                let content = if is_highlight { ".." } else { "  " };
                output.push_str(&format!("\x1b[1;{};m{}\x1b[m", color_code, content));
            }
            if r_idx < BOARD_SIZE - 1 {
                output.push('\n');
            }
        }

        output
    }

    /// Finds a connected group of same-colored tiles starting from the given coordinates (`r`, `c`).
    ///
    /// A group must consist of at least two tiles of the same color. Tiles are considered
    /// connected if they are adjacent horizontally or vertically (not diagonally).
    /// This method uses a Breadth-First Search (BFS) algorithm.
    ///
    /// # Arguments
    /// * `r`: The row index (0-based) of the starting tile.
    /// * `c`: The column index (0-based) of the starting tile.
    ///
    /// # Returns
    /// A `Vec<(usize, usize)>` containing the coordinates of all tiles in the found group.
    /// The coordinates within the returned vector are sorted (row-major, then column-major).
    /// Returns an empty vector if the starting tile is `Tile::Empty`, if the coordinates are
    /// out of bounds (though `get_tile` would panic first), or if no group of 2 or more
    /// same-colored tiles is found.
    ///
    /// # Panics
    /// Panics if `r` or `c` are out of the board's bounds, due to `get_tile`.
    pub fn find_group(&self, r: usize, c: usize) -> Vec<(usize, usize)> {
        let tile_kind = self.get_tile(r, c);
        if tile_kind == Tile::Empty {
            return Vec::new(); // Cannot form a group from an empty tile
        }

        let mut group = Vec::new();
        let mut q = VecDeque::new(); // Queue for BFS
        let mut visited = [[false; BOARD_SIZE]; BOARD_SIZE]; // Tracks visited cells for this specific BFS

        q.push_back((r, c));
        visited[r][c] = true;

        let dr = [-1, 1, 0, 0]; // Delta for row (up, down)
        let dc = [0, 0, -1, 1]; // Delta for column (left, right)

        while let Some((curr_r, curr_c)) = q.pop_front() {
            group.push((curr_r, curr_c));

            // Explore neighbors
            for i in 0..4 {
                let nr_signed = curr_r as isize + dr[i];
                let nc_signed = curr_c as isize + dc[i];

                // Check bounds for neighbor
                if nr_signed >= 0
                    && nr_signed < BOARD_SIZE as isize
                    && nc_signed >= 0
                    && nc_signed < BOARD_SIZE as isize
                {
                    let nr = nr_signed as usize;
                    let nc = nc_signed as usize;
                    // If neighbor is same color and not visited, add to queue
                    if !visited[nr][nc] && self.get_tile(nr, nc) == tile_kind {
                        visited[nr][nc] = true;
                        q.push_back((nr, nc));
                    }
                }
            }
        }

        // A valid group must have at least 2 tiles
        if group.len() >= 2 {
            group.sort_unstable(); // Ensure consistent order for easier testing and comparison
            group
        } else {
            Vec::new() // Not a valid group
        }
    }

    /// Finds all distinct groups of connected, same-colored tiles on the board.
    ///
    /// Each group returned will contain at least two tiles. The groups themselves are sorted
    /// by their first tile's coordinates (row-major, then column-major), and tiles within
    /// each group are also sorted by their coordinates. This ensures a canonical representation
    /// of groups on the board.
    ///
    /// This method iterates through each cell of the board. If a cell contains a non-empty tile
    /// and has not yet been visited as part of another group, `find_group` is called from that cell.
    ///
    /// # Returns
    /// A `Vec<Vec<(usize, usize)>>` where each inner vector represents a group of tile coordinates.
    /// Returns an empty vector if no groups of 2 or more tiles are found on the board.
    pub fn find_all_groups(&self) -> Vec<Vec<(usize, usize)>> {
        let mut all_groups = Vec::new();
        let mut visited_for_all_groups = [[false; BOARD_SIZE]; BOARD_SIZE]; // Tracks tiles already part of a found group

        for r_idx in 0..BOARD_SIZE {
            for c_idx in 0..BOARD_SIZE {
                // If tile is not empty and not yet part of any group found so far
                if self.get_tile(r_idx, c_idx) != Tile::Empty
                    && !visited_for_all_groups[r_idx][c_idx]
                {
                    let group = self.find_group(r_idx, c_idx);

                    if !group.is_empty() {
                        // find_group ensures group.len() >= 2
                        // Mark all tiles in this newly found group as visited
                        for &(gr, gc) in &group {
                            visited_for_all_groups[gr][gc] = true;
                        }
                        all_groups.push(group);
                    } else {
                        // If find_group returns empty (e.g., it was a singleton tile),
                        // mark just this starting tile as visited in the context of find_all_groups
                        // to avoid redundant `find_group` calls on it.
                        visited_for_all_groups[r_idx][c_idx] = true;
                    }
                }
            }
        }
        // Sort groups by their first tile's coordinates for consistent output
        all_groups.sort_unstable_by_key(|g| g[0]); // g[0] is (row, col) which sorts row-major
        all_groups
    }

    /// Eliminates a specified group of tiles from the board by setting them to `Tile::Empty`.
    ///
    /// Calculates the score obtained from eliminating this group. The score is `n * n * 5`,
    /// where `n` is the number of tiles in the group.
    ///
    /// # Arguments
    /// * `group`: A slice of `(usize, usize)` coordinates representing the tiles to be eliminated.
    ///   It's assumed that these tiles form a valid group.
    ///
    /// # Returns
    /// The score (`u32`) obtained from eliminating the group. Returns 0 if the group is empty.
    ///
    /// # Panics
    /// Panics if any coordinate in `group` is out of bounds, due to `set_tile`.
    pub fn eliminate_group(&mut self, group: &[(usize, usize)]) -> u32 {
        if group.is_empty() {
            return 0;
        }
        for &(r, c) in group {
            // Bounds check is implicitly handled by set_tile, but good to be aware.
            // If r,c were out of bounds, set_tile would panic.
            self.set_tile(r, c, Tile::Empty);
        }
        let n = group.len() as u32;
        n * n * 5 // Score calculation: n^2 * 5
    }

    /// Applies gravity to the board column by column.
    ///
    /// After tiles are eliminated, any tiles above the resulting empty spaces will fall
    /// down to fill these spaces within their respective columns.
    /// This method iterates through each column, moving tiles downwards to occupy
    /// the lowest available empty slots.
    pub fn apply_gravity(&mut self) {
        for c in 0..BOARD_SIZE {
            // Iterate through each column
            let mut empty_slot = BOARD_SIZE - 1; // Start searching for empty slots from the bottom of the column
                                                 // Iterate upwards from the bottom of the current column
            for r_check in (0..BOARD_SIZE).rev() {
                if self.grid[r_check][c] != Tile::Empty {
                    // If we find a non-empty tile
                    // If this tile is not already in the lowest available empty_slot for it
                    if r_check != empty_slot {
                        self.grid[empty_slot][c] = self.grid[r_check][c]; // Move tile to the empty_slot
                        self.grid[r_check][c] = Tile::Empty; // Vacate its original position
                    }
                    // Successfully placed a tile or found it already in place,
                    // move the empty_slot pointer up.
                    empty_slot = empty_slot.saturating_sub(1);
                }
            }
        }
    }

    /// Shifts columns to the left if any column becomes entirely empty.
    ///
    /// If a column is completely devoid of tiles (all `Tile::Empty`) after eliminations
    /// and gravity, all columns to its right are shifted one position to the left
    /// to fill the gap. This process is repeated if multiple empty columns are created.
    pub fn shift_columns(&mut self) {
        let mut write_col = 0; // Tracks the column index where the next non-empty column should be written
        for read_col in 0..BOARD_SIZE {
            // Iterate through all columns from left to right
            // Check if the current read_col is entirely empty by checking all its rows.
            let is_read_column_empty =
                (0..BOARD_SIZE).all(|r| self.grid[r][read_col] == Tile::Empty);

            if !is_read_column_empty {
                // If the read_col contains any tiles
                if read_col != write_col {
                    // And it's not already in its correct (shifted) position
                    // Move the entire column from read_col to write_col
                    for r_idx in 0..BOARD_SIZE {
                        self.grid[r_idx][write_col] = self.grid[r_idx][read_col];
                        self.grid[r_idx][read_col] = Tile::Empty; // Clear the original column cells
                    }
                }
                write_col += 1; // Increment write_col, as it's now filled
            }
            // If is_column_empty is true, write_col is not incremented, so the empty
            // column is effectively skipped and will be overwritten by subsequent non-empty columns.
        }
    }

    /// Calculates the end-of-game bonus based on the number of tiles remaining on the board.
    ///
    /// The bonus is awarded according to the formula: `max(0, 2000 - (remaining_tiles_count^2 * 20))`.
    /// A board cleared of all tiles (0 remaining tiles) yields the maximum bonus of 2000 points.
    /// If 10 or more tiles remain, the penalty `(remaining_tiles_count^2 * 20)` will be
    /// 2000 or more, resulting in a bonus of 0.
    ///
    /// # Returns
    /// The calculated bonus score as a `u32`.
    pub fn calculate_bonus(&self) -> u32 {
        let mut remaining_count = 0;
        for r in 0..BOARD_SIZE {
            for c in 0..BOARD_SIZE {
                if self.grid[r][c] != Tile::Empty {
                    remaining_count += 1;
                }
            }
        }

        if remaining_count == 0 {
            2000 // Max bonus for a completely cleared board
        } else {
            // Penalty calculation: (number of remaining tiles)^2 * 20
            let penalty = remaining_count * remaining_count * 20;
            if 2000 >= penalty {
                // Ensure bonus is not negative
                2000 - penalty
            } else {
                0 // Bonus is 0 if penalty exceeds or equals 2000 (e.g., for 10 or more tiles)
            }
        }
    }
}

impl fmt::Display for Board {
    /// Formats the board for display using `to_string_with_highlight(None)`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string_with_highlight(None))
    }
}

/// Manages the state and progression of a PopStar game session.
///
/// This struct encapsulates the game board, current score, number of steps (moves) taken,
/// and a history of game states. The history allows for undoing moves.
///
/// # Examples
/// ```
/// use popstar_solver::engine::{Game, Board};
/// // Create a game with a default random board
/// let mut game = Game::new();
/// // Or create a game with a specific board
/// let empty_board = Board::new_empty();
/// let mut game_with_board = Game::new_with_board(empty_board);
///
/// // Access game properties
/// println!("Current score: {}", game.score());
/// println!("Steps taken: {}", game.steps());
/// // println!("Board state:\n{}", game.board()); // board() returns &Board
///
/// // Process a move (e.g., clicking tile at row 0, col 0)
/// if game.process_move(0, 0) {
///     println!("Move successful!");
/// } else {
///     println!("Invalid move.");
/// }
///
/// // Check if game is over
/// if game.is_game_over() {
///     println!("Game Over! Final score: {}", game.final_score());
/// }
///
/// // Undo the last move
/// if game.undo_last_move() {
///     println!("Last move undone.");
/// }
/// ```
#[derive(Clone, Debug)] // Clone is needed for history and potentially for solver states (e.g. in DFS)
pub struct Game {
    board: Board,
    current_score: u32,
    steps: u32,
    history: Vec<(Board, u32, u32)>, // Stores (board_state, score_at_state, steps_at_state) for undo
}

impl Game {
    /// Creates a new game with a randomly generated board using `Board::new_random()`.
    ///
    /// The initial score is 0, and steps are 0. The game history starts with this initial state.
    /// `Board::new_random()` uses a fixed seed, so this will always produce the same initial game.
    pub fn new() -> Self {
        let initial_board = Board::new_random();
        Game {
            board: initial_board.clone(),
            current_score: 0,
            steps: 0,
            history: vec![(initial_board, 0, 0)], // Save initial state for potential undo to start
        }
    }

    /// Creates a new game with a specified initial board state.
    ///
    /// The initial score is 0, and steps are 0. The game history starts with this initial state.
    ///
    /// # Arguments
    /// * `initial_board`: The `Board` to start the game with.
    pub fn new_with_board(initial_board: Board) -> Self {
        Game {
            board: initial_board.clone(),
            current_score: 0,
            steps: 0,
            history: vec![(initial_board, 0, 0)], // Save initial state
        }
    }

    /// Returns an immutable reference to the current game board.
    pub fn board(&self) -> &Board {
        &self.board
    }

    /// Returns the current score of the game.
    /// This score reflects points from eliminated groups and does not include any end-game bonus.
    pub fn score(&self) -> u32 {
        self.current_score
    }

    /// Returns the number of moves (steps) taken so far in the game.
    /// Each step corresponds to one successful group elimination.
    pub fn steps(&self) -> u32 {
        self.steps
    }

    /// Processes a player's move by attempting to eliminate a group at the given coordinates `(r, c)`.
    ///
    /// If a valid group (2 or more same-colored tiles) is found at the specified coordinates:
    /// 1. The group is eliminated from the board using `Board::eliminate_group`.
    /// 2. The score obtained from this elimination is added to `current_score`.
    /// 3. Gravity is applied to the board using `Board::apply_gravity`.
    /// 4. Columns are shifted left if any become empty using `Board::shift_columns`.
    /// 5. The `steps` counter is incremented.
    /// 6. The new game state (board, score, steps) is saved to the `history` for undo purposes.
    ///
    /// # Arguments
    /// * `r`: The row index (0-based) of the selected tile.
    /// * `c`: The column index (0-based) of the selected tile.
    ///
    /// # Returns
    /// * `true` if a valid group was found and the move was processed successfully.
    /// * `false` if the coordinates are out of bounds, the selected tile is `Tile::Empty`,
    ///   or no valid group of 2 or more tiles is found at `(r, c)`.
    pub fn process_move(&mut self, r: usize, c: usize) -> bool {
        if r >= BOARD_SIZE || c >= BOARD_SIZE {
            return false; // Click is outside board boundaries
        }

        let group = self.board.find_group(r, c);
        if group.is_empty() {
            // No valid group (less than 2 tiles, or clicked on an Empty tile)
            return false;
        }

        // A valid group was found, proceed with the move
        let score_gained = self.board.eliminate_group(&group);
        self.current_score += score_gained;

        self.board.apply_gravity();
        self.board.shift_columns();

        self.steps += 1;

        // Save current state to history for potential undo
        self.history
            .push((self.board.clone(), self.current_score, self.steps));

        true
    }

    /// Undoes the last move made in the game, reverting to the previous state.
    ///
    /// If the history contains more than one state (i.e., at least one move has been made),
    /// this method removes the current state from history and restores the game's board,
    /// score, and steps to the state immediately preceding the last processed move.
    ///
    /// # Returns
    /// * `true` if a move was successfully undone.
    /// * `false` if no moves have been made yet (i.e., only the initial state is in history),
    ///   meaning there is nothing to undo.
    pub fn undo_last_move(&mut self) -> bool {
        if self.history.len() > 1 {
            // Can only undo if there's more than the initial state
            self.history.pop(); // Remove the current state from history
                                // The new current state is now the last one in history after the pop
            let &(ref prev_board, prev_score, prev_steps) = self
                .history
                .last()
                .expect("History should not be empty after checking len > 1 and popping");
            self.board = prev_board.clone();
            self.current_score = prev_score;
            self.steps = prev_steps;
            true
        } else {
            false // Nothing to undo, already at the initial state
        }
    }

    /// Checks if the game is over.
    ///
    /// The game is considered over if there are no more valid groups of tiles
    /// (2 or more same-colored, adjacent tiles) that can be eliminated from the board.
    /// This is determined by calling `Board::find_all_groups()` and checking if the result is empty.
    ///
    /// # Returns
    /// `true` if no more moves can be made (game is over), `false` otherwise.
    pub fn is_game_over(&self) -> bool {
        self.board.find_all_groups().is_empty()
    }

    /// Calculates the final score of the game.
    ///
    /// The final score is the sum of the `current_score` (accumulated from eliminated groups during play)
    /// and the end-of-game `bonus`. The bonus is calculated by `Board::calculate_bonus()`
    /// based on the number of tiles remaining on the board when the game ends.
    ///
    /// # Returns
    /// The total final score as a `u32`.
    pub fn final_score(&self) -> u32 {
        self.current_score + self.board.calculate_bonus()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::board_from_str_array;

    #[test]
    fn test_new_empty_board() {
        let board = Board::new_empty();
        for r in 0..BOARD_SIZE {
            for c in 0..BOARD_SIZE {
                assert_eq!(board.get_tile(r, c), Tile::Empty);
            }
        }
    }

    #[test]
    fn test_new_random_board() {
        let board = Board::new_random(); // Uses fixed seed now
        let board_s2 = Board::new_random_with_seed(12345);

        let mut has_non_empty_b1 = false;
        let mut different_from_empty_b2 = false;

        for r in 0..BOARD_SIZE {
            for c in 0..BOARD_SIZE {
                // Random boards should not produce Empty tiles with current Tile::random_color
                assert_ne!(
                    board.get_tile(r, c),
                    Tile::Empty,
                    "Random board should not contain Empty tiles"
                );
                if board.get_tile(r, c) != Tile::Red {
                    // Check against one color
                    has_non_empty_b1 = true;
                }
                if board_s2.get_tile(r, c) != Tile::Red {
                    different_from_empty_b2 = true;
                }
            }
        }
        assert!(
            has_non_empty_b1,
            "Random board (default seed) was all Red or Empty, which is unlikely or an error."
        );
        assert!(
            different_from_empty_b2,
            "Random board (seed 12345) was all Red or Empty."
        );

        // Test determinism of default seed
        let board_clone = Board::new_random();
        assert_eq!(
            board.grid, board_clone.grid,
            "new_random() should be deterministic"
        );
    }

    #[test]
    fn test_new_random_with_seed_determinism() {
        let seed = 123;
        let board1 = Board::new_random_with_seed(seed);
        let board2 = Board::new_random_with_seed(seed);
        assert_eq!(
            board1.grid, board2.grid,
            "Boards with the same seed must be identical."
        );

        let board3 = Board::new_random_with_seed(seed + 1);
        assert_ne!(
            board1.grid, board3.grid,
            "Boards with different seeds should differ."
        );
    }

    #[test]
    fn test_board_from_grid() {
        let mut initial_grid = [[Tile::Empty; BOARD_SIZE]; BOARD_SIZE];
        initial_grid[0][0] = Tile::Red;
        let board = Board::from_grid(initial_grid);
        assert_eq!(board.get_tile(0, 0), Tile::Red);
        assert_eq!(board.get_tile(0, 1), Tile::Empty);
    }

    #[test]
    fn test_tile_to_char() {
        assert_eq!(Tile::Empty.to_char(), '.');
        assert_eq!(Tile::Red.to_char(), 'R');
        assert_eq!(Tile::Green.to_char(), 'G');
        assert_eq!(Tile::Blue.to_char(), 'B');
        assert_eq!(Tile::Yellow.to_char(), 'Y');
        assert_eq!(Tile::Purple.to_char(), 'P');
    }

    #[test]
    fn test_display_board_formatting() {
        let board_str = [
            "R........",
            ".G.......",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........B",
        ];
        let board = board_from_str_array(&board_str).unwrap();
        let display_str = format!("{}", board);
        println!("---Board Display Test:\n{}---", display_str);

        // Check for column numbers
        assert!(
            display_str.contains("  0 1 2 3 4 5 6 7 8 9 "),
            "Missing or incorrect column numbers"
        );

        // Check for row numbers
        assert!(display_str.contains("0 "), "Missing row 0 formatting");
        assert!(
            display_str.contains(&format!("{} ", BOARD_SIZE - 1)),
            "Missing last row formatting"
        );

        // Basic checks sufficient

        // Check line count: 1 header line + BOARD_SIZE lines for rows
        assert_eq!(
            display_str.trim().lines().count(),
            BOARD_SIZE + 1,
            "Incorrect number of lines in display output"
        );
    }

    #[test]
    fn test_find_group_simple() {
        let board = board_from_str_array(&[
            "RR.......",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
        ])
        .unwrap();
        let group = board.find_group(0, 0);
        assert_eq!(group, vec![(0, 0), (0, 1)]);
    }

    #[test]
    fn test_find_group_no_group() {
        let board = board_from_str_array(&[
            "RB.......",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
        ])
        .unwrap();
        let group = board.find_group(0, 0);
        assert!(group.is_empty());
    }

    #[test]
    fn test_find_group_on_empty_tile() {
        let board = board_from_str_array(&[
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
        ])
        .unwrap();
        let group = board.find_group(0, 0);
        assert!(group.is_empty());
    }

    #[test]
    fn test_find_group_complex() {
        // Removed unused 'board' variable. The intended board for this test is 'board_complex'.
        // Original board was:
        // R R .
        // R B R
        // . R R
        // For the string "R.R" for row 1, tile (1,1) is Tile::Empty.
        // So find_group(1,1) will be empty.
        // The original test had board.set_tile(1,1, Tile::Blue);
        // Let's adjust the string to match the original intent for group finding.
        // The string was:
        // board.set_tile(0,0, Tile::Red); board.set_tile(0,1, Tile::Red);
        // board.set_tile(1,0, Tile::Red); board.set_tile(1,1, Tile::Blue); board.set_tile(1,2, Tile::Red);
        //                                 board.set_tile(2,1, Tile::Red); board.set_tile(2,2, Tile::Red);
        // R R . . .
        // R B R . .
        // . R R . .
        let board_complex = board_from_str_array(&[
            "RR.......",
            "RBR......",
            ".RR......",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
        ])
        .unwrap();

        let group_at_00 = board_complex.find_group(0, 0);
        assert_eq!(group_at_00, vec![(0, 0), (0, 1), (1, 0)]);

        let group_at_12 = board_complex.find_group(1, 2); // This will be R at (1,2) and (2,1), (2,2)
        assert_eq!(group_at_12, vec![(1, 2), (2, 1), (2, 2)]);

        let group_at_11_blue = board_complex.find_group(1, 1); // This is B at (1,1)
        assert!(group_at_11_blue.is_empty()); // Single B tile is not a group
    }

    #[test]
    fn test_find_all_groups() {
        let board = board_from_str_array(&[
            "RR.BB....", // Group RR, Group BB (col 3,4)
            "GG.B.....", // Group GG, B is part of BB group above
            ".........",
            "YYY......", // Group YYY
            "...PP....", // Group PP (col 3,4)
            ".....R...", // Single R, no group
            ".........",
            ".........",
            ".........",
            ".........",
        ])
        .unwrap();
        // Original:
        // board.set_tile(0,0,Tile::Red); board.set_tile(0,1,Tile::Red);
        // board.set_tile(0,3,Tile::Blue); board.set_tile(0,4,Tile::Blue); board.set_tile(1,3,Tile::Blue);
        // board.set_tile(1,0,Tile::Green); board.set_tile(1,1,Tile::Green);
        // board.set_tile(3,0,Tile::Yellow); board.set_tile(3,1,Tile::Yellow); board.set_tile(3,2,Tile::Yellow);
        // board.set_tile(5,5,Tile::Red);
        // board.set_tile(4,3,Tile::Purple); board.set_tile(4,4,Tile::Purple);

        let all_groups_found = board.find_all_groups();
        // Expected groups based on the string array:
        // 1. R R at (0,0), (0,1)
        // 2. B B B at (0,3), (0,4), (1,3)
        // 3. G G at (1,0), (1,1)
        // 4. Y Y Y at (3,0), (3,1), (3,2)
        // 5. P P at (4,3), (4,4)
        // The single R at (5,5) is not a group.
        let expected_groups_data = [
            vec![(0, 0), (0, 1)],         // RR
            vec![(0, 3), (0, 4), (1, 3)], // BBB
            vec![(1, 0), (1, 1)],         // GG
            vec![(3, 0), (3, 1), (3, 2)], // YYY
            vec![(4, 3), (4, 4)],         // PP
        ];

        // The find_all_groups function sorts groups by their first element, and elements within groups.
        // So, we need to ensure our expected_groups_data matches this.
        // The current expected_groups_data is already sorted in this manner.

        assert_eq!(
            all_groups_found.len(),
            5,
            "Mismatch in number of groups found"
        );
        for (i, expected_group) in expected_groups_data.iter().enumerate() {
            assert_eq!(&all_groups_found[i], expected_group, "Group {} mismatch", i);
        }
    }

    #[test]
    fn test_eliminate_group_score_and_empty() {
        let mut board = board_from_str_array(&[
            "RRR......",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
        ])
        .unwrap();
        let group_to_eliminate = vec![(0, 0), (0, 1), (0, 2)];
        let score = board.eliminate_group(&group_to_eliminate);

        assert_eq!(score, 3 * 3 * 5);
        assert_eq!(board.get_tile(0, 0), Tile::Empty);
        assert_eq!(board.get_tile(0, 1), Tile::Empty);
        assert_eq!(board.get_tile(0, 2), Tile::Empty);
    }

    #[test]
    fn test_apply_gravity_simple_revised() {
        let mut board = board_from_str_array(&[
            "R.R......", // Row 0: R at 0, R at 2
            ".G.......", // Row 1: G at 1
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
        ])
        .unwrap();
        board.apply_gravity();

        // Removed unused 'expected_board_str'.
        // Create the expected grid string dynamically
        let mut expected_rows_strings: Vec<String> = vec![".........".to_string(); BOARD_SIZE];
        if BOARD_SIZE > 0 {
            let last_row_idx = BOARD_SIZE - 1;
            let mut last_row_chars = vec!['.'; BOARD_SIZE];
            last_row_chars[0] = 'R';
            last_row_chars[1] = 'G';
            last_row_chars[2] = 'R';
            expected_rows_strings[last_row_idx] = last_row_chars.into_iter().collect::<String>();
        }
        // Convert Vec<String> to Vec<&str> for board_from_str_array
        let expected_rows_strs: Vec<&str> =
            expected_rows_strings.iter().map(|s| s.as_str()).collect();
        let expected_board = board_from_str_array(&expected_rows_strs).unwrap();

        assert_eq!(board.get_grid(), expected_board.get_grid());
    }

    #[test]
    fn test_apply_gravity_full_column_empty() {
        let mut board = Board::new_empty();
        let initial_state = board.clone();
        board.apply_gravity();
        assert_eq!(board.get_grid(), initial_state.get_grid());
    }

    #[test]
    fn test_apply_gravity_column_already_settled() {
        let mut board_rows = vec!["........."; BOARD_SIZE];
        if BOARD_SIZE >= 2 {
            board_rows[BOARD_SIZE - 1] = "R........";
            board_rows[BOARD_SIZE - 2] = "R........";
        } else if BOARD_SIZE == 1 {
            board_rows[BOARD_SIZE - 1] = "R........";
        }
        let mut board = board_from_str_array(&board_rows).unwrap();
        let expected_grid = board.get_grid().clone();
        board.apply_gravity();
        assert_eq!(board.get_grid(), &expected_grid);
    }

    #[test]
    fn test_apply_gravity_mixed_column() {
        let mut board = board_from_str_array(&[
            "R........", // Row 0
            ".........", // Row 1
            "B........", // Row 2
            ".........", // Row 3
            "R........", // Row 4
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
        ])
        .unwrap();
        board.apply_gravity();

        let mut expected_rows = vec!["........."; BOARD_SIZE];
        if BOARD_SIZE >= 3 {
            expected_rows[BOARD_SIZE - 1] = "R........"; // R from row 4
            expected_rows[BOARD_SIZE - 2] = "B........"; // B from row 2
            expected_rows[BOARD_SIZE - 3] = "R........"; // R from row 0
        } else if BOARD_SIZE == 2 {
            expected_rows[BOARD_SIZE - 1] = "B........";
            expected_rows[BOARD_SIZE - 2] = "R........";
        } else if BOARD_SIZE == 1 {
            expected_rows[BOARD_SIZE - 1] = "R........";
        }

        let expected_board = board_from_str_array(&expected_rows).unwrap();
        assert_eq!(board.get_grid(), expected_board.get_grid());
    }

    #[test]
    fn test_shift_columns_simple() {
        // R . B
        // R . B
        // ..... (rest of the rows are empty)
        let mut board = board_from_str_array(&[
            "R.B......",
            "R.B......",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
        ])
        .unwrap();
        board.shift_columns();

        // Expected:
        // R B .
        // R B .
        let expected_board = board_from_str_array(&[
            "RB.......",
            "RB.......",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
        ])
        .unwrap();
        assert_eq!(board.get_grid(), expected_board.get_grid());
    }

    #[test]
    fn test_shift_columns_no_empty_columns() {
        let mut board = Board::new_random_with_seed(123);
        let initial_state_grid = board.get_grid().clone();
        board.shift_columns();
        assert_eq!(board.get_grid(), &initial_state_grid);
    }

    #[test]
    fn test_shift_columns_all_empty() {
        let mut board = Board::new_empty();
        let initial_state_grid = board.get_grid().clone();
        board.shift_columns();
        assert_eq!(board.get_grid(), &initial_state_grid);
    }

    #[test]
    fn test_shift_columns_first_column_empty() {
        // . R B
        // .....
        let mut board = board_from_str_array(&[
            ".RB......",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
        ])
        .unwrap();
        board.shift_columns();

        // Expected:
        // R B .
        // .....
        let expected_board = board_from_str_array(&[
            "RB.......",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
        ])
        .unwrap();
        assert_eq!(board.get_grid(), expected_board.get_grid());
    }

    #[test]
    fn test_calculate_bonus() {
        let board_empty = board_from_str_array(&vec!["........."; BOARD_SIZE]).unwrap();
        assert_eq!(board_empty.calculate_bonus(), 2000);

        let mut board_one_tile_rows = vec!["........."; BOARD_SIZE];
        if BOARD_SIZE > 0 {
            board_one_tile_rows[0] = "R........";
        }
        let board_one_tile = board_from_str_array(&board_one_tile_rows).unwrap();
        assert_eq!(board_one_tile.calculate_bonus(), 1980);

        let mut board_two_tiles_rows = vec!["........."; BOARD_SIZE];
        if BOARD_SIZE > 0 {
            board_two_tiles_rows[0] = "RR.......";
        }
        let board_two_tiles = board_from_str_array(&board_two_tiles_rows).unwrap();
        assert_eq!(board_two_tiles.calculate_bonus(), 1920);

        let mut ten_tiles_rows = vec!["........."; BOARD_SIZE];
        if BOARD_SIZE > 0 {
            ten_tiles_rows[0] = "RRRRRRRRRR";
        }
        let board_ten_tiles = board_from_str_array(&ten_tiles_rows).unwrap();
        assert_eq!(board_ten_tiles.calculate_bonus(), 0);

        let mut eleven_tiles_rows = ["........."; BOARD_SIZE];
        if BOARD_SIZE > 1 {
            eleven_tiles_rows[0] = "RRRRRRRRRR";
            eleven_tiles_rows[1] = "R........";
        } else if BOARD_SIZE == 1 {
            // only 10 tiles can fit
            eleven_tiles_rows[0] = "RRRRRRRRRR";
        }
        let board_eleven_tiles = board_from_str_array(&eleven_tiles_rows).unwrap();
        // If BOARD_SIZE == 1, it's 10 tiles, bonus 0.
        // If BOARD_SIZE > 1, it's 11 tiles, bonus 0.
        assert_eq!(board_eleven_tiles.calculate_bonus(), 0);
    }

    fn create_board_with_simple_group() -> Board {
        // R R .
        // G . .  (G was at (1,0) to stop group)
        // . . .
        board_from_str_array(&[
            "RR.......",
            "G........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
        ])
        .unwrap()
    }

    #[test]
    fn test_game_new() {
        let game = Game::new(); // Uses Board::new_random()
        assert_eq!(game.score(), 0);
        assert_eq!(game.steps(), 0);
        assert_eq!(game.history.len(), 1); // Initial state
                                           // Check if board is not all empty (random board property)
        let mut all_empty = true;
        for r in 0..BOARD_SIZE {
            for c in 0..BOARD_SIZE {
                if game.board().get_tile(r, c) != Tile::Empty {
                    all_empty = false;
                    break;
                }
            }
            if !all_empty {
                break;
            }
        }
        assert!(
            !all_empty,
            "Game::new() with random board resulted in an all-empty board, unlikely."
        );
    }

    #[test]
    fn test_game_new_with_board() {
        let board = create_board_with_simple_group();
        let game = Game::new_with_board(board.clone());
        assert_eq!(game.score(), 0);
        assert_eq!(game.steps(), 0);
        assert_eq!(game.history.len(), 1);
        assert_eq!(game.board().get_grid(), board.get_grid());
    }

    #[test]
    fn test_game_process_move_valid() {
        let board = create_board_with_simple_group(); // RR. G.. ...
        let mut game = Game::new_with_board(board);

        let move_processed = game.process_move(0, 0); // Click on R at (0,0)
        assert!(move_processed, "Valid move was not processed");
        assert_eq!(game.score(), 2 * 2 * 5, "Score after one move incorrect"); // 20
        assert_eq!(game.steps(), 1, "Steps after one move incorrect");
        assert_eq!(
            game.history.len(),
            2,
            "History length after one move incorrect"
        );

        // Board state after RR at (0,0),(0,1) removed and gravity/shift:
        // G . .  (Green from (1,0) should fall to (9,0) if BOARD_SIZE=10)
        // . . .
        // . . .
        let expected_tile_at_bottom_left = if BOARD_SIZE > 0 {
            game.board.get_tile(BOARD_SIZE - 1, 0)
        } else {
            Tile::Empty
        };
        assert_eq!(
            expected_tile_at_bottom_left,
            Tile::Green,
            "Green tile did not fall to bottom-left as expected"
        );
        assert_eq!(
            game.board.get_tile(0, 0),
            Tile::Empty,
            "Original (0,0) was not cleared"
        );
    }

    #[test]
    fn test_game_process_move_invalid_coords() {
        let mut game = Game::new_with_board(Board::new_empty());
        let move_processed = game.process_move(BOARD_SIZE, BOARD_SIZE); // Out of bounds
        assert!(
            !move_processed,
            "Move with invalid coords should not be processed"
        );
        assert_eq!(game.score(), 0);
        assert_eq!(game.steps(), 0);
        assert_eq!(game.history.len(), 1); // No change
    }

    #[test]
    fn test_game_process_move_no_group() {
        let mut board_rows = vec!["........."; BOARD_SIZE];
        if BOARD_SIZE > 0 {
            board_rows[0] = "R........";
        }
        let board = board_from_str_array(&board_rows).unwrap(); // Single R tile
        let mut game = Game::new_with_board(board);

        let move_processed = game.process_move(0, 0); // Click on the single R
        assert!(
            !move_processed,
            "Move on a single tile (no group) should not be processed"
        );
        assert_eq!(game.score(), 0);
        assert_eq!(game.steps(), 0);
        assert_eq!(game.history.len(), 1);
    }

    #[test]
    fn test_game_undo_last_move() {
        let initial_board = create_board_with_simple_group();
        let mut game = Game::new_with_board(initial_board.clone());

        // Make a move
        let move_processed = game.process_move(0, 0);
        assert!(move_processed);
        let _score_after_move = game.score();
        let _steps_after_move = game.steps();
        let _board_after_move = game.board().clone();
        assert_eq!(game.history.len(), 2);

        // Undo the move
        let undo_successful = game.undo_last_move();
        assert!(undo_successful, "Undo failed");
        assert_eq!(game.score(), 0, "Score after undo is not initial score");
        assert_eq!(game.steps(), 0, "Steps after undo is not initial steps");
        assert_eq!(
            game.board().get_grid(),
            initial_board.get_grid(),
            "Board state after undo is not initial state"
        );
        assert_eq!(
            game.history.len(),
            1,
            "History length after undo is incorrect"
        );

        // Try to undo again (should fail as only initial state is left)
        let undo_again_successful = game.undo_last_move();
        assert!(!undo_again_successful, "Undo on initial state should fail");
        assert_eq!(game.history.len(), 1); // Still at initial state
    }

    #[test]
    fn test_game_undo_multiple_moves() {
        // R R .  (Group 1)
        // G G .  (Group 2)
        let board = board_from_str_array(&[
            "RR.......",
            "GG.......",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
            ".........",
        ])
        .unwrap();
        let initial_board_state = board.clone();
        let mut game = Game::new_with_board(board);

        // Move 1 (Red group at (0,0))
        game.process_move(0, 0);
        let score1 = game.score(); // 20
        let steps1 = game.steps(); // 1
        let board1_state = game.board().clone();
        assert_eq!(game.history.len(), 2);

        // Move 2 (Green group - which would have fallen)
        // After RR is removed, GG at (1,0)(1,1) falls to (say, 9,0)(9,1)
        // Need to find where it lands to click it. For simplicity, let's assume it's findable.
        // This test is more about undo than complex game simulation.
        // Let's find the green group after first move.
        let green_group_after_move1 = game
            .board()
            .find_all_groups()
            .into_iter()
            .find(|g| game.board().get_tile(g[0].0, g[0].1) == Tile::Green);
        assert!(
            green_group_after_move1.is_some(),
            "Green group not found after first move"
        );
        let (gr, gc) = green_group_after_move1.unwrap()[0];

        game.process_move(gr, gc);
        let _score2 = game.score(); // 20 (from red) + 20 (from green) = 40
        let _steps2 = game.steps(); // 2
        assert_eq!(game.history.len(), 3);

        // Undo Move 2
        assert!(game.undo_last_move());
        assert_eq!(game.score(), score1);
        assert_eq!(game.steps(), steps1);
        assert_eq!(game.board().get_grid(), board1_state.get_grid());
        assert_eq!(game.history.len(), 2);

        // Undo Move 1
        assert!(game.undo_last_move());
        assert_eq!(game.score(), 0);
        assert_eq!(game.steps(), 0);
        assert_eq!(game.board().get_grid(), initial_board_state.get_grid());
        assert_eq!(game.history.len(), 1);
    }

    #[test]
    fn test_is_game_over() {
        let board_empty = board_from_str_array(&vec!["........."; BOARD_SIZE]).unwrap();
        let mut game = Game::new_with_board(board_empty.clone());
        assert!(game.is_game_over(), "Empty board should be game over");

        let mut board_single_tile_rows = vec!["........."; BOARD_SIZE];
        if BOARD_SIZE > 0 {
            board_single_tile_rows[0] = "R........";
        }
        let board_single_tile = board_from_str_array(&board_single_tile_rows).unwrap();
        game = Game::new_with_board(board_single_tile.clone());
        assert!(
            game.is_game_over(),
            "Board with only single tiles should be game over"
        );

        let mut board_with_group_rows = vec!["........."; BOARD_SIZE];
        if BOARD_SIZE > 0 {
            board_with_group_rows[0] = "RR.......";
        }
        let board_with_group = board_from_str_array(&board_with_group_rows).unwrap();
        game = Game::new_with_board(board_with_group.clone());
        assert!(
            !game.is_game_over(),
            "Board with a valid group should not be game over"
        );

        game.process_move(0, 0); // Eliminate R R
        assert!(
            game.is_game_over(),
            "Board should be game over after eliminating the only group"
        );
    }

    #[test]
    fn test_final_score() {
        let mut board_one_remaining_rows = vec!["........."; BOARD_SIZE];
        if BOARD_SIZE > 0 {
            board_one_remaining_rows[0] = "R........";
        }
        let board_one_remaining = board_from_str_array(&board_one_remaining_rows).unwrap();
        let mut game = Game::new_with_board(board_one_remaining);
        game.current_score = 100;
        assert_eq!(
            game.final_score(),
            100 + 1980,
            "Final score calculation incorrect"
        );

        let mut ten_tiles_rows = vec!["........."; BOARD_SIZE];
        if BOARD_SIZE > 0 {
            ten_tiles_rows[0] = "RRRRRRRRRR";
        }
        let board_10_tiles = board_from_str_array(&ten_tiles_rows).unwrap();
        game = Game::new_with_board(board_10_tiles);
        game.current_score = 50;
        assert_eq!(
            game.final_score(),
            50,
            "Final score with zero bonus incorrect"
        );
    }
}
