use crate::engine::{Board, Tile, BOARD_SIZE};

/// Parses an array of string slices into a `Board` object.
///
/// Each string slice in the input array represents a row on the board, starting from row 0.
/// The board is assumed to be `BOARD_SIZE` x `BOARD_SIZE`.
/// If fewer than `BOARD_SIZE` rows are provided, the remaining rows are filled with `Tile::Empty`.
/// Similarly, if a row string is shorter than `BOARD_SIZE` characters, the rest of that
/// row is filled with `Tile::Empty`.
///
/// Valid characters for tiles are:
/// - 'R': `Tile::Red`
/// - 'G': `Tile::Green`
/// - 'B': `Tile::Blue`
/// - 'Y': `Tile::Yellow`
/// - 'P': `Tile::Purple`
/// - '.': `Tile::Empty`
///
/// Any other character will result in an error.
///
/// # Arguments
/// * `s`: A slice of string slices (`&[&str]`) representing the rows of the board.
///   Each string slice corresponds to a row, starting from the top (row 0).
///
/// # Returns
/// * `Ok(Board)` if parsing is successful. The returned `Board` will be fully initialized,
///   with unspecified parts of the grid (due to short input) defaulted to `Tile::Empty`.
/// * `Err(String)` if:
///     - The number of rows in `s` exceeds `BOARD_SIZE`.
///     - Any row string's character length exceeds `BOARD_SIZE`.
///     - An unrecognized character (not in `['R', 'G', 'B', 'Y', 'P', '.']`) is encountered.
///
/// # Examples
/// ```
/// use popstar_solver::utils::board_from_str_array;
/// use popstar_solver::engine::{Board, Tile, BOARD_SIZE};
///
/// let board_str = [
///     "RGY", // Row 0
///     "B.P", // Row 1
/// ];
/// let result = board_from_str_array(&board_str);
/// assert!(result.is_ok());
/// let board = result.unwrap();
/// assert_eq!(board.get_tile(0, 0), Tile::Red);
/// assert_eq!(board.get_tile(0, 1), Tile::Green);
/// assert_eq!(board.get_tile(0, 2), Tile::Yellow);
/// if BOARD_SIZE > 3 {
///     assert_eq!(board.get_tile(0, 3), Tile::Empty); // Rest of row 0 is empty
/// }
/// assert_eq!(board.get_tile(1, 0), Tile::Blue);
/// assert_eq!(board.get_tile(1, 1), Tile::Empty);
/// assert_eq!(board.get_tile(1, 2), Tile::Purple);
/// if BOARD_SIZE > 2 { // If board has more than 2 rows
///     assert_eq!(board.get_tile(2, 0), Tile::Empty); // Row 2 is entirely empty
/// }
///
/// let invalid_char_str = ["RXB"];
/// assert!(board_from_str_array(&invalid_char_str).is_err());
///
/// let too_many_rows_str = vec!["R"; BOARD_SIZE + 1];
/// let too_many_rows_slices: Vec<&str> = too_many_rows_str.iter().map(AsRef::as_ref).collect();
/// assert!(board_from_str_array(&too_many_rows_slices).is_err());
/// ```
pub fn board_from_str_array(s: &[&str]) -> Result<Board, String> {
    // Check if the number of provided rows exceeds the board's capacity.
    if s.len() > BOARD_SIZE {
        return Err(format!(
            "Invalid number of rows. Expected at most {}, found {}",
            BOARD_SIZE,
            s.len()
        ));
    }

    let mut grid = [[Tile::Empty; BOARD_SIZE]; BOARD_SIZE]; // Initialize with all empty tiles.

    // Iterate over the provided string slices, each representing a row.
    for (r, row_str) in s.iter().enumerate() {
        // This check is technically redundant due to the initial s.len() check,
        // but kept as a safeguard or for clarity if the logic were to change.
        // if r >= BOARD_SIZE { break; } // No longer needed due to initial check

        // Check if any individual row string is too long.
        if row_str.chars().count() > BOARD_SIZE {
            return Err(format!(
                "Row {} is too long. Expected at most {} characters, found {}",
                r,
                BOARD_SIZE,
                row_str.chars().count()
            ));
        }

        // Populate the grid row by character.
        for (c, char_tile) in row_str.chars().enumerate() {
            // `c` is the column index. If `row_str` is shorter than `BOARD_SIZE`,
            // remaining cells in this grid row will keep their `Tile::Empty` default.
            grid[r][c] = match char_tile {
                'R' => Tile::Red,
                'G' => Tile::Green,
                'B' => Tile::Blue,
                'Y' => Tile::Yellow,
                'P' => Tile::Purple,
                '.' => Tile::Empty,
                _ => {
                    return Err(format!(
                        "Unrecognized character '{}' in row {} col {}",
                        char_tile, r, c
                    ))
                }
            };
        }
    }
    // If fewer than BOARD_SIZE rows were in `s`, the remaining rows in `grid`
    // are already `Tile::Empty` due to the initial `grid` declaration.
    Ok(Board::from_grid(grid))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::{Tile, BOARD_SIZE};

    #[test]
    fn test_board_from_str_array_valid() {
        let board_str = [
            "RGYBPPBYGR",
            "..........",
            "RGYBPPBYGR",
            "..........",
            "RGYBPPBYGR",
            "..........",
            "RGYBPPBYGR",
            "..........",
            "RGYBPPBYGR",
            "..........",
        ];
        let board = board_from_str_array(&board_str).unwrap();
        assert_eq!(board.get_tile(0, 0), Tile::Red);
        assert_eq!(board.get_tile(1, 0), Tile::Empty);
    }

    #[test]
    fn test_board_from_str_array_invalid_char() {
        let board_str = ["RGYBPPBYGX"]; // X is invalid
        let result = board_from_str_array(&board_str);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Unrecognized character 'X'"));
    }

    #[test]
    fn test_board_from_str_array_with_spaces() {
        let board_str = ["R G Y B P"]; // Contains spaces
        let result = board_from_str_array(&board_str);
        assert!(result.is_err());
        // This will now fail due to ' ' being an unrecognized character.
        assert!(result.unwrap_err().contains("Unrecognized character ' '"));
    }

    #[test]
    fn test_board_from_str_array_row_too_long() {
        let too_long_row = "R".repeat(BOARD_SIZE + 1);
        let board_str = [too_long_row.as_str()];
        let result = board_from_str_array(&board_str);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Row 0 is too long"));
    }

    #[test]
    fn test_board_from_str_array_too_many_rows() {
        let mut rows = Vec::new();
        for _ in 0..=BOARD_SIZE {
            rows.push("R.........");
        }
        let result = board_from_str_array(&rows);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Invalid number of rows"));
    }

    #[test]
    fn test_board_from_str_array_empty_input() {
        let board_str: [&str; 0] = [];
        let board = board_from_str_array(&board_str).unwrap();
        for r in 0..BOARD_SIZE {
            for c in 0..BOARD_SIZE {
                assert_eq!(board.get_tile(r, c), Tile::Empty);
            }
        }
    }

    #[test]
    fn test_board_from_str_array_partial_rows_and_cols() {
        let board_str = [
            "RGY", // Shorter than BOARD_SIZE
            "B",   // Shorter than BOARD_SIZE
        ];
        let board = board_from_str_array(&board_str).unwrap();
        assert_eq!(board.get_tile(0, 0), Tile::Red);
        assert_eq!(board.get_tile(0, 1), Tile::Green);
        assert_eq!(board.get_tile(0, 2), Tile::Yellow);
        if BOARD_SIZE > 3 {
            assert_eq!(board.get_tile(0, 3), Tile::Empty);
        }
        assert_eq!(board.get_tile(1, 0), Tile::Blue);
        if BOARD_SIZE > 1 {
            assert_eq!(board.get_tile(1, 1), Tile::Empty);
        }
        if BOARD_SIZE > 2 {
            assert_eq!(board.get_tile(2, 0), Tile::Empty); // Next row should be empty
        }
    }
}
