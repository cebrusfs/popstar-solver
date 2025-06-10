use crate::engine::{Board, Tile, BOARD_SIZE};

/// Parses an array of string slices into a `Board` object.
///
/// Each string slice in the input array represents a row on the board.
/// Characters 'R', 'G', 'B', 'Y', 'P' map to their respective `Tile` colors.
/// The character '.' maps to `Tile::Empty`. Any other character will also default to `Tile::Empty`
/// to be lenient, though specific error handling for invalid characters could be added if required.
///
/// # Arguments
/// * `s`: A slice of string slices (`&[&str]`) representing the rows of the board.
///
/// # Returns
/// * `Ok(Board)` if parsing is successful.
/// * `Err(String)` if the number of rows exceeds `BOARD_SIZE`, or if any row's length
///   exceeds `BOARD_SIZE`.
pub fn board_from_str_array(s: &[&str]) -> Result<Board, String> {
    if s.len() > BOARD_SIZE {
        return Err(format!(
            "Invalid number of rows. Expected at most {}, found {}",
            BOARD_SIZE,
            s.len()
        ));
    }

    let mut grid = [[Tile::Empty; BOARD_SIZE]; BOARD_SIZE];

    for (r, row_str) in s.iter().enumerate() {
        if r >= BOARD_SIZE { // Should be caught by the first check, but as a safeguard
            return Err(format!("Too many rows. Maximum is {}", BOARD_SIZE));
        }

        if row_str.chars().count() > BOARD_SIZE {
            return Err(format!(
                "Row {} is too long. Expected at most {} characters, found {}",
                r,
                BOARD_SIZE,
                row_str.chars().count()
            ));
        }

        for (c, char_tile) in row_str.chars().enumerate() {
            // 'c' is index within effective_chars, which is already ensured to be <= BOARD_SIZE
            grid[r][c] = match char_tile {
                'R' => Tile::Red,
                'G' => Tile::Green,
                'B' => Tile::Blue,
                'Y' => Tile::Yellow,
                'P' => Tile::Purple,
                '.' => Tile::Empty,
                _ => return Err(format!("Unrecognized character '{}' in row {} col {}", char_tile, r, c)),
            };
        }
    }
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
            "B"    // Shorter than BOARD_SIZE
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
