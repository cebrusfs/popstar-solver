import re

with open('src/bin/arena.rs', 'r') as f:
    content = f.read()

# Replace rollout_board.color_at(pos.0, pos.1) with rollout_board.get_tile(pos.0, pos.1) as u8
content = content.replace("color_at", "get_tile")
content = content.replace("== self.target_color", "as u8 == self.target_color")

with open('src/bin/arena.rs', 'w') as f:
    f.write(content)

