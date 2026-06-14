#!/usr/bin/env python3
import sys
import argparse
import math
from PIL import Image

# Known popstar colors (approximate RGB centroids)
COLORS = {
    'R': (220, 50, 50),
    'G': (50, 200, 50),
    'B': (50, 100, 220),
    'Y': (220, 200, 50),
    'P': (200, 80, 200),
    '.': (20, 20, 20), # Empty background (dark)
}

def color_distance(c1, c2):
    # Euclidean distance in RGB space
    return math.sqrt(sum((a - b) ** 2 for a, b in zip(c1[:3], c2[:3])))

def closest_color(pixel):
    best_char = '.'
    min_dist = float('inf')
    for char, centroid in COLORS.items():
        dist = color_distance(pixel, centroid)
        if dist < min_dist:
            min_dist = dist
            best_char = char
    return best_char

def parse_args():
    parser = argparse.ArgumentParser(description="Convert PopStar screenshot to 10x10 text grid")
    parser.add_argument("image_path", help="Path to the screenshot image")
    parser.add_argument("--bottom-margin", type=int, default=0, 
                        help="Pixels from the bottom of the screen to the bottom of the grid (for modern iPhones with home indicator)")
    return parser.parse_args()

def main():
    args = parse_args()
    
    try:
        im = Image.open(args.image_path)
    except Exception as e:
        print(f"Error opening image: {e}", file=sys.stderr)
        sys.exit(1)

    im = im.convert('RGB')
    width = im.width
    height = im.height

    # Popstar grid is usually a perfect square spanning the full width of the screen.
    grid_size = width
    block_size = grid_size / 10.0
    
    # Calculate top crop position
    # The grid is usually at the bottom of the screen. 
    top = height - args.bottom_margin - grid_size

    if top < 0:
        print("Error: Computed crop area is outside the image. Check bottom margin and image dimensions.", file=sys.stderr)
        sys.exit(1)

    mp = []
    offset = block_size / 2.0

    for i in range(10):
        row_str = ""
        for j in range(10):
            # Calculate pixel coordinate to sample (center of the block)
            x = int(j * block_size + offset)
            y = int(top + i * block_size + offset)
            
            # Ensure within bounds
            x = min(max(x, 0), width - 1)
            y = min(max(y, 0), height - 1)
            
            pixel = im.getpixel((x, y))
            char = closest_color(pixel)
            row_str += char
        mp.append(row_str)

    print('\n'.join(mp))

if __name__ == "__main__":
    main()
