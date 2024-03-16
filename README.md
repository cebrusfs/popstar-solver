PopStar AI
==========

The simple heuristic search solver (a.k.a AI) of the little game on mobile, [popstar](https://play.google.com/store/apps/details?id=com.zplayworld.popstar&hl=en_US).


## Install

```bash
./setup.sh
make
```


## Usage

`color2txt.py` now is hardcoded with the position of screenshot, which is supported on iPhone SE screenshot.

```
./color2txt.py screen_shot.png | depth=4 ./popstar_ai_openmp -
```

### `popstar_ai`

argv[1] is text input file or `-` from `stdin`.


## TODO

1. Remember the best tree to avoid the re-search at the next stage
2. Add good heuristic function to prune the worse tree
3. Improve the data structure of maintaining the game state.
    * Need a good way to maintain the component in dynamicaly.
    * Avoid cache miss
    * support multithread
4.Auto parse the image from different phone's screen-shot or a better way to get the game state.
5. Use Rust with rayon lib to re-implement
