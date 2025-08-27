# Setup

We need the ydotoold tool running.

For example in my case:

```sh
cd ~/src/cloned/gh/ReimuNotMoe/ydotool/build
./ydotoold --socket-path="$HOME/.ydotool_socket"
```


# Running

Example:

```sh
INPUT_DEV='/dev/input/event{N}' ON_KEYS="KEY_KP6,KEY_2" KEY='18' INTERVALS_MS="1000,1300,2000" python3 run_sequence.py
```

You can find out which event{N} via `check_input_devices.py`.

This will listen for key code strings defined in `ON_KEYS`, and then execute the key specified by `KEY` for `len(INTERVALS_MS)` times.

`INTERVALS_MS` is a comma separated list of millisecond intervals to press the chosen `KEY`.

`KEY` should be a key code. For available options, see [keycodes](https://pickpj.github.io/keycodes.html).
