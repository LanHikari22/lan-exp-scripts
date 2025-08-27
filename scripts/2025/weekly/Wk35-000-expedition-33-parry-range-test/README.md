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
INPUT_DEV='/dev/input/event{N}' KEYS="KEY_KP6,KEY_2" INTERVALS_MS="1000, 1300, 2000" python3 run_sequence.py
```

You can find out which event{N} via `check_input_devices.py`.


This will listen
