import os
from typing import Callable, List
from evdev import InputDevice, categorize, ecodes
import subprocess
import time
import checkpipe as pipe

YTOOL = "/home/lan/src/cloned/gh/ReimuNotMoe/ydotool/build/ydotool"
SOCKET = "/home/lan/.ydotool_socket"

INPUT_DEV = os.environ["INPUT_DEV"]
INTERVALS_MS = (
    os.environ["INTERVALS_MS"].split(",").__iter__()
    | pipe.OfIter[str].map(lambda s: int(s))
    | pipe.OfIter[int].to_list()
)

KEY = int(os.environ["KEY"])
ON_KEYS = os.environ["ON_KEYS"].split(",")


def ydotool(*args):
    subprocess.run(
        [YTOOL, *args], env={**os.environ, "YDOTOOL_SOCKET": SOCKET}, check=True
    )


def beep(which=0):
    if which == 0:
        subprocess.run(["aplay", "/usr/share/sounds/sound-icons/glass-water-1.wav"])


def listen_on_key_events_pressed(keycodes: List[str], callback: Callable[[], None]):
    dev = InputDevice(INPUT_DEV)
    print(f"Listening to {dev.name}...")

    for event in dev.read_loop():
        if event.type == ecodes.EV_KEY:
            key_event = categorize(event)
            if key_event.keystate == key_event.key_down:
                if len(keycodes) == 0:
                    print(f"Key pressed: {key_event.keycode}")
                if key_event.keycode in keycodes:
                    callback()


def press_e():
    # E Key
    ydotool("key", f"{KEY}:1")
    ydotool("key", f"{KEY}:0")


def run():
    for interval_ms in INTERVALS_MS:
        if interval_ms != 0:
            press_e()
            time.sleep(interval_ms / 1000)


if __name__ == "__main__":
    listen_on_key_events_pressed(ON_KEYS, run)
