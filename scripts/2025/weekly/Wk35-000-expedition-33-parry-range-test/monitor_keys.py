import os
from typing import Callable, List
from evdev import InputDevice, categorize, ecodes
import subprocess
import time
from datetime import datetime
import checkpipe as pipe

YTOOL = "/home/lan/src/cloned/gh/ReimuNotMoe/ydotool/build/ydotool"
SOCKET = "/home/lan/.ydotool_socket"

INPUT_DEV = os.environ["INPUT_DEV"]

ON_KEYS = os.environ["ON_KEYS"].split(",")


def ydotool(*args):
    subprocess.run(
        [YTOOL, *args], env={**os.environ, "YDOTOOL_SOCKET": SOCKET}, check=True
    )


def beep(which=0):
    if which == 0:
        subprocess.run(["aplay", "/usr/share/sounds/sound-icons/glass-water-1.wav"])


def listen_on_key_events_pressed(keycodes: List[str]):
    dev = InputDevice(INPUT_DEV)
    print(f"Listening to {dev.name}...")

    for event in dev.read_loop():
        if event.type == ecodes.EV_KEY:
            key_event = categorize(event)
            if key_event.keystate == key_event.key_down:
                if len(keycodes) == 0 or key_event.keycode in keycodes:
                    print(f"{datetime.now()} Pressed {key_event.keycode}")


if __name__ == "__main__":
    listen_on_key_events_pressed(ON_KEYS)
