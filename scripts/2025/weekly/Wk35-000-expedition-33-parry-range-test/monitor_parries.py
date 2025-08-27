import os
from typing import Callable, List, Tuple
from evdev import InputDevice, categorize, ecodes
import subprocess
import time
from datetime import datetime, timedelta
import checkpipe as pipe

YTOOL = "/home/lan/src/cloned/gh/ReimuNotMoe/ydotool/build/ydotool"
SOCKET = "/home/lan/.ydotool_socket"

INPUT_DEV = os.environ["INPUT_DEV"]

KEY_RECORD = os.environ["KEY_RECORD"]
ON_KEYS = os.environ["ON_KEYS"].split(",")


def ydotool(*args):
    subprocess.run(
        [YTOOL, *args], env={**os.environ, "YDOTOOL_SOCKET": SOCKET}, check=True
    )


def beep(which=0):
    if which == 0:
        subprocess.run(["aplay", "/usr/share/sounds/sound-icons/glass-water-1.wav"])


def cluster_events(events: List[Tuple[str, datetime]], cluster_period):
    mut_clustered: List[List[Tuple[str, datetime]]] = [[]]

    for keycode, time in events:
        if len(mut_clustered[-1]) == 0:
            mut_clustered[-1].append((keycode, time))
        else:
            delta = time - (mut_clustered[-1][-1][1])

            if delta < cluster_period:
                mut_clustered[-1].append((keycode, time))
            else:
                mut_clustered.append([(keycode, time)])

    return mut_clustered


def is_pause_key(keycode: str):
    return (
        keycode == "KEY_KP6"
        or keycode == "KEY_KP5"
        or keycode == "KEY_2"
        or keycode == "KEY_3"
    )


def is_blank_key(keycode: str):
    return keycode == "KEY_E"


def is_fast_cluster_1(cluster: List[Tuple[str, datetime]]):
    # ..-..-...-
    key_seq = [
        is_pause_key,
        is_pause_key,
        is_blank_key,
        is_pause_key,
        is_pause_key,
        is_blank_key,
        is_pause_key,
        is_pause_key,
        is_pause_key,
        is_blank_key,
    ]

    if len(cluster) != len(key_seq):
        return False

    for i in range(len(cluster)):
        keycode, _ = cluster[i]

        if not key_seq[i](keycode):
            return False

    return True



def record_events(events: List[Tuple[str, datetime]]):
    print('recording...')
    clusters = cluster_events(events, timedelta(seconds=2))

    with open('fast.csv', 'w') as fw:
        fw.write(f'p2,b3,p4,p5,b6,p7,p8,b9\n')

        for cluster in clusters:
            if is_fast_cluster_1(cluster):
                p1 = cluster[0][1]

                p2 = cluster[1][1] - p1
                b3 = cluster[2][1] - p1
                p4 = cluster[3][1] - p1
                p5 = cluster[4][1] - p1
                b6 = cluster[5][1] - p1
                p7 = cluster[6][1] - p1
                p8 = cluster[7][1] - p1
                b9 = cluster[8][1] - p1

                fw.write(f'{p2},{b3},{p4},{p5},{b6},{p7},{p8},{b9}\n')



def listen_on_key_events_pressed(keycodes: List[str]):
    dev = InputDevice(INPUT_DEV)
    print(f"Listening to {dev.name}...")

    mut_events: List[Tuple[str, datetime]] = []

    for event in dev.read_loop():
        if event.type == ecodes.EV_KEY:
            key_event = categorize(event)
            if key_event.keystate == key_event.key_down:
                if len(keycodes) == 0 or key_event.keycode in keycodes:
                    mut_events.append((key_event.keycode, datetime.now()))
                    print(f"{datetime.now()} Pressed {key_event.keycode}")
                elif key_event.keycode == KEY_RECORD:
                    record_events(mut_events)


if __name__ == "__main__":
    listen_on_key_events_pressed(ON_KEYS)
