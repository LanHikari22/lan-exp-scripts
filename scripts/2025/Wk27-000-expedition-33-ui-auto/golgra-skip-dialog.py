#!/usr/bin/env python3
import os
import time
import subprocess
import glob
from typing import Callable
import cv2
import numpy as np
from pathlib import Path

YTOOL = "/home/lan/src/cloned/gh/ReimuNotMoe/ydotool/build/ydotool"
SOCKET = "/home/lan/.ydotool_socket"
TEMPLATE = os.path.join(os.path.dirname(__file__), "golgra-as-expected-dialog.png")
CONFIDENCE = 0.93
POLL_INTERVAL = 0.25


def ydotool(*args):
    subprocess.run(
        [YTOOL, *args], env={**os.environ, "YDOTOOL_SOCKET": SOCKET}, check=True
    )


def beep():
    subprocess.run(["aplay", "/usr/share/sounds/sound-icons/glass-water-1.wav"])


def take_screenshot():
    """
    Take a portal screenshot with animations temporarily disabled so the
    white flash never appears.  The original setting is restored afterward.
    """
    import subprocess, time, os
    from pathlib import Path

    shots_dir = Path.home() / "Pictures"

    try:
        orig_anim = subprocess.check_output(
            ["gsettings", "get", "org.gnome.desktop.interface", "enable-animations"],
            text=True,
        ).strip()  # returns 'true' or 'false'
    except Exception as e:
        # orig_anim = None  # gsettings not available, continue silently
        raise Exception(f"Setting Gsettings failed: {e}")

    restore_needed = orig_anim == "true"
    if restore_needed:
        subprocess.run(
            [
                "gsettings",
                "set",
                "org.gnome.desktop.interface",
                "enable-animations",
                "false",
            ],
            check=True,
        )

    try:
        before = {f.name for f in shots_dir.glob("Screenshot*.png")}
        subprocess.run(
            [
                "gdbus",
                "call",
                "--session",
                "--dest",
                "org.freedesktop.portal.Desktop",
                "--object-path",
                "/org/freedesktop/portal/desktop",
                "--method",
                "org.freedesktop.portal.Screenshot.Screenshot",
                "",
                "{'interactive': <false>}",
            ],
            check=True,
            stdout=subprocess.DEVNULL,
        )

        path = None
        for _ in range(20):
            time.sleep(0.1)
            new = {f.name for f in shots_dir.glob("Screenshot*.png")} - before
            if new:
                path = shots_dir / max(new)
                for _ in range(10):
                    s1 = path.stat().st_size
                    time.sleep(0.05)
                    if s1 == path.stat().st_size and s1 > 0:
                        break
                break
        if not path or not path.exists():
            raise RuntimeError("Portal never produced a screenshot")

        time.sleep(2.0)
        img = cv2.imread(str(path))

        try:
            path.unlink()
        except OSError:
            pass

        if img is None:
            raise RuntimeError(f"img is None. Could not read {path}")

        return img

    finally:
        if restore_needed:
            subprocess.run(
                [
                    "gsettings",
                    "set",
                    "org.gnome.desktop.interface",
                    "enable-animations",
                    "true",
                ],
                check=True,
            )


def on_visual_cue(x: int, y: int) -> None:
    print("VISUAL CUE DETECTED!")

    beep()

    # You lost. Skip dialog.

    # send the letter F  (key-code 33 = KEY_F)
    ydotool("key", "33:1")
    ydotool("key", "33:0")

    # Wait for screen fade
    time.sleep(1.2)

    # Go to Golgra

    # # KEY_W = 17  (see /usr/include/linux/input-event-codes.h)
    ydotool("key", "17:1")
    time.sleep(1.3)
    ydotool("key", "17:0")
    time.sleep(0.3)

    # Talk to Golgra

    # E Key
    ydotool("key", "18:1")
    ydotool("key", "18:0")
    time.sleep(0.3)

    # Skip Hi

    # F Key
    ydotool("key", "33:1")
    ydotool("key", "33:0")
    time.sleep(0.3)

    # Choose final dialog option

    # W Key
    ydotool("key", "17:1")
    ydotool("key", "17:0")
    time.sleep(0.3)

    # F Key
    ydotool("key", "33:1")
    ydotool("key", "33:0")
    time.sleep(0.3)

    # Golgra: Really? A Duel?

    # F Key
    ydotool("key", "33:1")
    ydotool("key", "33:0")
    time.sleep(0.3)

    # Select Fighter

    # A Key
    ydotool("key", "30:1")
    ydotool("key", "30:0")
    time.sleep(0.3)

    # Hold ENTER Key
    ydotool("key", "28:1")
    time.sleep(1.0)
    ydotool("key", "28:0")



def event_loop_for_visual_cue(on_visual_cue_callback: Callable[[int, int], None]):
    tmpl = cv2.imread(TEMPLATE, cv2.IMREAD_GRAYSCALE)
    if tmpl is None:
        raise FileNotFoundError(f"Template image not found: {TEMPLATE}")
    tw, th = tmpl.shape[::-1]

    print("Watching for Golgra Chat...")

    while True:
        img = take_screenshot()

        gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
        res = cv2.matchTemplate(gray, tmpl, cv2.TM_CCOEFF_NORMED)
        loc = np.where(res >= CONFIDENCE)

        if loc[0].size:
            y, x = int(loc[0][0] + th / 2), int(loc[1][0] + tw / 2)
            print(f"→ Visual detected at ({x}, {y})")

            y, x = y // 2, x // 2
            # print(f"→ Visual (Transformed) detected at ({x}, {y})")

            on_visual_cue_callback(x, y)

            time.sleep(0.5)  # debounce

        time.sleep(POLL_INTERVAL)


def main():
    event_loop_for_visual_cue(on_visual_cue)


if __name__ == "__main__":
    main()
