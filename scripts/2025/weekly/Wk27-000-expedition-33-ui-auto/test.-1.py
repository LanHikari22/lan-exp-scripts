#!/usr/bin/env python3
import os
import time
import subprocess
import glob
import cv2
import numpy as np
from pathlib import Path

YTOOL = "/home/lan/src/cloned/gh/ReimuNotMoe/ydotool/build/ydotool"
SOCKET = "/home/lan/.ydotool_socket"
TEMPLATE = os.path.join(os.path.dirname(__file__), "retry_button.png")
CONFIDENCE = 0.93
POLL_INTERVAL = 0.25

def ydotool(*args):
    subprocess.run(
        [YTOOL, *args],
        env={**os.environ, "YDOTOOL_SOCKET": SOCKET},
        check=True
    )

def screenshot_ppm():
    subprocess.run([
        "gdbus", "call", "--session",
        "--dest", "org.freedesktop.portal.Desktop",
        "--object-path", "/org/freedesktop/portal/desktop",
        "--method", "org.freedesktop.portal.Screenshot.Screenshot",
        "''", "{}"
    ], check=True)

    time.sleep(1.0)  # allow time for screenshot to save
    pics = sorted(Path.home().joinpath("Pictures").glob("Screenshot*.png"), key=os.path.getmtime)
    if not pics:
        raise RuntimeError("No screenshot found in ~/Pictures")
    return cv2.imread(str(pics[-1]))

def main():
    tmpl = cv2.imread(TEMPLATE, cv2.IMREAD_GRAYSCALE)
    if tmpl is None:
        raise FileNotFoundError(f"Template image not found: {TEMPLATE}")
    tw, th = tmpl.shape[::-1]

    print("Watching for Retry button...")

    while True:
        img = screenshot_ppm()
        img_h, img_w = img.shape[:2]

        screen_w = 1920
        screen_h = 1080
        scale_x = screen_w / img_w
        scale_y = screen_h / img_h

        gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
        res = cv2.matchTemplate(gray, tmpl, cv2.TM_CCOEFF_NORMED)
        loc = np.where(res >= CONFIDENCE)

        if loc[0].size:
            y, x = int(loc[0][0] + th/2), int(loc[1][0] + tw/2)

            print(f"→ Button detected at ({x}, {y})")

            y, x = y // 2, x // 2

            print(f"→ Button (Transformed) detected at ({x}, {y})")

            # raw_y, raw_x = int(loc[0][0] + tw/2), int(loc[1][0] + th/2)
            #x = raw_x // 2
            #y = raw_y // 2

            print(f"→ Button detected at ({x}, {y})")

            ydotool("mousemove", "-a", "-x", str(x), "-y", str(y))
            time.sleep(0.1)
            ydotool("click", "0xC0")
            print("✓ Clicked Retry")

            time.sleep(0.5)  # debounce

        time.sleep(POLL_INTERVAL)

if __name__ == "__main__":
    # ydotool("mousemove", "-a", "-x", "0", "-y", "600")
    main()
