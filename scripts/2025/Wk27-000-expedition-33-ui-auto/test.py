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
            text=True
        ).strip()           # returns 'true' or 'false'
    except Exception:
        orig_anim = None    # gsettings not available, continue silently

    restore_needed = (orig_anim == 'true')
    if restore_needed:
        subprocess.run(
            ["gsettings", "set",
             "org.gnome.desktop.interface", "enable-animations", "false"],
            check=True
        )

    try:
        before = {f.name for f in shots_dir.glob("Screenshot*.png")}
        subprocess.run([
            "gdbus", "call", "--session",
            "--dest", "org.freedesktop.portal.Desktop",
            "--object-path", "/org/freedesktop/portal/desktop",
            "--method", "org.freedesktop.portal.Screenshot.Screenshot",
            "",  "{'interactive': <false>}"
        ], check=True, stdout=subprocess.DEVNULL)

        # wait for the new file and for it to finish writing
        path = None
        for _ in range(20):          # up to 2 s
            time.sleep(0.1)
            new = {f.name for f in shots_dir.glob('Screenshot*.png')} - before
            if new:
                path = shots_dir / max(new)
                # settle loop
                for _ in range(10):
                    s1 = path.stat().st_size
                    time.sleep(0.05)
                    if s1 == path.stat().st_size and s1 > 0:
                        break
                break
        if not path or not path.exists():
            raise RuntimeError("Portal never produced a screenshot")

        img = cv2.imread(str(path))
        try:
            path.unlink()           # keep Pictures clean
        except OSError:
            pass
        if img is None:
            raise RuntimeError(f"Could not read {path}")

        return img

    finally:
        if restore_needed:
            subprocess.run(
                ["gsettings", "set",
                 "org.gnome.desktop.interface", "enable-animations", "true"],
                check=True
            )


def main():
    tmpl = cv2.imread(TEMPLATE, cv2.IMREAD_GRAYSCALE)
    if tmpl is None:
        raise FileNotFoundError(f"Template image not found: {TEMPLATE}")
    tw, th = tmpl.shape[::-1]

    print("Watching for Retry button...")

    while True:
        img = screenshot_ppm()

        gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
        res = cv2.matchTemplate(gray, tmpl, cv2.TM_CCOEFF_NORMED)
        loc = np.where(res >= CONFIDENCE)

        if loc[0].size:
            y, x = int(loc[0][0] + th/2), int(loc[1][0] + tw/2)
            print(f"→ Button detected at ({x}, {y})")
			
            y, x = y // 2, x // 2
            print(f"→ Button (Transformed) detected at ({x}, {y})")

            print(f"→ Button detected at ({x}, {y})")

            ydotool("mousemove", "-a", "-x", str(x), "-y", str(y))
            time.sleep(0.1)
            ydotool("click", "0xC0")
            print("✓ Clicked Retry")

            time.sleep(0.5)  # debounce

        time.sleep(POLL_INTERVAL)

if __name__ == "__main__":
    main()
