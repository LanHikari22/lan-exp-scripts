#!/usr/bin/env python3

import time
from Xlib import X, display
from Xlib.ext import shape

# ── connect to X ────────────────────────────────────────────────────────
d     = display.Display()
root  = d.screen().root

# ── create a 1×1 override-redirect window (never gets focus) ────────────
win = root.create_window(
    0, 0,                   # x, y
    1, 1,                   # width, height
    0,                      # border width
    X.CopyFromParent,       # depth
    X.InputOutput,          # class
    X.CopyFromParent,       # visual
    override_redirect=True  # attribute via kw-arg
)

# ── make it click-through using the Shape extension ─────────────────────
empty = root.create_pixmap(1, 1, 1)        # 1-bit dummy pixmap
win.shape_mask(shape.SO.Set, shape.SK.Input, 0, 0, empty)

# ── show for 100 ms, then destroy ───────────────────────────────────────
win.map()
d.flush()
time.sleep(0.1)
win.unmap()
win.destroy()
d.flush()
