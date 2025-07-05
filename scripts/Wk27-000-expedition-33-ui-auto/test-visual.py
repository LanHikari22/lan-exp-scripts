#!/usr/bin/env python3

#!/usr/bin/env python3
# pip install python-xlib pycairo

import time, cairo
from Xlib import X, display, Xatom
from Xlib.ext import shape

_disp   = display.Display()
_root   = _disp.screen().root
_OPACITY = _disp.intern_atom('_NET_WM_WINDOW_OPACITY')

# ── find a 32-bit ARGB visual ───────────────────────────────────────────
screen = _disp.screen()
visual = None
for d in screen.allowed_depths:
    if d.depth == 32:
        visual = d.visuals[0]
        break
if not visual:
    raise RuntimeError("No 32-bit ARGB visual found (need compositing WM)")

def flash_box(x, y, w, h,
              colour=(255, 0, 0),      # RGB 0-255
              alpha=0.35,              # 0-1
              duration=0.25):          # seconds
    """
    Translucent rectangle overlay at (x, y, w, h) for `duration` seconds.
    Input-transparent; does not steal focus.
    """

    # ⚠️ FIX: pass visual ID, not the Visual object
    colormap = _root.create_colormap(visual.visualid, X.AllocNone)

    win = _root.create_window(
        x, y, w, h, 0, visual.depth, X.InputOutput, visual,
        X.CWColormap | X.CWOverrideRedirect,
        {
            'colormap': colormap,
            'override_redirect': True
        }
    )

    # make window click-through
    empty = _root.create_pixmap(1, 1, 1)
    win.shape_mask(shape.SO.Set, shape.SK.Input, 0, 0, empty)

    # set overall opacity (fallback)
    win.change_property(_OPACITY, Xatom.CARDINAL, 32,
                        [int(alpha * 0xFFFFFFFF)])

    # paint RGBA rectangle
    surface = cairo.XCBSurface(_disp._display, win.id, visual, w, h)
    ctx = cairo.Context(surface)
    ctx.set_source_rgba(colour[0]/255, colour[1]/255, colour[2]/255, alpha)
    ctx.rectangle(0, 0, w, h)
    ctx.fill()

    win.map()
    _disp.flush()

    time.sleep(duration)

    win.unmap()
    win.destroy()
    _disp.flush()


# quick self-test
if __name__ == "__main__":
    flash_box(400, 400, 220, 120, (0, 128, 255), 0.4, 0.6)

