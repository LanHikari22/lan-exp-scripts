#!/usr/bin/env python3
import os, time, subprocess, tempfile, cv2, numpy as np

# ❶ grab a frame via the portal ---------------------------------
def screenshot_ppm():
    handle = subprocess.check_output([
        'dbus-send', '--session', '--print-reply',
        '--dest=org.freedesktop.portal.Desktop',
        '/org/freedesktop/portal/desktop',
        'org.freedesktop.portal.Screenshot.Screenshot',
        'boolean:false', 'a{sv}:'
    ]).decode()
    uri = handle.split('file://')[1].split("'")[0]
    return cv2.imread(uri)

# ❷ load reference once
tmpl = cv2.imread('retry_button.png', cv2.IMREAD_GRAYSCALE)
th, tw = tmpl.shape[::-1]

# ❸ event loop ---------------------------------------------------
while True:
    gray = cv2.cvtColor(screenshot_ppm(), cv2.COLOR_BGR2GRAY)
    res  = cv2.matchTemplate(gray, tmpl, cv2.TM_CCOEFF_NORMED)
    loc  = np.where(res >= 0.93)
    if loc[0].size:
        y, x = int(loc[0][0] + th/2), int(loc[1][0] + tw/2)
        subprocess.run(['ydotool', 'mousemove', str(x), str(y)])
        subprocess.run(['ydotool', 'click', '1'])
        time.sleep(0.4)                # small debounce
    time.sleep(0.1)
