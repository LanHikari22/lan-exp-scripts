from evdev import InputDevice, categorize, ecodes, list_devices

# List all input devices
devices = [InputDevice(path) for path in list_devices()]
for dev in devices:
    print(dev.path, dev.name)
