#!/bin/bash

# System reference:
# TAG="ubuntu_25.04" MOUNT="." sh <(curl -sSf https://raw.githubusercontent.com/delta-domain-rnd/delta-box/refs/heads/main/box/box000_blank_system/docker_root_bash.sh)

apt install -y python3-pip python3-venv ffmpeg
mkdir ~/.venv
python3 -m venv ~/.venv
~/.venv/bin/pip3 install -U --pre "yt-dlp[default]"

apt install -y csvkit
~/.venv/bin/pip3 install visidata

echo "PATH=$PATH:~/.venv/bin" >> /etc/profile
source /etc/profile
yt-dlp --version
cd /mnt/

echo "To start searching youtube videos for comments, do"
echo "./grep_comments_yt.sh {youtube_url} {text_to_search}"
echo "You do not need to provide text_to_search, it will show all text in visidata and it can still be filtered there."
echo "NOTE: You may need to Ctrl+C if it hangs in download after Extracted X comments. Then run the command again."
echo "CTRL+D twice to leave."

bash
