# System reference:
# TAG="ubuntu_25.04" MOUNT="." sh <(curl -sSf https://raw.githubusercontent.com/delta-domain-rnd/delta-box/refs/heads/main/box/box000_blank_system/docker_root_sh.sh)

apt install python3-pip python3-venv ffmpeg
mkdir ~/.venv
python3 -m venv ~/.venv
~/.venv/bin/pip3 install -U --pre "yt-dlp[default]"
export PATH=$PATH:~/.venv/bin
yt-dlp --version

apt install csvkit
~/.venv/bin/pip3 install visidata


