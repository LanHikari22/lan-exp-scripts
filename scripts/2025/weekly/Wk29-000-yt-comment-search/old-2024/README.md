# What is this?

Those are scripts I wrote in 2024 that allows use of `yt-dlp` to get comments for a youtube video and then search them.

# Installation

Reference base Ubuntu 25.04 image:

```sh
TAG="ubuntu_25.04" MOUNT="." sh <(curl -sSf https://raw.githubusercontent.com/delta-domain-rnd/delta-box/refs/heads/main/box/box000_blank_system/docker_root_sh.sh)
```

To run the below commands quickly, check out `ref_install.sh`.

yt-dlp related install:

```sh
apt install python3-pip python3-venv ffmpeg
mkdir ~/.venv
python3 -m venv ~/.venv
export PATH=$PATH:~/.venv/bin
pip3 install -U --pre "yt-dlp[default]"
yt-dlp --version
```

For `grep_comments_yt.sh`:

```sh
apt install csvkit 
~/.venv/bin/pip3 install visidata
```

# Usage

```sh
# to show all comments:
./grep_comments_yt.sh {youtube_url}

# to grep for specific comments:
./grep_comments_yt.sh {youtube_url} "specific"
```

This opens the results to be viewed in visidata.

## On Visidata,

You can word wrap using `v`. If the comment is still too large, do z + Enter and then v in side the new sheet.

# Dependencies

- [yt-dlp](<https://github.com/yt-dlp/yt-dlp>)
