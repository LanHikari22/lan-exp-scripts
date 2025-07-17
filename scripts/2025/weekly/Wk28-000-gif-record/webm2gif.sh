#!/bin/bash

# Usage: ./webm2gif.sh <webm_path> <start_time> <stop_time>
# Example: ./webm2gif.sh ~/Videos/cast-20250626-173727.webm 00:00:05 00:00:15

in="$1"
start="$2"
stop="$3"
gifout="${in%.webm}.gif"

if [[ -z "$in" || -z "$start" || -z "$stop" ]]; then
  echo "Usage: $0 <webm_path> <start_time> <stop_time>"
  exit 1
fi

# Convert HH:MM:SS to seconds
hms_to_sec() {
  IFS=: read -r h m s <<< "$1"
  echo "$((10#$h * 3600 + 10#$m * 60 + 10#$s))"
}

start_sec=$(hms_to_sec "$start")
stop_sec=$(hms_to_sec "$stop")
duration=$((stop_sec - start_sec))

if (( duration <= 0 )); then
  echo "Invalid time range: stop time must be after start time"
  exit 1
fi

echo "Converting $in to $gifout (from $start to $stop, duration $duration sec)"
ffmpeg -i "$in" -ss "$start" -t "$duration" \
  -vf "fps=10,scale=800:-1:flags=lanczos" -c:v gif "$gifout"

echo "Saved ➜ $gifout"

