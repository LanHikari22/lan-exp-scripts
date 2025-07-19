script_path=$(realpath "$0")
script_dir=$(dirname "$script_path")

yt_url="$1"
grep_content="$2"
#echo yt_url: "$yt_url"
#echo grep_content: "$grep_content"

# Use capture groups with regex to find the video id
video_id="$(echo "$yt_url" | perl -wne '/\?v=(.*)$/i and print $1')"

if [ -z "$video_id" ]; then
  video_id="$(echo "$yt_url" | perl -wne '/\?v\\=(.*)$/i and print $1')"
fi

# Might be in the format of a short, try again (Though they will likely have no comments anyway...)
if [ -z "$video_id" ]; then
  video_id="$(echo "$yt_url" | perl -wne '/shorts\/(.*)$/i and print $1')"
fi

# Cannot find the video id. Error.
if [ -z "$video_id" ]; then
  echo "could not find video_id for $yt_url. Exiting"
  exit 1
fi

echo video_id: "$video_id"

# grep for a file containing the video id
json_file="$(grep -l "$video_id" *.json)"
echo json_file: $json_file

# The youtube video was not downloaded. Let's download it first.
if [ -z "$json_file" ]; then
  echo "Downloading content for $yt_url"
  $script_dir/download_comments.sh $yt_url
fi

# Get the comments
$script_dir/grep_comments.sh "$json_file" "$grep_content"

#echo $json_file
