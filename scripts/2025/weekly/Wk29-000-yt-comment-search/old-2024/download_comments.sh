YOUTUBE_URL=$1

yt-dlp --skip-download --write-comments -o "%(title)s.comments.txt" $YOUTUBE_URL
