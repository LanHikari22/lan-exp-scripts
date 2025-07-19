json_file="$1"
grep_content="$2"

grep_sql_line="-- WHERE text like \"%$grep_content%\""
if [ ! -z "$grep_content" ]; then
  grep_sql_line="WHERE text like \"%$grep_content%\""
fi

sql_query=$(cat <<EOF
CREATE VIEW [Main] AS
  SELECT ROW_NUMBER() OVER (ORDER BY timestamp) as row_id, id, timestamp, _time_text as time, parent, author, like_count, text
  FROM stdin
;

-- Finds out the replies for a given parent. Can be left joined to get this data.
CREATE VIEW [Replies] AS
  SELECT Main.parent as parent_id, count(Main.id) as num_replies, group_concat(Main.id) as reply_ids
  FROM Main
  WHERE parent <> 'root'
  GROUP BY parent
;

-- Provides columns to order by replies to view them
CREATE VIEW [OrderedComments] AS
SELECT 
  Main.id,
  CASE 
    WHEN Main.parent = 'root' THEN Main.row_id
    ELSE (SELECT row_id FROM Main m2 WHERE m2.id = Main.parent)
  END as root_order,
  CASE 
    WHEN Main.parent = 'root' THEN 0
    ELSE Main.row_id
  END as reply_order
FROM Main;

-- Grep
SELECT Main.row_id, Main.id, Main.parent, Main.author, Main.time, Main.like_count, Replies.num_replies, Main.text
  FROM Main
  LEFT JOIN Replies ON Main.id = Replies.parent_id
  LEFT JOIN OrderedComments ON Main.id = OrderedComments.id
  $grep_sql_line
  ORDER BY OrderedComments.root_order, OrderedComments.reply_order;
EOF
)

#echo json_file: "$json_file"
#echo sql_query: "$sql_query"

# Get the comments
comments_csv="$(in2csv --key comments "$json_file")"

if [ -z "$comments_csv" ]; then
  echo "error: no comments could be parsed"
  exit 1
fi


echo "$comments_csv" | csvsql --query "$sql_query" | vd -f csv -
#echo "$comments_csv" | csvsql --query "$sql_query" | tabview -
#echo "$comments_csv" | csvsql --query "$sql_query"
