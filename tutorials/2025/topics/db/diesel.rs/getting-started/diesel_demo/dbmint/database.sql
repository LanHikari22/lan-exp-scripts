CREATE TABLE users (
  id INTEGER PRIMARY KEY,
  username TEXT,
  role TEXT,
  created_at TEXT
);
CREATE TABLE posts (
  id INTEGER PRIMARY KEY,
  title TEXT,
  body TEXT,
  user_id INTEGER,
  status TEXT,
  created_at TEXT
);
CREATE TABLE follows (
  following_user_id INTEGER,
  followed_user_id INTEGER,
  created_at TEXT,
  FOREIGN KEY(following_user_id) REFERENCES users(id),
  FOREIGN KEY(followed_user_id) REFERENCES users(id)
);
CREATE TABLE user_owns_posts (
  id INTEGER PRIMARY KEY,
  user_id INTEGER,
  post_id INTEGER,
  FOREIGN KEY(user_id) REFERENCES users(id),
  FOREIGN KEY(post_id) REFERENCES posts(id)
);

