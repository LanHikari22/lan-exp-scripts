export var m_connected: boolean = false;

export function connect(server: string, port: number, on_message: (event: MessageEvent<any>) => void): WebSocket {
  // Create WebSocket connection.
  const socket = new WebSocket(`ws://${server}:${port}`);

  socket.addEventListener("open", (_event) => {
    console.log("webio: open")
    m_connected = true;
  });

  socket.addEventListener("close", (_event) => {
    console.log("webio: close")
    m_connected = false;
  });

  socket.addEventListener("error", (event) => {
    console.log(`webio encountered an error: ${event}`);
  });

  socket.addEventListener("message", (event) => {
    // console.log("Message from server ", event.data);
    on_message(event);
  });

  return socket;
}

export function start_client_demo() {
  // Create WebSocket connection.
  const socket = new WebSocket("ws://localhost:3003");

  // Connection opened
  socket.addEventListener("open", (event) => {
    // console.log("It openeddd");
    m_connected = true;
    // socket.send("Hello Server!");
  });

  // Listen for messages
  socket.addEventListener("message", (event) => {
    console.log("Message from server ", event.data);
  });
}