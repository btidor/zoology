#!/usr/bin/env python3
# type: ignore
"""A helper script for opening profiler traces in speedscope."""

import contextlib
import socket
import webbrowser
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer


# https://stackoverflow.com/a/21957017
class CORSRequestHandler(SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header("Access-Control-Allow-Origin", "https://www.speedscope.app")
        self.send_header("Cache-Control", "no-cache")
        SimpleHTTPRequestHandler.end_headers(self)

    def do_OPTIONS(self):
        self.send_response(200)
        self.end_headers()


# https://github.com/python/cpython/blob/a286caa937/Lib/http/server.py#L1297-L1308
class DualStackServer(ThreadingHTTPServer):
    def server_bind(self) -> None:
        # suppress exception when protocol is IPv4
        with contextlib.suppress(Exception):
            self.socket.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_V6ONLY, 0)
        return super().server_bind()

    def finish_request(self, request, client_address):
        self.RequestHandlerClass(request, client_address, self, directory=".profiles/")


if __name__ == "__main__":
    server = DualStackServer(("", 8000), CORSRequestHandler)
    print("Serving on 0.0.0.0:8000...")
    webbrowser.open(
        f"https://www.speedscope.app/#profileURL=http://localhost:8000/combined.json"
    )
    server.serve_forever()
