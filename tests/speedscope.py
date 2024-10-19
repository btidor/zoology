#!/usr/bin/env python3
"""A helper script for opening profiler traces in speedscope."""

from http.server import HTTPServer, SimpleHTTPRequestHandler
from typing import Any

DIRECTORY = ".profiles/"


# https://stackoverflow.com/a/21957017
class ProfileRequestHandler(SimpleHTTPRequestHandler):
    def __init__(self, *args: Any, **kwargs: Any):
        super().__init__(*args, directory=DIRECTORY, **kwargs)

    def end_headers(self):
        self.send_header("Access-Control-Allow-Origin", "https://www.speedscope.app")
        self.send_header("Cache-Control", "no-cache")
        SimpleHTTPRequestHandler.end_headers(self)

    def do_OPTIONS(self):
        self.send_response(200)
        self.end_headers()


if __name__ == "__main__":
    server = HTTPServer(("", 8000), ProfileRequestHandler)
    print("Serving on 0.0.0.0:8000...")
    server.serve_forever()
