"""Reproduce the finite relay intervention in the causal-finitism investigation."""

import os
import secrets
import signal
import socket
import subprocess
import tempfile
from contextlib import ExitStack


def observe(receiver, feed_depth, cut=None, *, isolate_feed=False, buffered=False, bypass=False):
    """Return the complete output of seven cat processes and the post-cut token."""
    start = receiver.tell()
    with ExitStack() as processes, ExitStack() as links:
        def channel():
            reader, writer = socket.socketpair()
            return links.enter_context(reader), links.enter_context(writer)

        edges = [channel() for _ in range(6)]
        feed_reader, feed_writer = channel()
        stages = []
        for depth in range(7):
            incoming = edges[depth][0] if depth < len(edges) else subprocess.DEVNULL
            if depth == feed_depth:
                incoming = feed_reader
            outgoing = edges[depth - 1][1] if depth else receiver
            stages.append(processes.enter_context(
                subprocess.Popen(["cat"], stdin=incoming, stdout=outgoing)
            ))
        if buffered:
            edges[0][1].sendall(b"earlier")
        if cut is not None:
            edges[cut][1].shutdown(socket.SHUT_WR)
        if isolate_feed:
            feed_writer.shutdown(socket.SHUT_WR)
        token = secrets.token_hex(16).encode("ascii")
        if bypass:
            try:
                edges[0][1].sendall(token)
            except BrokenPipeError:
                if cut != 0:
                    raise
        try:
            feed_writer.sendall(token)
        except BrokenPipeError:
            if not isolate_feed:
                raise
        else:
            assert not isolate_feed
    # All senders are closed and every process has exited. Read the whole trial
    # from the same open receiver without moving its shared write offset.
    for stage in stages:
        if stage.returncode not in (0, -signal.SIGPIPE):
            raise RuntimeError(f"cat exited with {stage.returncode}")
    return os.pread(receiver.fileno(), receiver.tell() - start, start), token


def main():
    with tempfile.TemporaryFile() as receiver:
        for depth in (0, 2, 5, 6):
            received, token = observe(receiver, depth)
            assert received == token
            outcomes = []
            for cut in range(6):
                received, token = observe(receiver, depth, cut)
                assert received == (token if depth <= cut else b"")
                outcomes.append(int(received == token))
            print(f"feed at {depth}, cuts 0 through 5: {outcomes}")

        received, _ = observe(receiver, 2, 2, isolate_feed=True)
        assert received == b""
        received, token = observe(receiver, 6, 3, buffered=True)
        assert received == b"earlier" and token not in received
        received, token = observe(receiver, 6, 3, isolate_feed=True, bypass=True)
        assert received == token
        print("Isolating feed 2 after cut 2 stopped its output. Cut 3 passed the buffer and bypass controls.")

        # Both arrangements have the side writer through link 0. The second
        # also sends the same fresh token from depth 4.
        counts = []
        for isolate_feed in (True, False):
            row = []
            for cut in range(6):
                received, token = observe(receiver, 4, cut, isolate_feed=isolate_feed, bypass=True)
                count = received.count(token)
                assert received == token * count
                row.append(count)
            counts.append(row)
        assert counts == [[0, 1, 1, 1, 1, 1], [0, 1, 1, 1, 2, 2]]
        print(f"One and two live inputs, copies at the receiver: {counts}")


if __name__ == "__main__":
    main()
