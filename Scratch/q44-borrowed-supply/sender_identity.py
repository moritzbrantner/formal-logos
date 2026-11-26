"""Identify which live writer used a shared Linux datagram socket in one trial."""

import os
import secrets
import socket
import struct
import subprocess
import sys
from contextlib import ExitStack


def write_one(fd):
    with socket.socket(fileno=fd) as sender:
        token = sys.stdin.buffer.readline().rstrip(b"\n")
        sender.send(token)


def receive_from(receiver, expected_token):
    credentials = struct.Struct("3i")
    payload, messages, flags, _ = receiver.recvmsg(256, socket.CMSG_SPACE(credentials.size))
    assert payload == expected_token and not flags & socket.MSG_CTRUNC
    [(pid, uid, _)] = [
        credentials.unpack(data) for level, kind, data in messages
        if level == socket.SOL_SOCKET and kind == socket.SCM_CREDENTIALS
    ]
    assert uid == os.getuid()
    return pid


def run_trial():
    with ExitStack() as scope:
        receiver, sender = socket.socketpair(socket.AF_UNIX, socket.SOCK_DGRAM)
        scope.enter_context(receiver)
        scope.enter_context(sender)
        receiver.setsockopt(socket.SOL_SOCKET, socket.SO_PASSCRED, 1)
        receiver.settimeout(5)
        writers = [
            scope.enter_context(subprocess.Popen(
                [sys.executable, __file__, str(sender.fileno())],
                pass_fds=(sender.fileno(),), stdin=subprocess.PIPE,
            ))
            for _ in range(2)
        ]
        sender.close()
        for index, writer in enumerate(writers):
            token = secrets.token_hex(16).encode()
            writer.communicate(token + b"\n", timeout=5)
            assert writer.returncode == 0
            observed = receive_from(receiver, token)
            assert observed == writer.pid
            if index == 1:
                assert writers[0].returncode == 0 and observed != writers[0].pid
            print(f"writer {index + 1}: fresh datagram identified by PID {observed}")
        receiver.setblocking(False)
        try:
            receiver.recv(256)
        except BlockingIOError:
            return
        raise AssertionError("unexpected queued datagram after both trials")


if __name__ == "__main__":
    if len(sys.argv) == 2:
        write_one(int(sys.argv[1]))
    else:
        run_trial()
