#!/usr/bin/env python3
"""Compare an extracted Lean 4.28.0 Linux release with its pinned archive."""

import argparse
import hashlib
from pathlib import Path, PurePosixPath
import subprocess
import tarfile

from verify_equality_skeleton_portable import LINUX_TREE_SHA256, distribution_digest


ARCHIVE_SHA256 = "ceb3a3f844f7aebf63245e2b51c28d5b0ed38942c19f93cf3febd520302160bd"
PREFIX = "lean-4.28.0-linux/"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--toolchain-root", type=Path, required=True)
    parser.add_argument("--unzstd", default="unzstd", help="Path to the zstd decompressor")
    args = parser.parse_args()

    h = hashlib.sha256()
    with args.archive.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    if h.hexdigest() != ARCHIVE_SHA256:
        raise ValueError("Release archive does not match the published SHA-256")

    process = subprocess.Popen([args.unzstd, "-c", str(args.archive)], stdout=subprocess.PIPE)
    records = {}
    try:
        with tarfile.open(fileobj=process.stdout, mode="r|") as archive:
            for member in archive:
                if member.name.rstrip("/") == PREFIX.rstrip("/"):
                    continue
                if not member.name.startswith(PREFIX):
                    raise ValueError("Unexpected archive root: " + member.name)
                name = member.name[len(PREFIX):].rstrip("/")
                parts = PurePosixPath(name).parts
                if not name or any(part in (".", "..") for part in parts):
                    raise ValueError("Unsafe archive entry: " + member.name)
                if member.isdir():
                    continue
                if name in records:
                    raise ValueError("Duplicate archive entry: " + name)
                if member.isfile():
                    item = hashlib.sha256()
                    stream = archive.extractfile(member)
                    if stream is None:
                        raise ValueError("Unreadable archive entry: " + name)
                    for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                        item.update(chunk)
                    records[name] = ("f", item.hexdigest())
                elif member.issym():
                    records[name] = ("l", member.linkname)
                else:
                    raise ValueError("Unsupported archive entry: " + name)
    except BaseException:
        process.kill()
        process.wait()
        raise
    if process.wait():
        raise RuntimeError("Archive decompression failed")

    aggregate = hashlib.sha256()
    for name, (kind, value) in sorted(records.items()):
        aggregate.update(f"{kind}\0{name}\0{value}\n".encode("utf-8"))
    archived = (aggregate.hexdigest(), len(records))
    installed = distribution_digest(args.toolchain_root.resolve(strict=True))
    if archived[0] != LINUX_TREE_SHA256 or installed != archived:
        raise ValueError("Installed distribution does not match the pinned release archive")
    print("Archive and installed distribution agree:", archived[1], "files and symlinks")
    print("Distribution tree SHA-256:", archived[0])


if __name__ == "__main__":
    main()
