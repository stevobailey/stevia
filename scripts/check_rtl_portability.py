#!/usr/bin/env python3
import argparse
import os
import re
import subprocess
from pathlib import Path


RULES = (
    (
        "parameterized data types",
        re.compile(r"\bparameter\s+type\b"),
        "Use WIDTH plus packed logic ports in reusable primitives.",
    ),
    (
        "SystemVerilog interfaces",
        re.compile(r"^\s*interface\b"),
        "Use explicit module ports in reusable primitives.",
    ),
)


def traced_sources(filelist):
    repo_root = Path(os.environ.get("STEVIA_ROOT", filelist.parents[1])).resolve()
    env = os.environ.copy()
    env["STEVIA_ROOT"] = str(repo_root)
    result = subprocess.run(
        ["python3", str(repo_root / "scripts/trace_filelist.py"), str(filelist)],
        check=True,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
    )
    return [Path(line) for line in result.stdout.splitlines() if line.strip()]


def strip_block_comments(line, in_block_comment):
    output = ""
    index = 0
    while index < len(line):
        if in_block_comment:
            end = line.find("*/", index)
            if end == -1:
                return output, True
            index = end + 2
            in_block_comment = False
        else:
            start = line.find("/*", index)
            if start == -1:
                output += line[index:]
                return output, False
            output += line[index:start]
            index = start + 2
            in_block_comment = True
    return output, in_block_comment


def checked_lines(path):
    in_block_comment = False
    for line_number, raw_line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        line, in_block_comment = strip_block_comments(raw_line, in_block_comment)
        line = line.split("//", 1)[0]
        yield line_number, line


def main():
    parser = argparse.ArgumentParser(description="Check active RTL for portability rules")
    parser.add_argument("filelist", type=Path)
    args = parser.parse_args()

    failures = []
    for source in traced_sources(args.filelist.resolve()):
        for line_number, line in checked_lines(source):
            for name, pattern, guidance in RULES:
                if pattern.search(line):
                    failures.append((source, line_number, name, guidance))

    if failures:
        for source, line_number, name, guidance in failures:
            print(f"{source}:{line_number}: unsupported {name}. {guidance}")
        raise SystemExit(1)

    print("RTL portability checks passed")


if __name__ == "__main__":
    main()
