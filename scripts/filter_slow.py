#!/usr/bin/env python3
"""Pass a command's combined output through, logging slow lines and stalls.

Two things get appended to the log file given as the first argument:

  * A "slow line" of the form `<identifier> <duration>` (e.g. `foo 1.21ms`)
    whose duration is greater than one second.
  * A "stall": a gap of one second or more between two consecutive lines. The
    log record carries a timestamp plus the lines bracketing the gap.

A process can't read its own stdout/stderr, so the upstream command's stdout
and stderr are merged into this script's stdin (interleaved in real arrival
order, which is what stall detection needs) and echoed back to STDOUT:

    some_command 2>&1 | python3 filter_slow.py slow.log
"""
import re
import sys
import time
from datetime import datetime

# identifier, whitespace, number, time unit (anchored to the whole line)
LINE_RE = re.compile(r"^(\S+)\s+([0-9]*\.?[0-9]+)\s*(ns|us|µs|ms|s|m|h)\s*$")

# multiplier to convert each unit into seconds
UNIT_SECONDS = {
    "ns": 1e-9,
    "us": 1e-6,
    "µs": 1e-6,
    "ms": 1e-3,
    "s": 1.0,
    "m": 60.0,
    "h": 3600.0,
}

# minimum gap between consecutive lines that counts as a stall, in seconds
STALL_SECONDS = 1.0


def elapsed_seconds(line):
    """Return the duration in seconds if `line` is `<id> <duration>`, else None."""
    m = LINE_RE.match(line)
    if not m:
        return None
    value, unit = float(m.group(2)), m.group(3)
    return value * UNIT_SECONDS[unit]


def main():
    if len(sys.argv) != 2:
        sys.exit(f"usage: {sys.argv[0]} <output-log>")
    out_path = sys.argv[1]

    prev_line = None      # last line seen, for stall context
    prev_time = None      # arrival time (monotonic) of that line

    with open(out_path, "a", encoding="utf-8") as log:
        for line in sys.stdin:
            now = time.monotonic()
            sys.stdout.write(line)
            sys.stdout.flush()

            # Stall: too long since the previous line arrived.
            if prev_time is not None and now - prev_time >= STALL_SECONDS:
                stamp = datetime.now().isoformat(timespec="seconds")
                gap = now - prev_time
                log.write(
                    f"[STALL] {gap:.2f}s gap at {stamp}\n"
                    f"  before: {prev_line.rstrip(chr(10))}\n"
                    f"  after:  {line.rstrip(chr(10))}\n"
                )
                log.flush()

            # Slow line: a reported duration over one second.
            seconds = elapsed_seconds(line.rstrip("\n"))
            if seconds is not None and seconds > 1.0:
                log.write(line if line.endswith("\n") else line + "\n")
                log.flush()

            prev_line, prev_time = line, now


if __name__ == "__main__":
    main()
