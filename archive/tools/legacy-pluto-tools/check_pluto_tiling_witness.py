#!/usr/bin/env python3
from __future__ import annotations

import sys

from validate_pluto_tiling import main


if __name__ == "__main__":
    raise SystemExit(main(["check", *sys.argv[1:]]))
