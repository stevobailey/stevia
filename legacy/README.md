# Legacy Code

This directory contains pre-modernization RTL and cocotb tests that are not part
of the active Stevia release surface.

Files here are kept as reference material while blocks are reviewed, rewritten,
or promoted back into `rtl/`. Moving a block out of `legacy/` should include:

1. Adding the RTL to `rtl/filelist.f`.
2. Adding or updating cocotb smoke coverage.
3. Adding assertions and formal checks where practical.
4. Adding synthesis smoke coverage when supported by the open-source tool flow.
5. Passing `make all`.
