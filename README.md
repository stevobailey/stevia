# Stevia

Stevia is an open source SystemVerilog library.

## Introduction

Stevia is a free, open source SystemVerilog library.
I seek to use good design practices, such as well-formatted code, clean syntax, standardized interfaces, modular design construction, and extensive verification.
Code is linted by [verible](https://github.com/chipsalliance/verible) and [verilator](https://verilator.org).
Verification and coverage are performed by [cocotb](https://cocotb.org) and [verilator](https://verilator.org).

## Code Requirements

1. Do not use SystemVerilog interfaces.
2. All resets are asynchronous and active low.
3. Use parameters, not defines.
