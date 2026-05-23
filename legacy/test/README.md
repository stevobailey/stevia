# Stevia Verification

Verification is done through Cocotb, Verilator, and pytest.

## Quick Start

To run the full suite:
```
pytest -n 8
```

To run an individual test:
```
python path/to/test_stv_design.py
```

## Writing Tests

Tests are written in python using [Cocotb](https://www.cocotb.org/).

- Use the same directory structure as the rtl directory
- Name your python script test_[module name].py
- Decorate your test functions with @cocotb.test()
- Add a pytest function
- Call the pytest function from main

### Cocotb test functions

### The pytest function

Extend your test to use pytest, as documented 
[here](https://docs.cocotb.org/en/stable/runner.html#usage-with-pytest).

The example test function looks like:
```
def test_stv_skid_buffer():
     
    hdl_toplevel = "stv_skid_buffer"

    runner = get_runner("verilator")
    runner.build(
        hdl_toplevel=hdl_toplevel,
        build_dir="sim_build/" + hdl_toplevel,
        build_args=["-f", "$STEVIA_ROOT/rtl/filelist.f"],
        always=True,
    )

    runner.test(
        hdl_toplevel=hdl_toplevel, 
        test_module="test_" + hdl_toplevel,
        hdl_toplevel_lang = "verilog"
    )
```
The only changes you need to make are in the function name and `hdl_toplevel` variable.
This will allow pytest to run all your tests.

To run the tests multiple times with different parameters, pass the parameters list to the runner.
Be sure to change the results.xml filename, otherwise later tests will overwrite the file.
```
    for width in [8, 13, 32]:
        runner.test(
            hdl_toplevel=hdl_toplevel, 
            test_module="test_" + hdl_toplevel,
            hdl_toplevel_lang = "verilog",
            parameters = {"WIDTH": width},
            results_xml = f"results_{width}.xml"
        )
```

### The main function

Add the following code at the end of your test so it can be run directly:
```
if __name__ == "__main__":
    test_[module name]()
```

## Running Tests

Test files can be run directly.
```
python path/to/test_stv_design.py
```

TODO: add trace, coverage

## Cleaning up

This will remove all generated directories, files, and caches:
```
make clean
```
