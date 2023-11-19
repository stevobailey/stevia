
all: slang verible verilator
 
.PHONY: slang verible

slang:
	slang --lint-only -Weverything -Werror -f ${STEVIA_ROOT}/rtl/filelist.f | tee slang.log

verible:
	python ${STEVIA_ROOT}/scripts/trace_filelist.py ${STEVIA_ROOT}/rtl/filelist.f | xargs verible-verilog-lint --check_syntax=true | tee verible.log

verilator:
	verilator --lint-only -Wno-MULTITOP -f ${STEVIA_ROOT}/rtl/filelist.f | tee verilator.log

clean:
	rm -f *.log
