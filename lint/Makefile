
all: slang.log verible.log verilator.log

.PHONY: deps check-env

deps: check-env ${STEVIA_ROOT}/rtl/filelist.f

slang.log: deps
	slang --lint-only -Weverything -Werror -f ${STEVIA_ROOT}/rtl/filelist.f | tee slang.log

verible.log: deps
	python ${STEVIA_ROOT}/scripts/trace_filelist.py ${STEVIA_ROOT}/rtl/filelist.f | xargs verible-verilog-lint --rules_config=${STEVIA_ROOT}/lint/stevia.rules.verible_lint | tee verible.log

verilator.log: deps
	verilator --lint-only -Wno-MULTITOP -f ${STEVIA_ROOT}/rtl/filelist.f | tee verilator.log

check-env:
ifndef STEVIA_ROOT
	$(error STEVIA_ROOT is undefined (did you source setup.sh?))
endif

clean:
	rm -f *.log
