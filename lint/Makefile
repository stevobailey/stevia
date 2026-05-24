
STEVIA_ROOT ?= $(abspath ..)
STEVIA_OUTPUTS_DIR ?= $(STEVIA_ROOT)/outputs
export STEVIA_ROOT
export STEVIA_OUTPUTS_DIR
export PATH := $(STEVIA_ROOT)/.venv/bin:$(STEVIA_ROOT)/.tools/bin:$(PATH)
SHELL := /bin/bash
.SHELLFLAGS := -o pipefail -c

LINT_OUTPUTS_DIR := $(STEVIA_OUTPUTS_DIR)/lint
SLANG_LOG := $(LINT_OUTPUTS_DIR)/slang.log
VERIBLE_LOG := $(LINT_OUTPUTS_DIR)/verible.log
VERILATOR_LOG := $(LINT_OUTPUTS_DIR)/verilator.log

all: slang verible verilator

.PHONY: all deps slang verible verilator check-env clean

deps: check-env ${STEVIA_ROOT}/rtl/filelist.f

$(LINT_OUTPUTS_DIR):
	mkdir -p $@

slang: deps | $(LINT_OUTPUTS_DIR)
	slang --lint-only -Weverything -Werror -f ${STEVIA_ROOT}/rtl/filelist.f | tee $(SLANG_LOG)

verible: deps | $(LINT_OUTPUTS_DIR)
	python3 ${STEVIA_ROOT}/scripts/trace_filelist.py ${STEVIA_ROOT}/rtl/filelist.f | xargs verible-verilog-lint --rules_config=${STEVIA_ROOT}/lint/stevia.rules.verible_lint | tee $(VERIBLE_LOG)

verilator: deps | $(LINT_OUTPUTS_DIR)
	verilator --lint-only -Wno-MULTITOP -f ${STEVIA_ROOT}/rtl/filelist.f | tee $(VERILATOR_LOG)

check-env:
ifndef STEVIA_ROOT
	$(error STEVIA_ROOT is undefined (did you source setup.sh?))
endif

clean:
	rm -rf $(LINT_OUTPUTS_DIR)
