
STEVIA_ROOT ?= $(abspath ..)
STEVIA_OUTPUTS_DIR ?= $(CURDIR)/outputs
export STEVIA_ROOT
export STEVIA_OUTPUTS_DIR
export PATH := $(STEVIA_ROOT)/.venv/bin:$(STEVIA_ROOT)/.tools/bin:$(PATH)
SHELL := /bin/bash
.SHELLFLAGS := -o pipefail -c

LINT_SCOPE := full
LINT_MODULE := _all

ifneq ($(strip $(FILE)),)
ifneq ($(strip $(MODULE)),)
$(error Set FILE or MODULE, not both)
endif
LINT_SCOPE := $(basename $(notdir $(FILE)))
LINT_MODULE := $(LINT_SCOPE)
SELECTED_FILES := $(shell if [ -f "$(FILE)" ]; then realpath "$(FILE)"; elif [ -f "$(STEVIA_ROOT)/$(FILE)" ]; then realpath "$(STEVIA_ROOT)/$(FILE)"; else printf "%s" "$(abspath $(FILE))"; fi)
endif

ifneq ($(strip $(MODULE)),)
LINT_SCOPE := $(MODULE)
LINT_MODULE := $(MODULE)
SELECTED_FILES := $(shell find $(STEVIA_ROOT)/rtl -name "$(MODULE).sv" -print)
endif

LINT_RUN_DIR := $(STEVIA_OUTPUTS_DIR)/$(LINT_MODULE)
LINT_FILELIST := $(STEVIA_ROOT)/rtl/filelist.f
ifneq ($(strip $(SELECTED_FILES)),)
LINT_FILELIST := $(LINT_RUN_DIR)/filelist.f
endif

SLANG_LOG := $(LINT_RUN_DIR)/slang.log
VERIBLE_LOG := $(LINT_RUN_DIR)/verible.log
VERILATOR_LOG := $(LINT_RUN_DIR)/verilator.log

ifneq ($(strip $(TOOL)),)
all: $(TOOL)
else
all: slang verible verilator
endif

.PHONY: all deps filelist slang verible verilator FORCE check-env clean

deps: check-env $(LINT_FILELIST)

$(LINT_RUN_DIR):
	mkdir -p $@

$(LINT_RUN_DIR)/filelist.f: FORCE | $(LINT_RUN_DIR)
	test -n "$(SELECTED_FILES)"
	printf "%s\n" $(SELECTED_FILES) > $@

filelist: $(LINT_FILELIST)

FORCE:

slang: deps | $(LINT_RUN_DIR)
	slang --lint-only -Weverything -Werror -f $(LINT_FILELIST) | tee $(SLANG_LOG)

verible: deps | $(LINT_RUN_DIR)
	python3 ${STEVIA_ROOT}/scripts/trace_filelist.py $(LINT_FILELIST) | xargs verible-verilog-lint --rules_config=${STEVIA_ROOT}/lint/stevia.rules.verible_lint | tee $(VERIBLE_LOG)

verilator: deps | $(LINT_RUN_DIR)
	verilator --lint-only -Wno-MULTITOP -f $(LINT_FILELIST) | tee $(VERILATOR_LOG)

check-env:
ifndef STEVIA_ROOT
	$(error STEVIA_ROOT is undefined (did you source setup.sh?))
endif
ifneq ($(strip $(MODULE)),)
ifeq ($(strip $(SELECTED_FILES)),)
	$(error No RTL source found for MODULE=$(MODULE))
endif
endif

clean:
	rm -rf $(STEVIA_OUTPUTS_DIR)
