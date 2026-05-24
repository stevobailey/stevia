STEVIA_ROOT ?= $(abspath ..)
STEVIA_OUTPUTS_DIR ?= $(STEVIA_ROOT)/outputs
export STEVIA_ROOT
export STEVIA_OUTPUTS_DIR

SYNTH_MODULE := stv_lzc
SYNTH_CONFIG := stv_lzc_w8
SYNTH_OUTPUTS_DIR := $(STEVIA_OUTPUTS_DIR)/$(SYNTH_MODULE)/synth
SYNTH_RUN_DIR := $(SYNTH_OUTPUTS_DIR)/$(SYNTH_CONFIG)
SYNTH_LOG := $(SYNTH_RUN_DIR)/yosys.log
YOSYS_SCRIPT := yosys_smoke.ys

.PHONY: all smoke check-env clean

all: smoke

$(SYNTH_RUN_DIR):
	mkdir -p $@

smoke: $(YOSYS_SCRIPT) check-env | $(SYNTH_RUN_DIR)
	yosys -q -l $(SYNTH_LOG) $(YOSYS_SCRIPT)

check-env:
ifndef STEVIA_ROOT
	$(error STEVIA_ROOT is undefined)
endif

clean:
	rm -rf $(SYNTH_OUTPUTS_DIR)
