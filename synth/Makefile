STEVIA_ROOT ?= $(abspath ..)
STEVIA_OUTPUTS_DIR ?= $(STEVIA_ROOT)/outputs
export STEVIA_ROOT
export STEVIA_OUTPUTS_DIR

SYNTH_OUTPUTS_DIR := $(STEVIA_OUTPUTS_DIR)/synth
SYNTH_LOG := $(SYNTH_OUTPUTS_DIR)/yosys_smoke.log
YOSYS_SCRIPT := yosys_smoke.ys

.PHONY: all smoke check-env clean

all: smoke

$(SYNTH_OUTPUTS_DIR):
	mkdir -p $@

smoke: $(YOSYS_SCRIPT) check-env | $(SYNTH_OUTPUTS_DIR)
	yosys -q -l $(SYNTH_LOG) $(YOSYS_SCRIPT)

check-env:
ifndef STEVIA_ROOT
	$(error STEVIA_ROOT is undefined)
endif

clean:
	rm -rf $(SYNTH_OUTPUTS_DIR)
