STEVIA_ROOT ?= $(abspath ..)
export STEVIA_ROOT

SYNTH_LOG := yosys_smoke.log
YOSYS_SCRIPT := yosys_smoke.ys

.PHONY: all check-env clean

all: $(SYNTH_LOG)

$(SYNTH_LOG): $(YOSYS_SCRIPT) check-env
	yosys -q -l $(SYNTH_LOG) $(YOSYS_SCRIPT)

check-env:
ifndef STEVIA_ROOT
	$(error STEVIA_ROOT is undefined)
endif

clean:
	rm -f $(SYNTH_LOG)
