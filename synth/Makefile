STEVIA_ROOT ?= $(abspath ..)
STEVIA_OUTPUTS_DIR ?= $(CURDIR)/outputs
export STEVIA_ROOT
export STEVIA_OUTPUTS_DIR

.PHONY: all smoke check-env clean

all: smoke

smoke: check-env
	python3 run_synth.py --outputs-dir $(STEVIA_OUTPUTS_DIR) $(if $(MODULE),--module $(MODULE),) $(if $(CONFIG),--config $(CONFIG),)

check-env:
ifndef STEVIA_ROOT
	$(error STEVIA_ROOT is undefined)
endif

clean:
	rm -rf $(STEVIA_OUTPUTS_DIR)
