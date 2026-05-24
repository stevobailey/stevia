STEVIA_ROOT ?= $(abspath ..)
STEVIA_OUTPUTS_DIR ?= $(CURDIR)/outputs
export STEVIA_ROOT
export STEVIA_OUTPUTS_DIR
export PATH := $(STEVIA_ROOT)/.venv/bin:$(STEVIA_ROOT)/.tools/bin:$(PATH)

FORMAL_TARGETS := stv_lzc

.PHONY: all $(FORMAL_TARGETS) check-env clean

all: $(FORMAL_TARGETS)

$(FORMAL_TARGETS): check-env
	mkdir -p $(STEVIA_OUTPUTS_DIR)
	sby -f -d $(STEVIA_OUTPUTS_DIR)/$@ $@/$@.sby

check-env:
ifndef STEVIA_ROOT
	$(error STEVIA_ROOT is undefined)
endif

clean:
	rm -rf $(STEVIA_OUTPUTS_DIR)
