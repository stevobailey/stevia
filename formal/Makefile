STEVIA_ROOT ?= $(abspath ..)
STEVIA_OUTPUTS_DIR ?= $(STEVIA_ROOT)/outputs
export STEVIA_ROOT
export STEVIA_OUTPUTS_DIR
export PATH := $(STEVIA_ROOT)/.venv/bin:$(STEVIA_ROOT)/.tools/bin:$(PATH)

FORMAL_TARGETS := stv_lzc
FORMAL_OUTPUTS_DIR := $(STEVIA_OUTPUTS_DIR)/formal

.PHONY: all $(FORMAL_TARGETS) check-env clean

all: $(FORMAL_TARGETS)

$(FORMAL_TARGETS): check-env
	mkdir -p $(FORMAL_OUTPUTS_DIR)
	sby -f -d $(FORMAL_OUTPUTS_DIR)/$@ $@/$@.sby

check-env:
ifndef STEVIA_ROOT
	$(error STEVIA_ROOT is undefined)
endif

clean:
	rm -rf $(FORMAL_OUTPUTS_DIR)
