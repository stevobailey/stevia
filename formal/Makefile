STEVIA_ROOT ?= $(abspath ..)
STEVIA_OUTPUTS_DIR ?= $(STEVIA_ROOT)/outputs
export STEVIA_ROOT
export STEVIA_OUTPUTS_DIR
export PATH := $(STEVIA_ROOT)/.venv/bin:$(STEVIA_ROOT)/.tools/bin:$(PATH)

FORMAL_TARGETS := stv_lzc

.PHONY: all $(FORMAL_TARGETS) check-env clean

all: $(FORMAL_TARGETS)

$(FORMAL_TARGETS): check-env
	mkdir -p $(STEVIA_OUTPUTS_DIR)/$@/formal
	sby -f -d $(STEVIA_OUTPUTS_DIR)/$@/formal $@/$@.sby

check-env:
ifndef STEVIA_ROOT
	$(error STEVIA_ROOT is undefined)
endif

clean:
	rm -rf $(foreach target,$(FORMAL_TARGETS),$(STEVIA_OUTPUTS_DIR)/$(target)/formal)
