STEVIA_ROOT ?= $(abspath ..)
export STEVIA_ROOT
export PATH := $(STEVIA_ROOT)/.venv/bin:$(STEVIA_ROOT)/.tools/bin:$(PATH)

FORMAL_TARGETS := stv_lzc

.PHONY: all $(FORMAL_TARGETS) check-env clean

all: $(FORMAL_TARGETS)

$(FORMAL_TARGETS): check-env
	sby -f $@/$@.sby

check-env:
ifndef STEVIA_ROOT
	$(error STEVIA_ROOT is undefined)
endif

clean:
	rm -rf */*_*/
