STEVIA_ROOT ?= $(abspath ..)
STEVIA_OUTPUTS_DIR ?= $(CURDIR)/outputs
export STEVIA_ROOT
export STEVIA_OUTPUTS_DIR
export PATH := $(STEVIA_ROOT)/.venv/bin:$(STEVIA_ROOT)/.tools/bin:$(PATH)

FORMAL_TARGETS := stv_lzc \
	stv_buffer_f0_s0_oat0 \
	stv_buffer_f0_s0_oat1 \
	stv_buffer_f0_s1_oat0 \
	stv_buffer_f0_s1_oat1 \
	stv_buffer_f1_s0_oat0 \
	stv_buffer_f1_s0_oat1 \
	stv_buffer_f1_s1_oat0 \
	stv_buffer_f1_s1_oat1 \
	stv_sync_fifo_f0_s0 \
	stv_sync_fifo_f0_s1 \
	stv_sync_fifo_f1_s0 \
	stv_sync_fifo_f1_s1

SBY_FILE_stv_lzc := util/stv_lzc/stv_lzc.sby
SBY_FILE_stv_buffer_f0_s0_oat0 := util/stv_buffer/stv_buffer_f0_s0_oat0.sby
SBY_FILE_stv_buffer_f0_s0_oat1 := util/stv_buffer/stv_buffer_f0_s0_oat1.sby
SBY_FILE_stv_buffer_f0_s1_oat0 := util/stv_buffer/stv_buffer_f0_s1_oat0.sby
SBY_FILE_stv_buffer_f0_s1_oat1 := util/stv_buffer/stv_buffer_f0_s1_oat1.sby
SBY_FILE_stv_buffer_f1_s0_oat0 := util/stv_buffer/stv_buffer_f1_s0_oat0.sby
SBY_FILE_stv_buffer_f1_s0_oat1 := util/stv_buffer/stv_buffer_f1_s0_oat1.sby
SBY_FILE_stv_buffer_f1_s1_oat0 := util/stv_buffer/stv_buffer_f1_s1_oat0.sby
SBY_FILE_stv_buffer_f1_s1_oat1 := util/stv_buffer/stv_buffer_f1_s1_oat1.sby
SBY_FILE_stv_sync_fifo_f0_s0 := util/stv_sync_fifo/stv_sync_fifo_f0_s0.sby
SBY_FILE_stv_sync_fifo_f0_s1 := util/stv_sync_fifo/stv_sync_fifo_f0_s1.sby
SBY_FILE_stv_sync_fifo_f1_s0 := util/stv_sync_fifo/stv_sync_fifo_f1_s0.sby
SBY_FILE_stv_sync_fifo_f1_s1 := util/stv_sync_fifo/stv_sync_fifo_f1_s1.sby

.PHONY: all $(FORMAL_TARGETS) check-env clean

all: $(FORMAL_TARGETS)

$(FORMAL_TARGETS): check-env
	mkdir -p $(STEVIA_OUTPUTS_DIR)
	sby -f -d $(STEVIA_OUTPUTS_DIR)/$@ $(SBY_FILE_$@)

check-env:
ifndef STEVIA_ROOT
	$(error STEVIA_ROOT is undefined)
endif

clean:
	rm -rf $(STEVIA_OUTPUTS_DIR)
