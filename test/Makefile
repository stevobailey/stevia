
STEVIA_ROOT ?= $(abspath ..)
STEVIA_OUTPUTS_DIR ?= $(CURDIR)/outputs
export STEVIA_ROOT
export STEVIA_OUTPUTS_DIR
export STEVIA_WAVES := $(WAVES)
PYTHON ?= $(STEVIA_ROOT)/.venv/bin/python

.PHONY: all clean

all:
	mkdir -p $(STEVIA_OUTPUTS_DIR)
	cd $(STEVIA_ROOT) && $(PYTHON) -m pytest -n auto test/smoke

clean:
	rm -rf $(STEVIA_OUTPUTS_DIR)
	find $(STEVIA_ROOT) -name __pycache__ | xargs rm -rf
	find $(STEVIA_ROOT) -name .pytest_cache | xargs rm -rf
