
STEVIA_ROOT ?= $(abspath ..)
STEVIA_OUTPUTS_DIR ?= $(STEVIA_ROOT)/outputs
export STEVIA_ROOT
export STEVIA_OUTPUTS_DIR
export STEVIA_WAVES := $(WAVES)
PYTHON ?= $(STEVIA_ROOT)/.venv/bin/python

.PHONY: all clean

all:
	mkdir -p $(STEVIA_OUTPUTS_DIR)
	cd $(STEVIA_ROOT) && $(PYTHON) -m pytest -n auto test/smoke

clean:
	if [ -d $(STEVIA_OUTPUTS_DIR) ]; then find $(STEVIA_OUTPUTS_DIR) -mindepth 2 -maxdepth 2 -type d -name test -exec rm -rf {} +; fi
	find $(STEVIA_ROOT) -name __pycache__ | xargs rm -rf
	find $(STEVIA_ROOT) -name .pytest_cache | xargs rm -rf
