
STEVIA_ROOT ?= $(abspath ..)
export STEVIA_ROOT
PYTHON ?= $(STEVIA_ROOT)/.venv/bin/python

all:
	cd $(STEVIA_ROOT) && $(PYTHON) -m pytest -n auto test/smoke

clean:
	find $(STEVIA_ROOT) -name "sim_build*" | xargs rm -rf
	find $(STEVIA_ROOT) -name "results*.xml" | xargs rm -f
	find $(STEVIA_ROOT) -name __pycache__ | xargs rm -rf
	find $(STEVIA_ROOT) -name .pytest_cache | xargs rm -rf
