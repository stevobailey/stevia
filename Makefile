export STEVIA_ROOT := $(CURDIR)
export PATH := $(CURDIR)/.venv/bin:$(CURDIR)/.tools/bin:$(PATH)

.PHONY: all tools lint test formal synth clean

all: lint test formal synth

tools:
	scripts/install_tools.sh

lint:
	$(MAKE) -C lint

test:
	$(MAKE) -C test

formal:
	$(MAKE) -C formal

synth:
	$(MAKE) -C synth

clean:
	$(MAKE) -C lint clean
	$(MAKE) -C test clean
	$(MAKE) -C formal clean
	$(MAKE) -C synth clean
