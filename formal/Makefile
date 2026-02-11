# 8-bit CPU Simulator - Formal Verification

JAVA    ?= $(if $(JAVA_HOME),$(JAVA_HOME)/bin/java,java)
TLC_JAR ?= tla2tools.jar
TLC     := $(JAVA) -XX:+UseParallelGC -cp $(TLC_JAR) tlc2.TLC
TESTS   := $(sort $(basename $(notdir $(wildcard tests/test_*.cfg))))

.PHONY: help test clean _check $(TESTS)
.DEFAULT_GOAL := help

help:
	@echo "Usage: make <target>"
	@echo ""
	@echo "  test         Run all tests (verbose)"
	@echo "  clean        Remove TLC artifacts"
	@echo ""
	@echo "  test_<name>  Run a single test, e.g. make test_basic"
	@echo ""
	@echo "Tests found: $(words $(TESTS))"

_check:
	@$(JAVA) -version >/dev/null 2>&1 || { echo "Error: java not found or not working."; \
	echo "Set JAVA_HOME or add java to PATH, e.g.:"; \
	echo "  export JAVA_HOME=/path/to/jdk  # in ~/.zshrc or ~/.bashrc"; \
	exit 1; }
	@test -f $(TLC_JAR) || { echo "Error: $(TLC_JAR) not found. Download it:"; \
	echo "  curl -LO https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar"; \
	exit 1; }

define RUN_TEST
$(TLC) -config tests/$(1).cfg tests/$(1).tla
endef

test: _check
	@for t in $(TESTS); do \
		echo "=== $$t ==="; \
		$(call RUN_TEST,$$t); \
		echo; \
	done

$(TESTS): _check
	@$(call RUN_TEST,$@)

clean:
	@rm -rf states plans tests/states
	@rm -f *_TTrace_*.tla *_new.tla tests/*_TTrace_*.tla tests/*.bin
	@echo "Cleaned TLC artifacts"
