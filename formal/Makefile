# 8-bit CPU Simulator - Formal Verification

JAVA     ?= java
TLC_JAR  ?= tla2tools.jar
TLC      := $(JAVA) -XX:+UseParallelGC -cp $(TLC_JAR) tlc2.TLC
TESTS    := test_basic test_stack test_jumps test_math test_faults \
			test_bitwise test_overflow test_indirect test_xor \
			test_bitwise_laws test_shift test_fault_codes \
			test_state_machine test_demorgan test_arithmetic \
			test_associativity test_instruction_props test_registers \
			test_adversarial test_stack_attack test_invalid_code test_div_zero \
			test_shift_zero test_ip_overflow

.PHONY: test clean $(TESTS)

check_jar:
	@test -f $(TLC_JAR) || { echo "Error: $(TLC_JAR) not found. Download it:"; \
	echo "  curl -LO https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar"; \
	exit 1; }

define RUN_TEST
$(TLC) -config tests/$(1).cfg tests/$(1).tla
endef

test: check_jar
	@for t in $(TESTS); do \
		printf "%-16s" "$$t:"; \
		$(call RUN_TEST,$$t) 2>&1 | \
		grep -oE "(No error has been found|Error:.*)" | head -1; \
	done

$(TESTS): check_jar
	@$(call RUN_TEST,$@)

clean:
	@rm -rf states plans tests/states
	@rm -f *_TTrace_*.tla *_new.tla tests/*_TTrace_*.tla tests/*.bin
	@echo "Cleaned TLC artifacts"
