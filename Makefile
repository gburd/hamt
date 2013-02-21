TARGET=		hamt

REBAR=		/usr/bin/env rebar
ERL=		/usr/bin/env erl
DIALYZER=	/usr/bin/env dialyzer
REBAR=		/usr/bin/env rebar
ifdef suites
	SUITE_OPTION := suites=$(suites)
endif
ifdef tests
	TESTS_OPTION := tests=$(tests)
endif
EUNIT_OPTIONS := $(SUITE_OPTION) $(TESTS_OPTION)

.PHONY: deps test

all: deps compile

deps:
	$(REBAR) get-deps

compile: deps
	$(REBAR) compile

clean:
	$(REBAR) clean

distclean: clean
	$(REBAR) delete-deps

eunit: test

test: compile
	$(REBAR) skip_deps=true $(EUNIT_OPTIONS) eunit

console: compile
	erl -pa ebin deps/*/ebin

plt: compile
	@$(DIALYZER) --build_plt --output_plt .$(TARGET).plt \
		-pa deps/plain_fsm/ebin \
		deps/plain_fsm/ebin \
		--apps kernel stdlib

analyze: compile
	$(DIALYZER) --plt .$(TARGET).plt \
	-pa deps/plain_fsm/ebin \
	-pa deps/ebloom/ebin \
	ebin

repl:
	$(ERL) -pz deps/*/ebin -pa ebin

eunit-repl:
	erl -pa .eunit -pz deps/*/ebin -pz ebin -exec 'cd(".eunit").'

gdb-eunit-repl:
	USE_GDB=1 erl -pa .eunit -pz deps/*/ebin -pz ebin -exec 'cd(".eunit").'
