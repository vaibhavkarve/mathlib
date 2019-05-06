# Copyright (c) 2018 Simon Hudon. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Simon Hudon

LEAN = lean
SRCS = $(shell find src -name '*.lean')
TESTS = $(shell find test -name '*.lean')
OBJS = $(SRCS:.lean=.olean) $(TESTS:.lean=.olean)
# DEPS = $(SRCS:.lean=.depend)
DEPS = $(addprefix _build/,$(SRCS:.lean=.depend))
UNUSED = $(addsuffix .unused,$(addprefix _build/,$(SRCS)))

.PHONY: all clean

all: $(OBJS)

depends: $(DEPS)

unused: $(UNUSED)

_build/%.depend: %.lean
	@mkdir -p $(@D)
	@echo $(<:.lean=.olean) : `$(LEAN) --deps $< | python scripts/relative.py` "\n" > $@

_build/%.olean.unused: %.olean
	olean-rs -u $<
	@touch $@

%.olean: %.lean $(addprefix _build/,$(%:.lean=.depend))
	$(LEAN) --make $<
	@touch $*.olean
	olean-rs -u $@
	touch _build/$@.unused
# make sure the .olean file is newer than the .depend file to prevent infinite make cycles

test/%.olean: test/%.lean $(addprefix _build/test/,$(%:.lean=.depend))
	$(LEAN) --make $<
	@touch $*.olean

src/%.olean: src/%.lean $(addprefix _build/src/,$(%:.lean=.depend))
	$(LEAN) --make $<
	@touch $*.olean
	olean-rs -u $@
	touch _build/$@.unused
# make sure the .olean file is newer than the .depend file to prevent infinite make cycles

clean:
	find . -name *.olean -delete
	find . -name *.depend -delete
	find . -name *.unused -delete

# .PRECIOUS: %.depend

include $(DEPS)
