COQMAKEFILE=CoqMakefile
COQDOCJS_DIR ?= coqdocjs
EXTRA_DIR = $(COQDOCJS_DIR)/extra
COQDOCFLAGS ?= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQDOCJS_LN?=false
COQDOCJS_STATIC?=true

theories: $(COQMAKEFILE) FORCE
	$(MAKE) -f $(COQMAKEFILE)

coqdoc: $(COQMAKEFILE)
	$(MAKE) -f $^ html
ifeq ($(COQDOCJS_LN),true)
	ln -sf ../$(EXTRA_DIR)/resources html
else
	cp -R $(EXTRA_DIR)/resources html
endif
ifeq ($(COQDOCJS_STATIC),true)
	cd coqdocjs/coqdocjs-static &&	npm install && \
		find ../../html/ -name '*.html' | \
		parallel node index.js --inplace {}
	rm -f html/resources/preprocess.js
	rm -r html/resources/config.js
	grep -v preprocess $(EXTRA_DIR)/resources/coqdocjs.js > html/resources/coqdocjs.js
endif

README.html: README.org
	pandoc -s --metadata title='Algorithmic conversion with surjective pairing' README.org --output README.html


validate: $(COQMAKEFILE) FORCE
	$(MAKE) -f $(COQMAKEFILE) validate

$(COQMAKEFILE) : theories/Autosubst2/syntax.v theories/Autosubst2/core.v theories/Autosubst2/unscoped.v
	$(COQBIN)coq_makefile -f _CoqProject -o $(COQMAKEFILE)

install: $(COQMAKEFILE)
	$(MAKE) -f $^ install

uninstall: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) uninstall

export:
	git archive --output supplementary.tar master --prefix supplementary/source/

theories/Autosubst2/syntax.v theories/Autosubst2/core.v theories/Autosubst2/unscoped.v : syntax.sig
	autosubst -f -v ge813 -s urocq -o theories/Autosubst2/syntax.v syntax.sig

.PHONY: clean FORCE export deepclean coqdoc

clean:
	test ! -f $(COQMAKEFILE) || ( $(MAKE) -f $(COQMAKEFILE) clean && rm $(COQMAKEFILE) )

deepclean: clean
	rm -f theories/Autosubst2/syntax.v theories/Autosubst2/core.v theories/Autosubst2/unscoped.v

FORCE:
