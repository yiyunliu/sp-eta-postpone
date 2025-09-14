COQMAKEFILE=CoqMakefile

theories: $(COQMAKEFILE) FORCE
	$(MAKE) -f $(COQMAKEFILE)

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
	autosubst -f -v ge813 -s ucoq -o theories/Autosubst2/syntax.v syntax.sig

.PHONY: clean FORCE export deepclean

clean:
	test ! -f $(COQMAKEFILE) || ( $(MAKE) -f $(COQMAKEFILE) clean && rm $(COQMAKEFILE) )

deepclean: clean
	rm -f theories/Autosubst2/syntax.v theories/Autosubst2/core.v theories/Autosubst2/unscoped.v

FORCE:
