HS_TO_COQ = hs-to-coq
HS_TO_COQ_BASEDIR = /Users/amos/proj/hs-to-coq

# Edit this
GENMODS = List Replicate RunLengthEncoding
MANMODS = List_Proof Replicate_Proof RunLengthEncoding_Proof

# Abstract stuff

VFILES_GEN = $(addsuffix .v,$(subst .,/,$(GENMODS)))
VFILES_MAN = $(addsuffix .v,$(MANMODS))

VFILES   = $(VFILES_GEN) $(VFILES_MAN)

all: coq

$(VFILES_GEN): %.v : %.hs edits  $(HS_TO_COQ_BASEDIR)/base/edits
	$(HS_TO_COQ) -e edits -e $(HS_TO_COQ_BASEDIR)/base/edits --midamble midamble.v $< -o .

_CoqProject : Makefile
	> $@
	echo '-Q .               ""'		>> $@
	echo '-Q $(HS_TO_COQ_BASEDIR)/base-thy/ Proofs' >> $@
	echo '-Q $(HS_TO_COQ_BASEDIR)/base/     ""'		>> $@
	echo $(VFILES)										>> $@

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

coq: Makefile.coq $(VFILES)
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

clean:
	rm -f */*/*.vo */*/*.glob */*/*.v.d */*.vo */*.glob */*.v.d *.glob *.vo *.v.d _CoqProject Makefile.coq $(VFILES_GEN) */*.v~
