CURRENT_DIR=.
SETS_DIR = sets
COMPCERT_DIR = compcert_lib
PL_DIR = pl

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

PL_FLAG = -R $(PL_DIR) PL -R $(SETS_DIR) SetsClass -R $(COMPCERT_DIR) compcert.lib

SETS_FLAG = -R $(SETS_DIR) SetsClass

COMPCERT_FLAG = -R $(COMPCERT_DIR) compcert.lib

DEP_FLAG = -R $(PL_DIR) PL -R $(SETS_DIR) SetsClass -R $(COMPCERT_DIR) compcert.lib

SETS_FILE_NAMES = \
   SetsClass.v SetsDomain.v SetElement.v SetProd.v RelsDomain.v
   
SETS_FILES=$(SETS_FILE_NAMES:%.v=$(SETS_DIR)/%.v)
   
COMPCERT_FILE_NAMES = \
    Coqlib.v Integers.v Zbits.v
    
COMPCERT_FILES=$(COMPCERT_FILE_NAMES:%.v=$(COMPCERT_DIR)/%.v)

PL_FILE_NAMES = \
    CoqIntro.v InductiveType.v Logic.v SyntaxInCoq.v DenotationalSemantics.v PracticalDenotations.v \
	EquivAndRefine.v
PL_FILES=$(PL_FILE_NAMES:%.v=$(PL_DIR)/%.v)

FILES = $(PL_FILES) \
  $(SETS_FILES) \
  $(COMPCERT_FILES)

$(SETS_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $<
	@$(COQC) $(SETS_FLAG) $<

$(COMPCERT_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $<
	@$(COQC) $(COMPCERT_FLAG) $<
			
$(PL_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(PL_FLAG) $<

all: $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f *.glob */*.glob
	@rm -f *.vo */*.vo
	@rm -f *.vok */*.vok
	@rm -f *.vos */*.vos 
	@rm -f .*.aux */.*.aux
	@rm -f .depend

.PHONY: clean depend
.DEFAULT_GOAL := all

-include .depend
