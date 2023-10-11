CURRENT_DIR=.

-include CONFIGURE

COQC=$(COQBIN)coqc$(EXESUF)
COQDEP=$(COQBIN)coqdep$(EXESUF)

COQ_FLAG = -Q $(CURRENT_DIR) SetsClass
DEP_FLAG = -Q $(CURRENT_DIR) SetsClass

FILES = \
  SetsClass.v \
  SetsDomain.v \
  SetElement.v \
  RelsDomain.v \
  SetProd.v

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

Test.vo: Test.v
	@echo COQC Test.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/Test.v

world: \
  $(FILES:%.v=%.vo)

test: \
  Test.vo

all: world test

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) Test.v > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) Test.v > .depend

clean:
	@rm *.vo *.glob *.vos *.vok

.DEFAULT_GOAL := all

include .depend

