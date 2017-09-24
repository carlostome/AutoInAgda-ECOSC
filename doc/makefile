TEMP_FILE    := $(shell mktemp)
LATEXMK_OPTS := -bibtex
MAIN := report

all: $(MAIN).tex
	lhs2TeX --agda $(MAIN).tex  > $(TEMP_FILE)
	latexmk -pdf $(LATEXMK_OPTS) -jobname=$(MAIN) $(TEMP_FILE)

clean:
	latexmk $(LATEXMK_OPTS) -c -C $(MAIN).tex
