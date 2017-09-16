TEMP_FILE    := $(shell mktemp)
LATEXMK_OPTS := -bibtex

all: main.tex
	lhs2TeX --agda main.tex  > $(TEMP_FILE)
	latexmk -pdf $(LATEXMK_OPTS) -jobname=main $(TEMP_FILE)

clean:
	latexmk $(LATEXMK_OPTS) -C main.tex
