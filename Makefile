LATEXMK ?= latexmk
PDFLATEX ?= pdflatex

.PHONY: all clean dist

all: paper.pdf

paper.pdf: paper.tex
	@if command -v $(LATEXMK) >/dev/null 2>&1; then \
		$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error paper.tex; \
	else \
		$(PDFLATEX) -interaction=nonstopmode -halt-on-error paper.tex; \
		$(PDFLATEX) -interaction=nonstopmode -halt-on-error paper.tex; \
	fi

clean:
	@if command -v $(LATEXMK) >/dev/null 2>&1; then \
		$(LATEXMK) -C paper.tex; \
	else \
		rm -f paper.aux paper.log paper.out paper.toc paper.pdf; \
	fi

dist: paper.tex README.md Makefile
	tar -czf greedy-3-sumfree-publishable-layer-arxiv.tar.gz \
		paper.tex README.md Makefile
