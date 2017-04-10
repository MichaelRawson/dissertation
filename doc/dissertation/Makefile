.PHONY: clean

all: dissertation.pdf

dissertation.pdf: chapters/evaluation/evaluation.tex dissertation.tex dissertation.bib
	latexmk -silent -halt-on-error -pdf -pdflatex="pdflatex -interaction=nonstopmode --shell-escape" -outdir=output dissertation.tex

clean:
	latexmk -CA
