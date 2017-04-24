all: dissertation.pdf

dissertation.pdf: chapters/evaluation/evaluation.tex dissertation.tex dissertation.bib
	latexmk -silent -halt-on-error -pdf --pdflatex='pdflatex --shell-escape %O %S' -outdir=output dissertation.tex
