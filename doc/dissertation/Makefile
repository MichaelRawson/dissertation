.PHONY: dissertation.pdf all clean

all: dissertation.pdf

dissertation.pdf: dissertation.tex
	latexmk -quiet -pdf -pdflatex="pdflatex -interaction=nonstopmode --shell-escape" -use-make $<

clean:
	latexmk -CA
