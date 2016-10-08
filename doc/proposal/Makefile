.PHONY: proposal.pdf all clean

all: proposal.pdf

proposal.pdf: proposal.tex
	latexmk -quiet -pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make $<

clean:
	latexmk -CA
