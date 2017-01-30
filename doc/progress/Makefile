.PHONY: progress.pdf all clean

all: progress.pdf

progress.pdf: progress.tex
	latexmk -quiet -pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make $<

clean:
	latexmk -CA
