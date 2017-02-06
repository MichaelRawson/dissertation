.PHONY: slides.pdf all clean

all: slides.pdf

slides.pdf: slides.tex
	latexmk -quiet -pdf -pdflatex="pdflatex -interaction=nonstopmode" -use-make $<

clean:
	latexmk -CA
