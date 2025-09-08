
.PHONY: main
main: main.pdf

main.pdf: tex
	latexmk -pdf -auxdir=aux main

.PHONY: watch
watch: tex
	latexmk -pdf -pvc -auxdir=aux main

.PHONY: tex
tex: main.lhs
	lhs2TeX --agda main.lhs -o main.tex

.PHONY: bib
bib: aux/main.aux
	bibexport -o ref.bib aux/main.aux

.PHONY: clean
clean:
	latexmk -auxdir=aux -C main
	rm main.tex
