TEX           := $(MODULES:%=latex/%.v.tex)

abc : 

notes: latex/g52ifr.pdf

%.v.tex: Makefile src/%.v src/%.glob
	coqdoc --interpolate --latex --body-only -s \
		$*.v -o $*.v.tex

latex/%.pdf: latex/%.tex 

latex/g52ifr.pdf: latex/g52ifr.tex $(TEX) 
	cd latex ; pdflatex g52ifr ; pdflatex g52ifr 

