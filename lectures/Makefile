MODULES       := Intro Prop
TEX           := $(MODULES:%=latex/%.v.tex)
VS            := $(MODULES:%=src/%.v)

.PHONY: notes html

notes: latex/g52ifr.pdf

latex/%.v.tex: Makefile src/%.v 
	cd src ; coqdoc --interpolate --latex --body-only -s \
		$*.v -o ../latex/$*.v.tex

latex/Intro.v.tex: Makefile src/Intro.v 
	cd src ; coqdoc --interpolate --latex --body-only -s \
		Intro.v -o ../latex/Intro.v.tex

latex/Prop.v.tex: Makefile src/Prop.v 
	cd src ; coqdoc --interpolate --latex --body-only -s \
		Prop.v -o ../latex/Prop.v.tex

latex/%.pdf: latex/%.tex 

latex/g52ifr.pdf: latex/g52ifr.tex $(TEX)
	cd latex ; pdflatex g52ifr ; pdflatex g52ifr 

html: Makefile $(VS) 
	mkdir -p html
	coqdoc --interpolate $(VS) -d html

