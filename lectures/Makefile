MODULES       := Intro Prop Pred
TEX           := $(MODULES:%=latex/%.v.tex)
VS            := $(MODULES:%=src/%.v)
VS_DOC        := $(MODULES:%=%.v)

.PHONY: notes html src

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

latex/Pred.v.tex: Makefile src/Pred.v 
	cd src ; coqdoc --interpolate --latex --body-only -s \
		Pred.v -o ../latex/Pred.v.tex

src : $(VS)
	mkdir -p ../www/src
	cp src/*.v ../www/src

latex/%.pdf: latex/%.tex 

latex/g52ifr.pdf: latex/g52ifr.tex $(TEX)
	cd latex ; pdflatex g52ifr ; pdflatex g52ifr ; cp g52ifr.pdf ../../www

html: Makefile $(VS) 
	mkdir -p ../www/html
	cd src; coqdoc --interpolate $(VS_DOC) -d ../../www/html
	
