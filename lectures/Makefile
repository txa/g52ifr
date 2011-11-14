MODULES       := Intro Prop Pred Bool Sets Arith Lists Expr Meta
TEX           := $(MODULES:%=latex/%.v.tex)
VS            := $(MODULES:%=src/%.v)
VS_DOC        := $(MODULES:%=%.v)

.PHONY: notes html src all

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

latex/Bool.v.tex: Makefile src/Bool.v 
	cd src ; coqdoc --interpolate --latex --body-only -s \
		Bool.v -o ../latex/Bool.v.tex

latex/Sets.v.tex: Makefile src/Sets.v 
	cd src ; coqdoc --interpolate --latex --body-only -s \
		Sets.v -o ../latex/Sets.v.tex

latex/Arith.v.tex: Makefile src/Arith.v 
	cd src ; coqdoc --interpolate --latex --body-only -s \
		Arith.v -o ../latex/Arith.v.tex

latex/Lists.v.tex: Makefile src/Lists.v 
	cd src ; coqdoc --interpolate --latex --body-only -s \
		Lists.v -o ../latex/Lists.v.tex

latex/Expr.v.tex: Makefile src/Expr.v 
	cd src ; coqdoc --interpolate --latex --body-only -s \
		Expr.v -o ../latex/Expr.v.tex

latex/Meta.v.tex: Makefile src/Meta.v 
	cd src ; coqdoc --interpolate --latex --body-only -s \
		Meta.v -o ../latex/Meta.v.tex
src : $(VS)
	mkdir -p ../www/src
	cp src/*.v ../www/src

latex/%.pdf: latex/%.tex 

latex/g52ifr.pdf: latex/g52ifr.tex $(TEX)
	cd latex ; pdflatex g52ifr ; pdflatex g52ifr ; cp g52ifr.pdf ../../www

html: Makefile $(VS) 
	mkdir -p ../www/html
	cd src; coqdoc --interpolate $(VS_DOC) -d ../../www/html

all : html src notes
