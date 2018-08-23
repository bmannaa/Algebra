all:
	happy -gca ParNewtonGrammar.y
	alex -g LexNewtonGrammar.x
	latex DocNewtonGrammar.tex; dvips DocNewtonGrammar.dvi -o DocNewtonGrammar.ps
	ghc --make TestNewtonGrammar.hs -o TestNewtonGrammar
clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f DocNewtonGrammar.ps
distclean: clean
	-rm -f DocNewtonGrammar.* LexNewtonGrammar.* ParNewtonGrammar.* LayoutNewtonGrammar.* SkelNewtonGrammar.* PrintNewtonGrammar.* TestNewtonGrammar.* AbsNewtonGrammar.* TestNewtonGrammar ErrM.* SharedString.* NewtonGrammar.dtd XMLNewtonGrammar.* Makefile*

