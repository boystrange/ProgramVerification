
NULL =

HTMLDIR = ../pages

all: Main.lagda.md
	agda --html-dir=$(HTMLDIR) --html --html-highlight=auto $^

dependencies.dot: Main.lagda.md
	agda --dependency-graph=$@ Main.lagda.md

dependencies.pdf: dependencies.dot
	dot -Tpdf $< >$@

clean:
	rm -f dependencies.* $(HTMLDIR)/*
