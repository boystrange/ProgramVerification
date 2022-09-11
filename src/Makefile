
NULL =

HTMLDIR = ../pages

all: Main.lagda.md
	( \
		TEMPDIR=`mktemp -d`; \
		agda --html-dir=$$TEMPDIR --html --html-highlight=auto $^; \
		rsync -r -c -v --delete $$TEMPDIR/ $(HTMLDIR)/; \
	)

dependencies.dot: Main.lagda.md
	agda --dependency-graph=$@ Main.lagda.md

dependencies.pdf: dependencies.dot
	dot -Tpdf $< >$@

clean:
	rm -f dependencies.* $(HTMLDIR)/*
