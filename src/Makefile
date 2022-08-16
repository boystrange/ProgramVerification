
NULL =

ROOTS = \
  Library.lagda.md \
  Chapters.lagda.md \
  $(NULL)

HTMLDIR = ../pages

all: $(ROOTS)
	for i in $^; do agda --html-dir=$(HTMLDIR) --html --html-highlight=auto $$i; done

dependencies.dot: Main.lagda.md
	agda --dependency-graph=$@ Main.lagda.md

dependencies.pdf: dependencies.dot
	dot -Tpdf $< >$@

clean:
	rm -f dependencies.* $(HTMLDIR)/*
