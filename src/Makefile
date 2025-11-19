
NULL =

HTMLDIR = ../_pages

all: Main.lagda.md
	( \
		TEMPDIR=`mktemp -d`; \
		agda --html-dir=$$TEMPDIR --html --html-highlight=auto $^; \
		for f in $$TEMPDIR/*.html; do sed -f ../insert.sed -i .bak $$f; done; \
		sed -f ../insert.sed -i .bak $$TEMPDIR/Agda.css; \
		rm -f $$TEMPDIR/*.bak; \
		rsync -r -c -v --delete $$TEMPDIR/ $(HTMLDIR)/; \
	)

dependencies.dot: Main.lagda.md
	agda --dependency-graph=$@ Main.lagda.md

dependencies.pdf: dependencies.dot
	dot -Tpdf $< >$@

clean:
	rm -f dependencies.* $(HTMLDIR)/*
