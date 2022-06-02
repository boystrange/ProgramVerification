
all: Main.lagda.md
	agda --html-dir=../pages --html --html-highlight=auto $<

dependencies.dot: Main.lagda.md
	agda --dependency-graph=$@ Main.lagda.md

dependencies.pdf: dependencies.dot
	dot -Tpdf $< >$@

clean:
	rm -f dependencies.*
