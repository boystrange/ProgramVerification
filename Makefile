
NULL =

NAME = ProVer

PDFS  = $(SECTIONS:%=assets/pdf/%.pdf)
DEPS  = \
  _includes/prima_slide.md \
  _includes/defaults_common.dot \
  _includes/defaults_automaton.dot \
  _includes/defaults_tree.dot \
  _layouts/slide.html \
  assets/css/main.scss \
  $(NULL)

serve:
	bundle exec jekyll serve --incremental

build:
	bundle exec jekyll build

all: $(TARGETS:%=target/%.md)

fake:
	touch $(PDFS)

zip:
	( \
		bundle exec jekyll build -d $(NAME); \
		NAMEDATE="$(NAME)_`date +'%d_%m_%Y'`"; \
		zip --filesync -b /tmp -r "$$NAMEDATE".zip $(NAME) \
	)

.PHONY: Library.zip
Library.zip:
	( \
		cd src; \
		zip ../$@ `find . -name "*.agda"`\
	)

assets/pdf/%.pdf: target/%.md $(DEPS)
	@echo "Converting" $< "..."
	@node js/print.js http://localhost:4000/$(<:%.md=%.html)?handout $@ A5 landscape

%.pdf: esami/%.md $(DEPS) assets/css/esame.scss
	node js/print.js http://localhost:4000/$(<:%.md=%.html) $@ A4 portrait

target/%.md: source/%.lagda.md
	agda --html-dir=target --html --html-highlight=code $<

clean:
	rm -f $(PDFS) $(NAME).zip
