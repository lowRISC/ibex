.PHONY: all
all: perms.svg

perms.dot: perms.py
	./perms.py | tred > $@

%.svg : %.dot
	dot -Tsvg -o $@ $<


%.png : %.dot
	dot -Tpng -o $@ $<


%.pdf : %.dot
	dot -Tpdf -o $@ $<

.PHONY: clean
clean:
	rm perms.svg perms.dot
