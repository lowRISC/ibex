TARGET=cheriot-architecture.pdf
MAIN_TEX=cheriot-architecture.tex
SAIL_LATEX_RISCV_DIR=sail_latex_riscv

SOURCES=$(wildcard *.tex insn-riscv/*.tex $(SAIL_LATEX_RISCV_DIR)/*.tex) cheri.bib LICENSE LICENSE-sail-cheri-riscv LICENSE-sail-riscv

TIKZFIGURES=fig-representable-regions.pdf fig-sentry-plt.pdf fig-type-token.pdf
FIGSOURCES=						\
	misc/perms/perms5_clustered.pdf \
	$(TIKZFIGURES)

V?=0
ifeq ($(V),0)
INTERACTION=batchmode
TEXLOGANALYSER_FLAGS=-w
else
INTERACTION=nonstopmode
# Also include page numbers to make it easier to find what caused the warning
TEXLOGANALYSER_FLAGS=-w -n
endif

LATEXMK_COMMON_FLAGS=-bibtex -pdf
PDFLATEX_FLAGS=-file-line-error -halt-on-error -interaction=$(INTERACTION)

.PHONY: all
all: sail-latex ${TARGET}

# The texloganalyser tool can be used to find all warning messages in the latex
# logfile which is useful when using interaction=batchmode. There is also
# a python package pydflatex that does the same thing (but with colours).
# Howver, texloganalyser is included by default in some TeX distributions so
# prefer that one.
# TODO: fix the broken sail hyperrefs so we don't have to filter the out.
${TARGET}: ${SOURCES} ${FIGSOURCES}
	latexmk $(LATEXMK_COMMON_FLAGS) $(MAIN_TEX) $(PDFLATEX_FLAGS); ret=$$?; \
	    if command -v texloganalyser >/dev/null 2>/dev/null; then \
	        texloganalyser $(TEXLOGANALYSER_FLAGS) build/cheri-architecture.log; \
	    fi; exit $$ret

$(TIKZFIGURES): %.pdf: %.tex Makefile
	latexmk $(LATEXMK_COMMON_FLAGS) $(PDFLATEX_FLAGS) $<

.PHONY: figures
figures: $(TIKZFIGURES)

.PHONY: quick
quick:
	pdflatex $(MAIN_TEX) $(PDFLATEX_FLAGS)
	@(echo "pdflatex only run once so build may be incomplete")

# The sed commands require GNU sed
ifeq ($(shell uname -s),Linux)
SED?=sed
else
SED?=gsed
endif

# Work around `find: fts_read: Invalid argument` on macOS
ifeq ($(shell uname -s),Darwin)
FIND?=gfind
else
FIND?=find
endif

SAIL_CHERI_RISCV_DIR?=..
sail-latex:
	rm -rf $(SAIL_LATEX_RISCV_DIR)
	$(MAKE) -C $(SAIL_CHERI_RISCV_DIR) latex
	mv $(SAIL_CHERI_RISCV_DIR)/$(SAIL_LATEX_RISCV_DIR) .
	$(FIND) $(SAIL_LATEX_RISCV_DIR) -type f -name 'fcl*zexecute*.tex' -exec $(SED) -i -e '1d; 2{/^{$$/d}; $$d; s/^  //;' {} +
	touch $(SAIL_LATEX_RISCV_DIR)/0GENERATED_FILES_DO_NOT_EDIT
	touch $(SAIL_LATEX_RISCV_DIR)/zGENERATED_FILES_DO_NOT_EDIT
	$(FIND) $(SAIL_LATEX_RISCV_DIR) -type f -exec chmod -w {} +

.PHONY: clean update-sail-defs sail-latex
clean:
	latexmk -C $(LATEXMK_COMMON_FLAGS) $(MAIN_TEX)
	latexmk -C $(LATEXMK_COMMON_FLAGS) fig-*.tex
	rm -f $(TARGET) $(TIKZFIGURES)

cheri-sorted.bib: cheri.bib bib-sorting.conf
	biber --tool $< --sortcase=false --strip-comments --sortdebug --isbn13 --isbn-normalise --fixinits \
	    --output_indent=4 --output_fieldcase=lower --sortlocale=en_GB \
	    --configfile=bib-sorting.conf --validate-config --output-file=$@


.PHONY: check-bibliography check-bibliography-strict
check-bibliography:
	# For more detailed output add --debug
	biber --tool cheri.bib

check-bibliography-strict:
	biber --tool --validate-datamodel cheri.bib | grep -v "Missing mandatory field 'editor'" | grep -v "is not an integer"
