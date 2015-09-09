ROOT_DIR           = .
CONTENT_SRC        = content
MAIN_SRC           = datasheet
FIG_DIR            = figures
FIG_RAW_DIR        = figures_raw


# Get only the path to the Tgif source files.
TGIF_SRCS       = $(wildcard $(ROOT_DIR)/$(FIG_RAW_DIR)/*.obj)
TGIF_SRCS_NAMES = $(basename $(TGIF_SRCS))

# Get only the path to the Tgif destination files.
TGIF_DEST       = $(wildcard $(ROOT_DIR)/$(FIG_DIR)/*.obj)
TGIF_DEST_NAMES = $(basename $(TGIF_SRCS))

# Derive the file names for the resulting EPS and PDF file names for
# the TGIF sources.
TGIF_OUTP_NAMES     = $(addprefix $(ROOT_DIR)/$(FIG_DIR)/, $(notdir $(TGIF_SRCS_NAMES)))
TGIF_OUTP_EPS_NAMES = $(addsuffix .eps, $(TGIF_OUTP_NAMES))
TGIF_OUTP_PDF_NAMES = $(addsuffix .pdf, $(TGIF_OUTP_NAMES))



######################################################################
#####                                                                #
#####     Main Targets                                               #
#####                                                                #
######################################################################
do: pdf

all: figures pdf
	make -B pdf
	make -B pdf

pdf: $(MAIN_SRC).pdf

%.pdf: %.tex $(CONTENT_SRC) preamble/preamble.tex
	pdflatex $(MAIN_SRC).tex

clean: clean-figures
	@echo "***** Cleaning the LaTeX directory structure."
	@rm -rf $(ROOT_DIR)/*.acr $(ROOT_DIR)/*.alg $(ROOT_DIR)/*.bbl 
	@rm -rf $(ROOT_DIR)/*.blg $(ROOT_DIR)/*.glg $(ROOT_DIR)/*.gls 
	@rm -rf $(ROOT_DIR)/*.aux $(ROOT_DIR)/*.glo $(ROOT_DIR)/*.ist
	@rm -rf $(ROOT_DIR)/*.lof $(ROOT_DIR)/*.log $(ROOT_DIR)/*.lot 
	@rm -rf $(ROOT_DIR)/*.toc $(ROOT_DIR)/*.acn $(ROOT_DIR)/*.out
	@rm -rf $(ROOT_DIR)/*.tex~ $(ROOT_DIR)/*.tex.backup
	@rm -rf $(ROOT_DIR)/*.fdb_latexmk $(ROOT_DIR)/*.fls
	@rm -rf $(ROOT_DIR)/Makefile~ $(ROOT_DIR)/pso.conv-*
	@rm -rf $(ROOT_DIR)/auto
	@rm -rf $(ROOT_DIR)/content/*.tex~ $(ROOT_DIR)/content/*.aux
	@rm -rf $(ROOT_DIR)/content/*.log $(ROOT_DIR)/content/auto
	@rm -rf $(ROOT_DIR)/content/*.tex.backup
	@rm -rf $(ROOT_DIR)/content/*.fdb_latexmk $(ROOT_DIR)/content/*.fls
	@rm -rf $(ROOT_DIR)/glossaries/*.tex~ $(ROOT_DIR)/glossaries/auto
	@rm -rf $(ROOT_DIR)/preamble/auto $(ROOT_DIR)/preamble/*.tex~
	@rm -rf $(ROOT_DIR)/preamble/*.log
	@rm -rf $(ROOT_DIR)/bib/auto $(ROOT_DIR)/bib/*.bib~
	@rm -rf $(ROOT_DIR)/bib/*.bib.backup
	@rm -rf $(ROOT_DIR)/*.mtc* $(ROOT_DIR)/*.maf


######################################################################
#####                                                                #
#####     Sub Targets                                                #
#####                                                                #
######################################################################

figures: tgif_figures

tgif_figures: $(TGIF_OUTP_PDF_NAMES)


$(TGIF_OUTP_PDF_NAMES): $(ROOT_DIR)/$(FIG_DIR)/%.pdf : $(ROOT_DIR)/$(FIG_RAW_DIR)/%.obj
	@echo "*****"
	@echo "***** Printing Tgif figure:"
	@echo "***************************"
	@echo "***** $(ROOT_DIR)/$(FIG_RAW_DIR)/$*.eps"
	@tgif -print -epsi -color -quiet $(ROOT_DIR)/$(FIG_RAW_DIR)/$*.obj
	@echo "*****"
	@echo "***** Converting Tgif EPS to PDF:"
	@echo "*********************************"
	@echo "***** $(ROOT_DIR)/$(FIG_RAW_DIR)/$*.eps --> $(ROOT_DIR)/$(FIG_RAW_DIR)/$*.pdf"
	@epstopdf $(ROOT_DIR)/$(FIG_RAW_DIR)/$*.eps
	@echo "*****"
	@echo "***** Moving EPS and PDF figures"
	@echo "********************************"
	@echo "***** $(ROOT_DIR)/$(FIG_RAW_DIR)/$*.eps --> $(ROOT_DIR)/$(FIG_DIR)/$*.eps"
	@echo "***** $(ROOT_DIR)/$(FIG_RAW_DIR)/$*.pdf --> $(ROOT_DIR)/$(FIG_DIR)/$*.pdf"
	-@mv $(ROOT_DIR)/$(FIG_RAW_DIR)/$*.eps $(ROOT_DIR)/$(FIG_DIR)/
	-@mv $(ROOT_DIR)/$(FIG_RAW_DIR)/$*.pdf $(ROOT_DIR)/$(FIG_DIR)/
	@echo "*****"

clean-tgif-figures:
	-@rm -f $(TGIF_OUTP_EPS_NAMES) $(TGIF_OUTP_PDF_NAMES)

clean-figures: clean-tgif-figures
