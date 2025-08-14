ROOT_DIR            :=  $(shell git rev-parse --show-toplevel)
REDMULE_ROOT_DIR    :=  $(ROOT_DIR)/vendor/redmule
mkfile_path         :=  $(ROOT_DIR)/isolde/sw/redmule_test


TEST_SRCS   := golden.h  tensor_dim.h  w_input.h  x_input.h  y_input.h

all: copy_headers



TEST_SRCS := golden.h tensor_dim.h w_input.h x_input.h y_input.h

# Directories
SRC_DIR          := $(REDMULE_ROOT_DIR)/sw/inc
DST_DIR          := $(mkfile_path)/inc
# Full paths to source and destination files
TEST_SRC_PATHS   := $(addprefix $(SRC_DIR)/, $(TEST_SRCS))
DST_FILES        := $(addprefix $(DST_DIR)/, $(TEST_SRCS))

# Ensure the destination directory exists
$(DST_DIR):
	@mkdir -p $@

# Rule to copy headers with dependency tracking
$(DST_DIR)/%.h:  $(SRC_DIR)/%.h 
	@cp $< $@
	@echo "Copied $< to $@"

copy_headers: $(DST_DIR)  $(DST_FILES)
	@echo "All header files copied to $(DST_DIR)"


.PHONY:  clean	
clean:
	rm -rf $(DST_DIR) 

.PHONY:  golden
golden: copy_headers
	