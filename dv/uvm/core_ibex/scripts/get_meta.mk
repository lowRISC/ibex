define get-metadata-variable
    env PYTHONPATH=$(PYTHONPATH) python3 ./scripts/metadata.py \
    --op "print_field" \
    --dir-metadata $(METADATA-DIR) \
    --field $(1)
endef
define get-meta
    $(shell $(call get-metadata-variable,$(1)))
endef

# This is how you can get variables from the python metadata easily...
# testvar := $(call get-meta,"ibex_root")
