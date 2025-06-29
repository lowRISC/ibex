## redmule config
REDMULE_ROOT_DIR :=$(shell bender path redmule)
include $(REDMULE_ROOT_DIR)/bender_common.mk
include $(REDMULE_ROOT_DIR)/bender_sim.mk
include $(REDMULE_ROOT_DIR)/bender_synth.mk
