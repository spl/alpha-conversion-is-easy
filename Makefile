# Use the appropriate readlink command for absolute paths
# OS check adapted from: https://stackoverflow.com/a/12099167/545794
OS_NAME := $(shell uname -s)
ifeq ($(OS_NAME),Darwin)
  # If macOS
  READLINK := $(shell command -v greadlink 2> /dev/null)
  ifndef READLINK
    $(error greadlink on macOS and not found in path: brew install coreutils)
  endif
else
  # Otherwise Linux is assumed
  READLINK := $(shell command -v readlink 2> /dev/null)
  ifndef READLINK
    $(error readlink not found in path.)
  endif
endif

#-------------------------------------------------------------------------------

# Lean directories
LEAN_DIR := $(shell $(READLINK) -f './lean')
LEAN_SRC_DIR := $(LEAN_DIR)/src
LEAN_BUILD_DIR := $(LEAN_DIR)/build/release
LEAN_BIN_DIR := $(LEAN_DIR)/bin

# Lean build dependencies: all files except for build and binary files.
LEAN_BUILD_DEPS := $(shell find '$(LEAN_DIR)' -path '$(LEAN_BUILD_DIR)' -prune -o -path '$(LEAN_BIN_DIR)' -prune -o -type f -print)

# Lean binaries
LEAN := $(LEAN_BIN_DIR)/lean
LEANPKG := $(LEAN_BIN_DIR)/leanpkg

#-------------------------------------------------------------------------------

default: $(LEAN)
	$(LEANPKG) build

clean:
	@find src -name '*.d' -or -name '*.clean' -or -name '*.olean' | xargs rm

clean-lean: clean $(LEAN_BUILD_DIR)/Makefile
	@make clean -C $(LEAN_BUILD_DIR)
	@make clean-olean -C $(LEAN_BUILD_DIR)

#-------------------------------------------------------------------------------

# Build the Lean binary
$(LEAN): $(LEAN_BUILD_DEPS)
	# Undocumented Build/Home flags:
	# https://stackoverflow.com/a/20611964/545794
	# We use these flags to avoid relative directories (e.g. ../../src).
	cmake -B$(LEAN_BUILD_DIR) -H$(LEAN_SRC_DIR)
	@make -C $(LEAN_BUILD_DIR)
	@touch $(LEAN)

# Create the Lean build directory
$(LEAN_BUILD_DIR):
	mkdir -p $(LEAN_BUILD_DIR)
