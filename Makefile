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

# Define if it is not already defined
CMAKE_BUILD_TYPE ?= RELEASE

ifeq ($(CMAKE_BUILD_TYPE), RELEASE)
  LEAN_BUILD_SUBDIR := release
else ifeq ($(CMAKE_BUILD_TYPE), DEBUG)
  LEAN_BUILD_SUBDIR := debug
else
  $(error Unknown $$CMAKE_BUILD_TYPE: $(CMAKE_BUILD_TYPE))
endif

#-------------------------------------------------------------------------------

# Lean directories
LEAN_DIR := $(shell $(READLINK) -f './lean')
LEAN_SRC_DIR := $(LEAN_DIR)/src
LEAN_BUILD_DIR := $(LEAN_DIR)/build/$(LEAN_BUILD_SUBDIR)
LEAN_BIN_DIR := $(LEAN_DIR)/bin

# Lean build dependencies: all files except for build and binary files.
LEAN_BUILD_DEPS := $(shell find '$(LEAN_DIR)' -path '$(LEAN_BUILD_DIR)' -prune -o -path '$(LEAN_BIN_DIR)' -prune -o -type f -print)

# Lean binaries
LEAN := $(LEAN_BIN_DIR)/lean
LEANPKG := $(LEAN_BIN_DIR)/leanpkg

#-------------------------------------------------------------------------------

# Build with default options
default: $(LEAN)
	$(LEANPKG) build

# Build without kernel extensions (may be slow)
noexts: $(LEAN)
	$(LEANPKG) build -- -t0

version: $(LEAN)
	$(LEAN) --version

clean:
	@find src _target -name '*.d' -or -name '*.clean' -or -name '*.olean' -delete
	@find src _target -type d -empty -delete

clean-lean: clean $(LEAN_BUILD_DIR)/Makefile
	@make clean -C $(LEAN_BUILD_DIR)
	@make clean-olean -C $(LEAN_BUILD_DIR)

#-------------------------------------------------------------------------------

# Build the Lean binary
$(LEAN): $(LEAN_BUILD_DIR) $(LEAN_BUILD_DEPS)
	# Undocumented Build/Home flags:
	# https://stackoverflow.com/a/20611964/545794
	# We use these flags to avoid relative directories (e.g. ../../src).
	cmake -DCMAKE_BUILD_TYPE=$(CMAKE_BUILD_TYPE) -B$(LEAN_BUILD_DIR) -H$(LEAN_SRC_DIR)
	@make -C $(LEAN_BUILD_DIR)
	@touch $(LEAN)

# Create the Lean build directory
$(LEAN_BUILD_DIR):
	mkdir -p $(LEAN_BUILD_DIR)
