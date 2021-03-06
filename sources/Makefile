
# ====================================
# Variable Definitions & Configuration
# ====================================

NAME=alt-ergo

# Include configuration makefile
# Since there is a rule to create/update this makefile, make
# should automatically run it and reload/restart if needed
include Makefile.config

# Some variables to help with adding
# flags and/or renaming the dune binary
DUNE=dune
DUNE_FLAGS=

# List the files:
# - generated by rules in this makefile,
# - used by the build process
#
# This excludes:
# - .ml files generated by menhir or ocamllex
#   (since they reside in dune specific directory)
GENERATED_USEFUL=lib/util/config.ml
GENERATED_LINKS=alt-ergo altgr-ergo
GENERATED=$(GENERATED_USEFUL) $(GENERATED_LINKS)


# =======
# Aliases
# =======

# IMPORTANT: this is the first rules, and as such the default
# run when "make is called", keep it as the first rule
world: all

# Small alias to re-generate necessary files for the build
gen: $(GENERATED_USEFUL)

# Convenient alias for running all configuration steps
conf: Makefile Makefile.config lib/util/config.ml

# Alias for generated artifacts
clean: generated-clean dune-clean ocamldot-clean

# Alias to remove all generated files
distclean: makefile-distclean release-distclean

# declare these aliases as phony
.PHONY: world gen conf clean distclean



# ===========
# Build rules
# ===========

# Build the alt-ergo lib
lib: gen
	$(DUNE) build $(DUNE_FLAGS) \
		lib/AltErgoLib.cma \
		lib/AltErgoLib.cmxa \
		lib/AltErgoLib.cmxs

# Build the cli/text alt-ergo bin
bin: gen
	$(DUNE) build $(DUNE_FLAGS) _build/install/default/bin/alt-ergo
	ln -sf _build/install/default/bin/alt-ergo alt-ergo

# Build the GUI
gui: gen
	$(DUNE) build $(DUNE_FLAGS) _build/install/default/bin/altgr-ergo
	ln -sf _build/install/default/bin/altgr-ergo altgr-ergo

# fm-simplex plugin
fm-simplex:
	$(DUNE) build $(DUNE_FLAGS) \
		_build/install/default/share/alt-ergo/plugins/fm-simplex-plugin.cma \
		_build/install/default/share/alt-ergo/plugins/fm-simplex-plugin.cmxs

# Ab-Why3 plugin
AB-Why3:
	$(DUNE) build $(DUNE_FLAGS) \
		_build/install/default/share/alt-ergo/plugins/AB-Why3-plugin.cma \
		_build/install/default/share/alt-ergo/plugins/AB-Why3-plugin.cmxs

# Build all plugins
plugins:
	$(DUNE) build $(DUNE_FLAGS) \
		_build/install/default/share/alt-ergo/plugins/fm-simplex-plugin.cma \
		_build/install/default/share/alt-ergo/plugins/fm-simplex-plugin.cmxs \
		_build/install/default/share/alt-ergo/plugins/AB-Why3-plugin.cma \
		_build/install/default/share/alt-ergo/plugins/AB-Why3-plugin.cmxs

# Alias to build all targets using dune
# Hopefully more efficient than making "all" depend
# on "lib", "bin" and "gui", since dune can
# parralelize more
all: gen
	$(DUNE) build $(DUNE_FLAGS) @install
	ln -sf _build/install/default/bin/alt-ergo alt-ergo
	ln -sf _build/install/default/bin/altgr-ergo altgr-ergo

# declare these targets as phony to avoid name clashes with existing directories,
# particularly the "plugins" target
.PHONY: lib bin gui fm-simplex AB-Why3 plugins all


# =====================
# Non-regressions tests
# =====================

# Run non-regression tests using the scripts in
# ../non-regression
non-regression: all
	cp _build/install/default/bin/alt-ergo ../non-regression/alt-ergo.opt
	cd ../non-regression &&  ./non-regression.sh
	rm ../non-regression/alt-ergo.opt

.PHONY: non-regression


# ============
# Installation
# ============

# Installation using dune is *NOT* recommended
# The good way to install alt-ergo is to use the alt-ergo.install
# file generated by dune, which specifies all files that need to
# be copied, and where they should be copied

# Use dune to install the lib, bin, and gui
install: all
	$(DUNE) install $(DUNE_FLAGS)		\
		--prefix $(prefix)						\
		--libdir $(libdir)

# Use dune to uninstall the lib, bin, and gui
uninstall:
	$(DUNE) uninstall $(DUNE_FLAGS)	\
		--prefix $(prefix)						\
		--libdir $(libdir)

.PHONY: install uninstall


# ========================
# Documentation generation
# ========================

# Build the documentation
doc:
	$(DUNE) build $(DUNE_FLAGS) @doc

# Open the generated html doc in browser
html: doc
	xdg-open _build/default/_doc/_html/index.html

.PHONY: doc html

# ========================
# Configuration generation
# ========================

# The hand-written configure script is used to query
# opam (or accept user spec) to set a few variables,
# and generate the Config module, which stores information
# about destination directories, including plugin directories
Makefile.config lib/util/config.ml: configure configure.ml
	./configure


# ================
# Dependency graph
# ================

../extra/ocamldot/ocamldot:
	cd ../extra/ocamldot/ && $(MAKE) bin

# plot the dependency graph
# specifying all dependencies is really, really bothersome,
# so we just put the ocamldot executable as dep
archi: ../extra/ocamldot/ocamldot
	ocamldep \
		-I lib/frontend/ -I lib/reasoners/ -I lib/structures/ -I lib/util/ \
		-I parsers/ -I tools/text/ -I tools/gui/ \
		lib/frontend/*.ml lib/reasoners/*.ml lib/structures/*.ml lib/util/*.ml \
		parsers/*.ml tools/text/*.ml tools/gui/*.ml | \
		../extra/ocamldot/ocamldot | grep -v "}" > archi.dot
	cat ../extra/subgraphs.dot >> archi.dot
	echo "}" >> archi.dot
	dot -Tpdf archi.dot > archi.pdf

.PHONY: archi

# ===============
# PUBLIC RELEASES
# ===============

# Get the current commit hash and version number
COMMIT_ID = $(shell git log -1 | grep commit | cut -d " " -f 2)
VERSION=$(shell grep "=" lib/util/version.ml | cut -d"=" -f2 | head -n 1)

# Some convenient variables
PUBLIC_VERSION=$(VERSION)
PUBLIC_RELEASE=alt-ergo-$(PUBLIC_VERSION)
PUBLIC_TARGZ=$(PUBLIC_RELEASE).tar.gz
FILES_DEST=../public-release/$(PUBLIC_RELEASE)/$(PUBLIC_RELEASE)

public-release:
	rm -rf ../public-release
	mkdir -p $(FILES_DEST)
	cp configure $(FILES_DEST)
	git clean -dfx
	cp ../License.OCamlPro ../OCamlPro-Non-Commercial-License.txt ../OCamlPro-Non-Commercial-License.pdf ../LGPL-License.txt ../Apache-License-2.0.txt $(FILES_DEST)/
	cp ../README.md ../LICENSE.md ../COPYING.md $(FILES_DEST)/
	cp Makefile $(FILES_DEST)/
	cp INSTALL.md alt-ergo.opam CHANGES $(FILES_DEST)/
	cp -rf lib tools parsers plugins preludes examples doc $(FILES_DEST)/
	#echo "let version=\"$(PUBLIC_VERSION)\"" >> $(FILES_DEST)/lib/util/version.ml
	echo "let release_commit = \"$(COMMIT_ID)\"" >> $(FILES_DEST)/lib/util/version.ml
	echo "let release_date = \""`LANG=en_US; date`"\"" >> $(FILES_DEST)/lib/util/version.ml
	cd $(FILES_DEST)/.. && tar cfz $(PUBLIC_TARGZ) $(PUBLIC_RELEASE)
	rm -rf $(FILES_DEST)

# ==============
# Cleaning rules
# ==============

# Cleanup generated files
generated-clean:
	rm -rf $(GENERATED)

# Clean build artifacts
dune-clean:
	$(DUNE) clean

# Clean ocamldot's build artifacts
ocamldot-clean:
	cd ../extra/ocamldot && $(MAKE) clean

# Cleanup all makefile-related files
makefile-distclean:
	rm -rf Makefile.config

# Clenaup release generated files and dirs
release-distclean:
	rm -rf ../public-release

.PHONY: generated-clean dune-clean makefile-distclean release-distclean

emacs-edit:
	emacs `find . -name '*'.ml* | grep -v _build` &
