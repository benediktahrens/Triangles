#######################################################
# BINARIES

LIBS=-R . Cat

COQC=$(COQBIN)coqc $(LIBS)
COQDEP=$(COQBIN)coqdep $(LIBS)

#######################################################
# FILES

FILES=\
	  InfiniteTriangles/redecInfiniteTriangles8_4.v   \
	  Misc/Unicode.v                                  \
	  Theory/Notations.v                              \
	  Theory/SetoidType.v                             \
	  Theory/Category.v                               \
	  Theory/Functor.v                                \
	  Theory/RelativeComonad.v                        \
	  Category/Types.v                                \
	  Category/Setoids.v                              \
	  Category/Types_Setoids.v                        \
	  Category/RComonad.v                             \
	  Theory/Comodule.v                               \
	  Category/RComod.v                               \
	  Theory/Product.v                                \
	  Theory/Isomorphism.v                            \
	  Theory/CartesianStrongMonoidal.v                \
	  Theory/RelativeComonadWithCut.v                 \
	  Category/RComonadWithCut.v                      \
	  Theory/ProductInContext.v                       \
	  Theory/PushforwardComodule.v                    \
	  Category/Triangles.v

ALL= $(FILES)

#######################################################
# TARGETS

.SUFFIXES: .v .vo
.PHONY: all files depend

all: $(ALL:.v=.vo)
files: $(FILES:.v=.vo)
depend: .depend

.v.vo : .depend
	$(COQC) $<


#######################################################
#DEPENDENCIES

.depend : $(ALL)
	$(COQDEP) -I . $(ALL) > .depend

ifeq ($(findstring $(MAKECMDGOALS),depend clean),)
include .depend
endif
