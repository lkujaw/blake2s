TOP_DIR=$(shell cd ..; pwd)

BIN_SDIR=$(TOP_DIR)/gnat/sbin
BIN_DDIR=$(TOP_DIR)/gnat/dbin
BIN_ADIR=$(TOP_DIR)/bin
BIN_DLOC=$(BIN_DDIR)/b2ssum
BIN_ALOC=$(BIN_ADIR)/b2ssum.adb
BIN_SNMS=$(addprefix $(BIN_SDIR)/,b2ssum b2stest)

LIB_NAME=ab2s
LIB_SDIR=$(TOP_DIR)/gnat/slib
LIB_DDIR=$(TOP_DIR)/gnat/dlib
LIB_ADIR=$(TOP_DIR)/common
LIB_ALOC=$(LIB_ADIR)/blake2s.adb

ifeq ($(OS),Windows_NT)
	SYSNAME := Windows
else
	SYSNAME := $(shell uname -s)
endif

# Default
LIB_SLOC=$(LIB_SDIR)/lib$(LIB_NAME).a
LIB_DLOC=$(LIB_DDIR)/lib$(LIB_NAME).so

ifeq ($(SYSNAME), Darwin)
	LIB_DLOC=$(LIB_DDIR)/lib$(LIB_NAME).dylib
	LDFLAGS=-dynamiclib -fPIC
endif
ifeq ($(SYSNAME), Linux)
	LDFLAGS=-shared -fPIC
endif

GCCFLAGS=-O3
ADAFLAGS=-gnatN -gnata -gnatk8 -gnatwadl -gnaty3abcdefhiklmnprtux -q $(GCCFLAGS)
ADABINFLAGS=-gnatec=$(TOP_DIR)/gnat/bin.adc $(ADAFLAGS)
ADALIBFLAGS=-gnatec=$(TOP_DIR)/gnat/lib.adc $(ADAFLAGS)
ADA83=$(shell gnatmake 2>&1|grep -q -- '-gnat83' && echo "-gnat83")
ADA95=$(shell gnatmake 2>&1|grep -q -- '-gnat95' && echo "-gnat95")

GLIB=$(shell gnatls -v|grep adalib|sed -e 's: ::g')

all: $(BIN_SNMS) $(BIN_DLOC) test

.PHONY: FORCE

$(LIB_SDIR) $(LIB_DDIR) $(BIN_SDIR) $(BIN_DDIR):
	@mkdir $@

.SECONDEXPANSION:
$(BIN_SNMS): %: $(BIN_ADIR)/$$(notdir %).adb $(BIN_SDIR) $(LIB_SLOC)
	gnatmake $(ADABINFLAGS) $(ADA95) -aI$(TOP_DIR)/gnat $(LIB_ADIR:%=-aI%) -D $(BIN_SDIR) -o $@ $<

$(BIN_DLOC): $(BIN_ALOC) $(BIN_DDIR) $(LIB_DLOC)
	gnatmake $(ADABINFLAGS) $(ADA95) -aI$(TOP_DIR)/gnat $(LDFLAGS) -c $(BIN_ALOC) -D $(BIN_DDIR) $(LIB_ADIR:%=-aI%) $(LIB_DDIR:%=-aO%)
	cd $(BIN_DDIR) && \
		gnatbind -shared $(LIB_DDIR:%=-aO%) -x $(BIN_DLOC).ali && \
		gnatlink $(BIN_DLOC).ali $(GCCFLAGS) $(LIB_NAME:%=-l%) -o $(BIN_DLOC)
# Changing the working directory is what gnatmake does, and there
# seems to be no other way to get gnatbind and gnatlink to work otherwise.

$(LIB_SLOC):: $(LIB_SDIR)
	gnatmake $(ADALIBFLAGS) $(ADA83) -aI$(TOP_DIR)/gnat -c $(LIB_ALOC) -D $(LIB_SDIR)
	ar -c -r -u $(LIB_SLOC) $(LIB_SDIR)/*.o

$(LIB_DLOC):: $(LIB_DDIR)
	gnatmake $(ADALIBFLAGS) $(ADA83) -aI$(TOP_DIR)/gnat $(LDFLAGS) -c $(LIB_ALOC) -D $(LIB_DDIR)
	gcc $(LDFLAGS) -o $(LIB_DLOC) $(LIB_DDIR)/*.o -L$(GLIB) -lgnat

test:: $(BIN_SDIR)/b2stest $(TOP_DIR)/tests/blake2s.txt
	@cd $(TOP_DIR)/tests && \
		$(BIN_SDIR)/b2stest | tee test.out && \
			cmp test.out test.cmp

gnat.sum:: FORCE spark.smf
	@spark @spark.smf
	@sparksimp
	@isabelle build -D . -e
	@pogs

adactl:: ../blake2sn.aru quadlets.adb
	@gnatmake -I../common -gnat95 -gnatk8 -gnatct -q quadlets.adb
	@adactl -e -f ../blake2sn.aru -r quadlets.adt
	@echo "Passed AdaControl"
	-@rm -f *.adt *.ali

adactl.old:: ../blake2so.aru quadlets.adb
	@gnatmake -I../common -gnat95 -gnatk8 -gnatct -q quadlets.adb
	@adactl -e -f ../blake2so.aru -r quadlets.adt
	@echo "Passed AdaControl"
	-@rm -f *.adt *.ali

clean::
	-@rm -f dbin/* sbin/* dlib/* slib/*
	-@rm -f $(TOP_DIR)/tests/*.out
	-@rm -f quadlets/*.prv
	-@sparkclean -examiner -simplifier
	-@rm -f *~ *.adt *.ali *.lst *.o *.rep *.sli *.stderr *.stdout
