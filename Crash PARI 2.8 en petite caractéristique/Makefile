# Generic Makefile for PARI programs -- amd64 running linux (x86-64/GMP-6.1.0 kernel) 64-bit version
#
#  This file was created by Configure. Any change made to it will be
#  lost when Configure is run.
#
# make all will create
#  extgcd-dyn (linked dynamically with libpari)
#  extgcd-sta (linked statically)
#  libextgcd.so (to be used by "install" under GP)
#
# Under GP: install("extgcd", "GG&&", "gcdex", "./libextgcd.so") enables
# you to subsequently use gcdex to call extgcd (see the reference manual).
#

# change this TARGET to compile your own programs
TARGET = glue
SHELL  = /bin/sh

DBGFLAGS   = -g -Wall
CFLAGS     = -O3 -Wall -fno-strict-aliasing -fomit-frame-pointer
EXTRACFLAGS=
#CFLAGS    = $(DBGFLAGS)

# Various linkers use different flags to force static compilation. Choose
# the one which is relevant for your installation.
#
# Solaris ld (global)
#STATIC    = -dn

# Solaris ld (toggle: no shared object accepted until -B dynamic is seen
#STATIC    = -B static

# gcc
#STATIC    = -static

CC         = /usr/bin/gcc
#CPPFLAGS   = -I. -I/home/aurelien/local/include
CPPFLAGS   = -I. -I/home/aurelien/local2/include
LD         = /usr/bin/gcc
LDFLAGS    = -O3 -Wall -fno-strict-aliasing -fomit-frame-pointer    -Wl,--export-dynamic 
MODLD      = /usr/bin/gcc
MODLDFLAGS = -shared  $(CFLAGS) $(DLCFLAGS) -Wl,-shared 
#EXTRAMODLDFLAGS = -lc -lm -L/home/aurelien/local/lib -lpari
EXTRAMODLDFLAGS = -lc -lm -L/home/aurelien/local2/lib -lpari
EXTRALIBS  =

#RUNPTH     = -Wl,-rpath "/home/aurelien/local/lib"
RUNPTH     = -Wl,-rpath "/home/aurelien/local2/lib"
DLCFLAGS   = -fPIC
#LIBS       = -lm -L/home/aurelien/local/lib -lpari -lgmp
LIBS       = -lm -L/home/aurelien/local2/lib -lpari -lgmp
RM = rm -f


OBJS = $(TARGET).o
DYN = lib$(TARGET).so
ALL = $(TARGET)-sta $(TARGET)-dyn $(DYN)

dft: $(TARGET)-dyn

all: $(ALL)

sta: $(TARGET)-sta

dyn: $(TARGET)-dyn

dynlib: $(DYN)

$(DYN): $(OBJS)
	$(MODLD) -o $@ $(MODLDFLAGS) $(EXTRACFLAGS) $(OBJS) $(EXTRAMODLDFLAGS)

$(TARGET)-sta: $(OBJS)
	$(LD) -o $@ $(LDFLAGS) $(EXTRACFLAGS) $< $(EXTRALIBS) $(STATIC) $(LIBS)

$(TARGET)-dyn: $(OBJS)
	$(LD) -o $@ $(LDFLAGS) $(EXTRACFLAGS) $< $(EXTRALIBS) $(RUNPTH) $(LIBS)

%.o: %.c
	$(CC) -c $(CFLAGS) $(EXTRACFLAGS) $(CPPFLAGS) $(DLCFLAGS) $<
clean:
	-$(RM) *.o $(ALL)
