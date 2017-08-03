OPTIMIZE  := -O3
OPTIMORE  := -O10 -foptimize-sibling-calls -finline-functions -fcse-follow-jumps -fcse-skip-blocks -frerun-cse-after-loop -frerun-loop-opt -fgcse # -fomit-frame-pointer
INCLUDES  := $(FM_INCLUDE) -include $(FM)/Global/Global.h -I$(FM)/ADTs -I$(FM)/Lib/Include -I$(PWD)
OBJS      := $(sort $(addsuffix .o, $(basename $(wildcard *.C *.l *.env))))
ifdef EXTENSION
  XOBJS    := $(sort $(addsuffix .o, $(basename $(wildcard ext_$(EXTENSION)/*.C ext_$(EXTENSION)/*.def ext_$(EXTENSION)/*.l ext_$(EXTENSION)/*.env))))
  OBJS     := $(filter-out $(notdir $(XOBJS)), $(OBJS)) $(XOBJS)
endif
GOBJS     := $(FM)/Global/Global.o $(FM)/ADTs/File.o
EXEC      := $(notdir $(shell pwd))
DEP_FILES := $(addsuffix .C, $(basename $(OBJS)))
