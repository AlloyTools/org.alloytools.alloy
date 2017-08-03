### This file assumes OPTIMIZE, OPTIMOR, INCLUDES, OBJS, GOBJS, EXEC, DEP_FILES to be defined.
### (OBJS are object files generated from ".C" files)


## Compilation:
##
COMPILE_STANDARD = -m32 -ggdb -D DEBUG $(OPTIMIZE) $(DEBUG) $(INCLUDES) $(FM_COPTS)
COMPILE_PROFILE	 = -m32 -pg -ggdb -D DEBUG $(OPTIMIZE) $(DEBUG) $(INCLUDES) $(FM_COPTS)
COMPILE_DEBUG	 = -m32 -ggdb -D DEBUG -D PARANOID -O0 $(DEBUG) $(INCLUDES) $(FM_COPTS)
COMPILE_RELEASE	 = -m32 -D NDEBUG -D RELEASE $(OPTIMORE) $(INCLUDES) $(FM_COPTS)
COMPILE_EXTRA	 = -m32 $(COMPILE_STANDARD) -cxxlib-icc

compile-C  = if [ "$(notdir $<)" = "$<" ] || extdir "$<"; then echo Compiling: $<; g++ -c -Wall $(COMPILE_STANDARD) -o $@ $<; else echo Compiling: $<; (if [ -e $(dir $<)/Makefile ]; then make -C $(dir $<) $(notdir $@); else make -f $(FM)/standard.mak -C $(dir $<) $(notdir $@); fi) ; fi
compile-Cp = if [ "$(notdir $<)" = "$<" ]; then echo Compiling profile: $<; g++ -c -Wall $(COMPILE_PROFILE) -o $@ $<; else echo Compiling profile: $<; (if [ -e $(dir $<)/Makefile ]; then make -C $(dir $<) $(notdir $@); else make -f $(FM)/standard.mak -C $(dir $<) $(notdir $@); fi) ; fi
compile-Cd = if [ "$(notdir $<)" = "$<" ]; then echo Compiling debug: $<; g++ -c -Wall $(COMPILE_DEBUG) -o $@ $<; else echo Compiling debug: $<; (if [ -e $(dir $<)/Makefile ]; then make -C $(dir $<) $(notdir $@); else make -f $(FM)/standard.mak -C $(dir $<) $(notdir $@); fi) ; fi
compile-Cr = if [ "$(notdir $<)" = "$<" ]; then echo Compiling release: $<; g++ -c -Wall $(COMPILE_RELEASE) -o $@ $<; else echo Compiling release: $<; (if [ -e $(dir $<)/Makefile ]; then make -C $(dir $<) $(notdir $@); else make -f $(FM)/standard.mak -C $(dir $<) $(notdir $@); fi) ; fi
compile-Cx = if [ "$(notdir $<)" = "$<" ]; then echo Compiling extra: $<; icc -c  $(COMPILE_EXTRA) -o $@ $<; else echo Compiling extra: $<; (if [ -e $(dir $<)/Makefile ]; then make -C $(dir $<) $(notdir $@); else make -f $(FM)/standard.mak -C $(dir $<) $(notdir $@); fi) ; fi

%.o: %.C
	@$(compile-C)
%.op: %.C
	@$(compile-Cp)
%.od: %.C
	@$(compile-Cd)
%.or: %.C
	@$(compile-Cr)
%.ox: %.C
	@$(compile-Cx)


%.C : %.def $(FM)/Bin/BuildOptions
	@echo Building : $(notdir $@)
	@$(FM)/Bin/BuildOptions $<

%.C : %.env $(FM)/Bin/BuildEnv
	@echo Building : $(notdir $@)
	@$(FM)/Bin/BuildEnv  $<

%.C : %.l
	@echo Flexing  : $(notdir $<)
	flex -o$@ -P$(basename $(notdir $<))_ $<


## Build/Clean:
##
LFLAGS = -m32 $(FM_LOPTS)  -L $(FM)/Lib $(addprefix -l, $(LIBS)) $(addprefix -l, $(CLIBS))
LIBFILES = $(addprefix $(FM)/Lib/lib, $(addsuffix .a, $(LIBS)))

$(EXEC) : $(OBJS) $(GOBJS) $(LIBFILES)
	@echo Linking...
	@g++ -ggdb -Wall $(OBJS) $(GOBJS) -o $(EXEC) $(LFLAGS)

$(EXEC)_purify : $(GOBJS) $(OBJS) $(LIBFILES)
	@echo Linking purify version...
	@purify g++ -ggdb -Wall $(GOBJS) $(OBJS) -o $(EXEC)_purify $(LFLAGS)

$(EXEC)_profile : $(addsuffix .op, $(basename $(GOBJS) $(OBJS))) $(LIBFILES)
	@echo Linking profile version...
	@g++ -ggdb -pg -Wall $(addsuffix .op, $(basename $(GOBJS) $(OBJS))) -o $(EXEC)_profile $(LFLAGS)

$(EXEC)_debug : $(addsuffix .od, $(basename $(GOBJS) $(OBJS))) $(LIBFILES)
	@echo Linking debug version...
	@g++ -ggdb -Wall $(addsuffix .od, $(basename $(GOBJS) $(OBJS))) -o $(EXEC)_debug $(LFLAGS)

$(EXEC)_release : $(addsuffix .or, $(basename $(GOBJS) $(OBJS))) $(LIBFILES)
	@echo Linking release version...
	g++ --static -O3 -Wall $(addsuffix .or, $(basename $(GOBJS) $(OBJS))) -o $(EXEC)_release $(LFLAGS)

$(EXEC)_extra : $(addsuffix .ox, $(basename $(GOBJS) $(OBJS))) $(LIBFILES)
	@echo Linking extra version...
	icc -cxxlib-icc --static -ggdb $(addsuffix .ox, $(basename $(GOBJS) $(OBJS))) -o $(EXEC)_extra $(LFLAGS)

.PHONY : purify
pure: $(EXEC)_purify
.PHONY : p
p: $(EXEC)_profile
.PHONY : d
d: $(EXEC)_debug
.PHONY : r
r: $(EXEC)_release
.PHONY : x
x: $(EXEC)_extra

.PHONY : clean
clean:
	@rm -f $(CLEAN) depend.mak \
	       $(EXEC) $(EXEC)_purify $(EXEC)_profile $(EXEC)_debug $(EXEC)_release \
	       $(OBJS) \
	       $(addsuffix .op, $(basename $(OBJS))) \
	       $(addsuffix .od, $(basename $(OBJS))) \
	       $(addsuffix .or, $(basename $(OBJS))) \
	       $(addsuffix .ox, $(basename $(OBJS))) 

.PHONY : realclean
realclean:
	@rm -f $(CLEAN) depend.mak \
	       $(EXEC) $(EXEC)_purify $(EXEC)_profile $(EXEC)_debug $(EXEC)_release \
	       $(GOBJS) $(OBJS) \
	       $(addsuffix .op, $(basename $(GOBJS) $(OBJS))) \
	       $(addsuffix .od, $(basename $(GOBJS) $(OBJS))) \
	       $(addsuffix .or, $(basename $(GOBJS) $(OBJS))) \
	       $(addsuffix .ox, $(basename $(GOBJS) $(OBJS))) 


## Dependencies:
##
define make-depend
	@echo "Generating dependencies"
	@g++ -MM $(FM_COPTS) $(INCLUDES) $(addsuffix .C, $(basename $(OBJS) $(GOBJS))) > dummy.mak
	@cp dummy.mak depend.mak
	@sed "s/o:/op:/" dummy.mak >> depend.mak
	@sed "s/o:/od:/" dummy.mak >> depend.mak
	@sed "s/o:/or:/" dummy.mak >> depend.mak
	@sed "s/o:/ox:/" dummy.mak >> depend.mak
	@rm -f dummy.mak 
endef

.PHONY : depend
depend : $(DEP_FILES)
	$(make-depend)

depend.mak : $(DEP_FILES)
	$(make-depend)

include depend.mak
