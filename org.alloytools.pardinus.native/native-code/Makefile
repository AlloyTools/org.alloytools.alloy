#
# On a mac (amd64/arm64) just type make in this directory
# All native code will end up in ../native/OS/ARCH. OS=[darwin,linux,windows], ARCH=[amd64,arm64]
#


DIRS = native/linux/amd64 native/windows/amd64 native/darwin/amd64 native/darwin/arm64
REPOS= minisat glucose lingeling minisatprover
CLASSPATH = ../target/classes:../../org.alloytools.pardinus.core/target/classes

REPOS_PATHS = $(addsuffix /repo/.git/config,$(REPOS))

.PHONY: all native darwin linux windows go

install: clean darwin linux windows
	-rm -rf ../native
	cp -rf dependencies/* native/
	cp -rf native ..

clean:
	rm -rf build native headers $(addsuffix /repo,$(REPOS))

native : 
	mkdir -p $(DIRS)

headers:
	mkdir headers
	javac -classpath $(CLASSPATH) -h . -d ../target ../src/main/java/org/alloytools/solvers/natv/glucose/Glucose.java
	mv org_alloytools_solvers_natv_glucose_Glucose.h headers/AlloyGlucose.h
	javac -classpath $(CLASSPATH) -h . -d ../target ../src/main/java/org/alloytools/solvers/natv/minisat/MiniSat.java
	mv org_alloytools_solvers_natv_minisat_MiniSat.h headers/AlloyMiniSat.h
	javac -classpath $(CLASSPATH) -h . -d ../target ../src/main/java/org/alloytools/solvers/natv/minisatprover/MiniSatProver.java
	mv org_alloytools_solvers_natv_minisatprover_MiniSatProver.h headers/AlloyMiniSatProver.h

$(DIRS):
	mkdir -p $@

minisat/repo/.git/config:
	git clone --depth 1 --branch alloy https://github.com/AlloyTools/minisat minisat/repo
glucose/repo/.git/config:
	git clone --depth 1 --branch alloy https://github.com/AlloyTools/glucose glucose/repo
minisatprover/repo/.git/config:
	git clone --depth 1 --branch alloy https://github.com/AlloyTools/minisatprover minisatprover/repo
lingeling/repo/.git/config:
	git clone --depth 1 --branch alloy https://github.com/AlloyTools/lingeling lingeling/repo
	cd lingeling/repo && ./configure.sh && make lglcfg.h lglcflags.h && cd ../..


native/darwin/amd64/libminisat.dylib: $(REPOS_PATHS) native headers
		rm -rf build
		cmake -DJNI_INCLUDE=../jni/darwin/amd64 -DOSX_ARCH=x86_64 -Bbuild minisat
		make -C build
		cp build/libminisat.dylib $@

native/darwin/arm64/libminisat.dylib: $(REPOS_PATHS) native headers
		rm -rf build
		cmake -DJNI_INCLUDE=../jni/darwin/arm64 -DOSX_ARCH=arm64 -Bbuild minisat
		make -C build
		cp build/libminisat.dylib $@

native/darwin/amd64/libminisatprover.dylib: $(REPOS_PATHS) native headers
		rm -rf build
		cmake -DJNI_INCLUDE=../jni/darwin/amd64 -DOSX_ARCH=x86_64 -Bbuild minisatprover
		make -C build
		cp build/libminisatprover.dylib $@

native/darwin/arm64/libminisatprover.dylib: $(REPOS_PATHS) native headers
		rm -rf build
		cmake -DJNI_INCLUDE=../jni/darwin/arm64 -DOSX_ARCH=arm64 -Bbuild minisatprover
		make -C build
		cp build/libminisatprover.dylib $@

native/darwin/amd64/libglucose.dylib: $(REPOS_PATHS) native headers
		rm -rf build
		cmake -DJNI_INCLUDE=../jni/darwin/amd64 -DOSX_ARCH=x86_64 -Bbuild glucose
		make -C build
		cp build/libglucose.dylib $@

native/darwin/arm64/libglucose.dylib: $(REPOS_PATHS) native headers
		rm -rf build
		cmake -DJNI_INCLUDE=../jni/darwin/arm64 -DOSX_ARCH=arm64 -Bbuild glucose
		make -C build
		cp build/libglucose.dylib $@

native/darwin/amd64/plingeling : $(REPOS_PATHS) native headers
		rm -rf build
		cmake -DJNI_INCLUDE=../jni/darwin/amd64 -DOSX_ARCH=x86_64 -Bbuild lingeling
		make -C build
		cp build/plingeling native/darwin/amd64/plingeling

native/darwin/arm64/plingeling: $(REPOS_PATHS) native headers
		rm -rf build
		cmake -DJNI_INCLUDE=../jni/darwin/arm64 -DOSX_ARCH=arm64 -Bbuild lingeling
		make -C build
		cp build/plingeling native/darwin/arm64/plingeling


darwin: \
	native/darwin/amd64/libminisat.dylib \
	native/darwin/arm64/libminisat.dylib \
	native/darwin/amd64/libminisatprover.dylib \
	native/darwin/arm64/libminisatprover.dylib \
	native/darwin/amd64/libglucose.dylib \
	native/darwin/arm64/libglucose.dylib \
	native/darwin/arm64/plingeling \
	native/darwin/amd64/plingeling 

linux: $(DIRS) $(REPOS) native headers
	./dockcross_linux bash -c "make build_linux_inner"

build_linux_inner:
	rm -rf build
	cmake -DJNI_INCLUDE=../jni/linux/amd64 -Bbuild minisat
	make -C build
	cp build/libminisat.so native/linux/amd64/libminisat.so
	rm -rf build
	cmake -DJNI_INCLUDE=../jni/linux/amd64 -Bbuild minisatprover
	make -C build
	cp build/libminisatprover.so native/linux/amd64/libminisatprover.so
	rm -rf build
	cmake -DJNI_INCLUDE=../jni/linux/amd64 -Bbuild glucose
	make -C build
	cp build/libglucose.so native/linux/amd64/libglucose.so
	rm -rf build
	cmake -DJNI_INCLUDE=../jni/linux/amd64 -Bbuild lingeling
	make -C build
	cp build/plingeling native/linux/amd64/plingeling


windows: $(DIRS) $(REPOS) headers
	./dockcross_windows bash -c "make build_windows_inner"

build_windows_inner:
	sudo make -C /usr/src/mxe zlib
	rm -rf build ; \
	cmake -DJNI_INCLUDE=../jni/windows/amd64 -Bbuild minisat 
	make -C build
	cp build/libminisat.dll native/windows/amd64/minisat.dll
	rm -rf build
	cmake -DJNI_INCLUDE=../jni/windows/amd64 -Bbuild glucose
	make -C build
	cp build/libglucose.dll native/windows/amd64/glucose.dll


