#!/bin/sh -x

rm -rf native
mkdir -p native/linux/x86-64
mkdir -p native/windows/x86-64
mkdir -p native/macos/x86-64
mkdir -p native/macos/arm64

rm -rf minisat/repo
git clone --depth 1  --branch alloy https://github.com/AlloyTools/minisat minisat/repo
rm -rf glucose/repo
git clone --depth 1  --branch alloy https://github.com/AlloyTools/glucose glucose/repo
rm -rf lingeling/repo
git clone --depth 1  --branch alloy https://github.com/AlloyTools/lingeling lingeling/repo
rm -rf gini/repo
git clone --depth 1  --branch alloy https://github.com/AlloyTools/gini gini/repo
rm -rf minisatp/repo
git clone --depth 1  --branch alloy https://github.com/AlloyTools/minisatp minisatp/repo

cd lingeling/repo
./configure.sh
make lglcfg.h lglcflags.h
cd ../..

rm -rf build archive
mkdir archive

cd gini/repo/cmd/gini
GOOS=windows GOARCH=amd64 go build
cp gini.exe ../../../../native/windows/x86-64/

GOOS=darwin GOARCH=arm64 go build
cp gini ../../../../native/macos/arm64/

GOOS=darwin GOARCH=amd64 go build
cp gini ../../../../native/macos/x86-64/

GOOS=linux GOARCH=amd64 go build
cp gini ../../../../native/linux/x86-64/
cd -

cmake -DJNI_INCLUDE=../jni/macos/arm64 -DOSX_ARCH=arm64 -Bbuild minisat
make -C build
cp build/libminisat.dylib native/macos/arm64
mv build archive/mac_arm_minisat;

rm -rf build
cmake -DJNI_INCLUDE=../jni/macos/x86-64 -DOSX_ARCH=x86_64 -Bbuild minisat
make -C build
cp build/libminisat.dylib native/macos/x86-64
mv build archive/mac_x86_minisat;

rm -rf build
cmake -DJNI_INCLUDE=../jni/macos/arm64 -DOSX_ARCH=arm64 -Bbuild glucose
make -C build
cp build/libglucose.dylib native/macos/arm64
mv build archive/mac_arm_glucose;

rm -rf build
cmake -DJNI_INCLUDE=../jni/macos/x86-64 -DOSX_ARCH=x86_64 -Bbuild glucose
make -C build
cp build/libglucose.dylib native/macos/x86-64
mv build archive/mac_x86_glucose

cmake -DJNI_INCLUDE=../jni/macos/arm64 -DOSX_ARCH="arm64" -Bbuild lingeling
make -C build
cp build/liblingeling.dylib native/macos/arm64
cp build/lingeling native/macos/arm64
cp build/plingeling native/macos/arm64
mv build archive/mac_arm_lingeling

rm -rf build
cmake -DJNI_INCLUDE=../jni/macos/x86-64 -DOSX_ARCH=x86_64 -Bbuild lingeling
make -C build
cp build/liblingeling.dylib native/macos/x86-64
cp build/lingeling native/macos/x86-64
cp build/plingeling native/macos/x86-64
mv build archive/mac_x86_lingeling

./dockcross_linux bash -c "
	rm -rf build;
	cmake -DJNI_INCLUDE=../jni/linux/x86-64 -Bbuild minisat;
	make -C build;
	cp build/libminisat.so native/linux/x86-64;
	mv build archive/lin_x86_minisat;

	cmake -DJNI_INCLUDE=../jni/linux/x86-64 -Bbuild glucose;
	make -C build;
	cp build/libglucose.so native/linux/x86-64;
	mv build archive/lin_x86_glucose

	cmake -DJNI_INCLUDE=../jni/linux/x86-64 -Bbuild lingeling;
	make -C build;
	cp build/liblingeling.so native/linux/x86-64;
	cp build/plingeling native/linux/x86-64;
	cp build/lingeling native/linux/x86-64;
	mv build archive/lin_x86_lingeling

	"


./dockcross_windows bash -c "sudo make -C /usr/src/mxe zlib; 
	rm -rf build;
	cmake -DJNI_INCLUDE=../jni/windows/x86-64 -Bbuild glucose;
	make -C build;
	cp build/libglucose.dll native/windows/x86-64/glucose.dll;
	mv build archive/win_x86_glucose;

	cmake -DJNI_INCLUDE=../jni/windows/x86-64 -Bbuild minisat;
	make -C build;
	cp build/libminisat.dll native/windows/x86-64/minisat.dll;
	mv build archive/win_x86_minisat
	"

