#!/bin/bash

BUILD_DATE=$(date +"%F %H:%M %Z")
VERSION="4.2_$(date +"%F")"

CP_SEP=":"

if [[ ! -z $(uname -o | grep -i "Cygwin") ]]
then
    CP_SEP=";"
fi

PATH=$JDK6/bin:$PATH

if [[ -z $KODKOD_HOME ]]
then
    KODKOD_HOME=../kodkod  #../relations-experimental
fi

function fade_start { echo -ne "$(tput setaf 8)"; }
function fade_end   { echo -ne "$(tput sgr0)"; }

function step  { echo -e "$(tput setaf 12; tput bold)[$@...]$(tput sgr0)"; }
function info  { echo -e "$(tput setaf 4)$@$(tput sgr0)"; }
function emph  { echo -e "$(tput setaf 10; tput bold)$@$(tput sgr0)"; }
function warn  { echo -e "$(tput setaf 3)  [Warn] $@$(tput sgr0)"; }
function error { echo -e "$(tput setaf 9; tput bold)  [ERROR]: $@$(tput sgr0)"; }
function trace { echo -e "$(tput setaf 7)$@$(tput sgr0)"; }
function fatal { error $@; fade_end; exit 1; }

function compile {
    version_file=src/edu/mit/csail/sdg/alloy4/Version.java
    cp -r $version_file $version_file.bak
    sed -i \
      -e 's/public static String buildDate.*/public static String buildDate() { return "'"$BUILD_DATE"'"; }/' \
      -e 's/public static String version.*/public static String version() { return "'"$VERSION"'"; }/' $version_file

    mkdir -p bin

    info "cleaning up the bin folder"
    rm -rf bin/*

    step "compiling"
    CP=$(ls -1 lib/*.jar | xargs | sed 's/\ /'$CP_SEP'/g')

    if [[ -d $KODKOD_HOME ]]; then
        CP=$KODKOD_HOME/bin:$CP
    else
        warn "Kodkod project not found in $KODKOD_HOME; relying on kodkod.jar, which may be obsolete"
    fi

    trace "  using CLASSPATH: $CP"
    find src -name "*.java" | xargs javac -cp $CP -d bin # -source 1.5 -target 1.5
    ok="$?"

    mv $version_file.bak $version_file

    if [[ $ok != "0" ]]; then fatal "Could not compile from sources"; fi

    fade_end
}

function dist {
    DST=dist
    MACOSDST=Alloy-OSX

    rm -rf $DST/*
    mkdir -p $DST/alloy

    step "building JAR distribution"

    for f in lib/*jar
    do
        trace "  extracting: $f"
	unzip -q -o $f -d $DST/alloy
    done

    # copy the content of the extra folder
    cp -r extra/* $DST/alloy

    rm -rf bin/tmp
    cp -r bin/* $DST/alloy/
    cp -r src/* $DST/alloy/
    if [[ -d $KODKOD_HOME ]]; then
        rm -rf $DST/alloy/kodkod
        trace "  copying kodkod binaries: $KODKOD_HOME/bin/kodkod"
        cp -r $KODKOD_HOME/bin/kodkod $DST/alloy/kodkod
        trace "  copying kodkod sources: $KODKOD_HOME/src/kodkod"
        cp -r $KODKOD_HOME/src/kodkod/* $DST/alloy/kodkod/
    fi
    rm -rf $DST/alloy/META-INF

    find $DST/alloy -type d -name ".git" -exec rm -rf {} \;
    find $DST/alloy -type d -name ".svn" -exec rm -rf {} \;
    find $DST/alloy -type d -name "CVS" -exec rm -rf {} \;

    mkdir -p $DST/alloy/META-INF
    cp MANIFEST.MF $DST/alloy/META-INF

    # DEPRECATED
    # for d in META-INF # amd64-linux  help  icons  images  LICENSES  META-INF  models  README.TXT  x86-freebsd  x86-linux  x86-mac  x86-windows
    # do
    # 	cp -r template/$d alloy/
    # done

    pushd $(pwd) &> /dev/null
    cd $DST/alloy
    # find -type f -name "*.java" -exec rm -f {} \;
    jarName="alloy$VERSION.jar"
    zip -q -r $jarName *
    chmod +x $jarName
    mv $jarName ../
    cd ..
    rm -rf allo
    popd &> /dev/null

    emph " *** jar file created:    $DST/$jarName"

    step "building OSX app"

    export jarName VERSION
    ant

    ###############################
    # for Mac dist
    ###############################

    step "packaging OSX"
    osxdir="alloy-osx"
    rm -rf $DST/$osxdir
    mkdir -p $DST/$osxdir/dist
    cp -r $DST/*.app $DST/$osxdir/dist
    cp -r OSX-extra/* $DST/$osxdir/dist
    find $DST/$osxdir/dist -type d -name ".svn" -exec rm -rf {} \;
    cat build-dmg.sh | sed 's/VERSION=X/VERSION='$VERSION'/g' > $DST/$osxdir/build-dmg.sh

    # build dmg on hudsonbay
    step "building DMG"
    cd $DST
    zip -q -r $osxdir.zip $osxdir
    rm -rf $osxdir
    info "  copying files to hudsonbay..."
    scp -r $osxdir.zip hudsonbay:
    exe_str="rm -rf $osxdir; unzip -q $osxdir; cd $osxdir; chmod +x *.sh; ./*.sh"
    info "  building DMG on hudsonbay..."
    ssh hudsonbay "$exe_str"
    info "  copying files back from hudsonbay..."
    scp hudsonbay:$osxdir/*dmg .
    emph " *** dmg file created:   $DST/$(ls *dmg)"
    info "  cleaning up on hudsonbay..."
    ssh hudsonbay 'rm alloy-osx.zip'

    fade_end
}

if [[ "X"$1 == "X" ]]
then
  compile
  dist
else
  $1
fi

# echo '#!/bin/bash

# CP=classes:$(ls -1 lib/*.jar | xargs | sed "s/\ /:/g")
# java -Xms512m -Xmx2048m -ea -cp $CP edu.mit.csail.sdg.alloy4whole.SimpleGUI
# ' > $DST/alloy/run-alloy.sh

# chmod +x $DST/alloy/run-alloy.sh

