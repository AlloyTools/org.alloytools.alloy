## Steps to generate a new release

### Install Inno setup
http://www.jrsoftware.org/isinfo.php

Update the installation files:
```
\build\windows\installation-files\org.alloytools.alloy.dist.jar
\build\windows\installation-files\redist\jre-8u231-windows-x64.exe
\build\windows\installation-files\redist\jre-8u231-windows-i586.exe
```

open the inno script from the Alloy repository \build\windows\setup-file.iss
Update the version of alloy (and jra version if needed)
```
#define MyAppVersion "5.1.0"
...
#define JavaVersion "1.8"
```

Build the new setup using inno

## Steps to generate the installer from scratch

### Download a compatible java version for windows

https://www.java.com/en/download/manual.jsp

### Download the logo from alloy from:
https://avatars3.githubusercontent.com/u/30268214?v=4&s=200

### Create an .ico file from the alloy logo
https://www.icoconverter.com/

### Download BatToExeConverter
https://www.battoexeconverter.com/

Open BatToExeConverter and add the following script:
```
@echo off
java -jar org.alloytools.alloy.dist.jar
```

Compile the bat file to start-alloy-tools.exe
* Enable hide console windows
* Select the generated .ico file

### Download the latest release of Alloy as a jar file:
https://github.com/AlloyTools/org.alloytools.alloy/releases

### Download the windows binary .dll files from:
https://github.com/beckus/AlloyAnalyzer/tree/master/x86-windows

place them into the same folder as the jar file

### Download the license file
https://github.com/AlloyTools/org.alloytools.alloy/blob/master/LICENSE

### Install Inno setup
http://www.jrsoftware.org/isinfo.php

follow the steps in: Steps to generate a new release


