# Alloy2smt

Alloy2smt is a translator that translates models written in alloy language into cvc4 smt-lib language. 

### Requirements

Java Platform (JDK) 8

### Building alloy2smt

1. Clone the project `git clone https://github.com/mudathirmahgoub/alloy2smt`
2. Run gradle wrapper command with build. For Linux run the command `./gradlew build`.  For Windows run the command `gradlew.bat build`. To build without running the tests, use the task `alloy2smtWithDependencies` instead of `build`
3. Run the translator using the command
```jshelllanguage
java -jar build/libs/alloy2smt_with_dependencies.jar -i examples/test.als -o examples/test.smt2
```
The generated smt files can be checked using the SMT solver [CVC4](http://cvc4.cs.stanford.edu/downloads/). 