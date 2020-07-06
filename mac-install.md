```
Install Java 11
1. `brew update`
2. `brew tap homebrew/cask-versions`
3. `brew cask install java11`

Make sure Java 11 is the defualt. For example, if you’re using bash, put this in your .bash_profile
`export JAVA_11_HOME=$(/usr/libexec/java_home -v11)
alias java11='export JAVA_HOME=$JAVA_11_HOME'
java11`

INSTALL Z3
1. clone z3 and go into the directory
2. `python scripts/mk_make.py --java`
2. `mkdir build; cd build`
4. `make -j4`

Make sure the z3 java libraries are in the right place
1. `sudo cp <buildfolderInZ3>*z3*.dylib /Library/Java/Extensions/.`

Install sbt
1. `brew install sbt`

install UCLID
1. clone uclid, cd into the directory
2. `sbt update clean compile`
3. `sbt universal:packageBin`
4. `unzip <target/universal>/uclid-0.9.5.zip; cd uclid-0.9.5; export PATH=$PATH:$PWD/bin`
```
