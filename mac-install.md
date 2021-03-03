## macOS Installation Instructions

### Install Java 11
1. `brew install openjdk@11`

If the above step does not work and you are running an old version of macOS, try:
1. `brew update`
2. `brew tap homebrew/cask-versions`
3. `brew cask install java11`

Make sure Java 11 is the default by adding the following lines to your dotfiles. For `bash` this is usually `.bash_profile` and for `zsh` this is usually `.zshrc`.
```
export JAVA_11_HOME=$(/usr/libexec/java_home -v11)
alias java11='export JAVA_HOME=$JAVA_11_HOME'
java11
```

### Install Z3
1. `git clone https://github.com/Z3Prover/z3.git; cd z3`
2. `python scripts/mk_make.py --java`
2. `mkdir build; cd build`
4. `make -j4`

Make sure the Z3 Java libraries are in the right place by copying the files in the `build` directory to their proper place. See the main `README.md` for more details on why this is necessary.
1. `sudo cp <buildfolderInZ3>/libz3.dylib /usr/local/bin`
2. `sudo cp <buildfolderInZ3>/libz3java.dylib /Library/Java/Extensions`

### Install sbt
1. `brew install sbt`

### Install UCLID
1. `git clone https://github.com/uclid-org/uclid.git; cd uclid`
2. `sbt update clean compile`
3. `sbt universal:packageBin`
4. `unzip <target/universal>/uclid-0.9.5.zip; cd uclid-0.9.5; export PATH=$PATH:$PWD/bin`

