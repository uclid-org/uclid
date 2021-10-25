## Procedure to install and run UCLID5:

---

1. Install git (might not have to do this if we provide the precloned snapshot of the UCLID repository)

	- `sudo apt-get-install git`

---

2. Install solver binaries (won't be necessary if we send them the packaged version):
	- Download and install z3: `source get-z3-linux.sh `
    - Download and install cvc4: `source get-cvc4-linux.sh `
	- Download and install delphi: `source get-delphi-linux.sh`

- Add the binaries and cvc4 run script to $PATH:
    - `export PATH=$PATH:~/uclid/z3/bin/:~/uclid/cvc4/bin:~/uclid/delphi/bin/:~/uclid/`
    - `export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:~/uclid/z3/bin/`


---

3. Install `sbt`

	- `sbt` is made available as a debian package in `~/Documents/packages/sbt_1.5.5_all.deb`. Please install it using:
    	- `sudo dpkg -i sbt_1.5.5_all.deb`
		
---

4. Run sbt and build `UCLID5`
	- Load the `sbt` prompt: this will install/update some Scala packages
    	- `sbt // this will update/install several libraries`

	- Once inside the `sbt` prompt, run clean, compile, test. This will run all tests.
  		- `sbt:uclid> clean; compile`
  		- `sbt:uclid> "set fork:=true"; test`