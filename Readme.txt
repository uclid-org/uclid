## Artifact for TACAS 2022 Submission 178

#### UCLID5: Multi-Modal Formal Modeling, Verification, and Synthesis

---

This is the artifact corresponding to submission #178. Please follow the instructions below to install and run the artifact.

The `.zip` package contains two directories, `uclid` and `packages`. The `packages` directory contains the Debian package for `sbt` (Scala build tool), which is used for building `uclid`. The `uclid` directory contains the source code of the tool as well as solver binaries for `z3`, `cvc4` and `delphi` in directories of the same name.

Copy the `packages` and `uclid` directories into the home directory (`~/`).

---

1. Add the solver binaries and cvc4 run script to `$PATH`. Note that this would have to repeated for each shell that is launched (to avoid this, add these commands to the `~/.bashrc` file).
    - `export PATH=$PATH:~/uclid/z3/bin/:~/uclid/cvc4/bin:~/uclid/delphi/bin/:~/uclid/`
    - `export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:~/uclid/z3/bin/`

---

2. Install `sbt`

	- `sbt` is made available as a debian package in `packages/sbt_1.5.5_all.deb`. Please install it using: `sudo dpkg -i sbt_1.5.5_all.deb`
		
---

3. Run sbt and build `UCLID5`
	- Load the `sbt` prompt: this will install/update Scala packages
    	- `sbt // this will update/install several Scala packages`

	- Once inside the `sbt` prompt, run clean, compile, test. This will run all tests.
  		- `sbt:uclid> clean; compile`
  		- `sbt:uclid> "set fork:=true"; test`