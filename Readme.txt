## Artifact for TACAS 2022 Submission #177 (Artifact) and #178 (Paper)

#### UCLID5: Multi-Modal Formal Modeling, Verification, and Synthesis

---

This is the artifact corresponding to submission #178. Please follow the instructions below to install and run the artifact.

The `.zip` package contains two directories, `uclid` and `packages`. The `packages` directory contains the Debian package for `sbt` (Scala build tool), which is used for building `UCLID5`. The `uclid` directory contains the source code of the tool as well as solver binaries for `z3`, `cvc4` and `delphi` in directories of the same name. Note that steps 1 and 2 are optional and they will require an internet connection.

Copy the `packages` and `uclid` directories into the home directory (`~/`).

---

1. (Optional) Only if you want to compile uclid from source: Install `sbt`.
	- `sbt` is made available as a debian package in `packages/sbt_1.5.5_all.deb`. Please install it using: `sudo dpkg -i sbt_1.5.5_all.deb`
	- Note that compiling uclid from source would require an internet connection.
		
---

2. (Optional) Startup sbt and build `UCLID5` from source:
	- From the `uclid` directory, load the `sbt` prompt: `sbt` will install/update Scala packages and this **will require an internet connection**
    	- `sbt // this will update/install several Scala packages`
	- Follow the instructions (replicated from the `uclid5` GitHub [README](https://github.com/uclid-org/uclid#compiling-uclid5)):
	- Once inside the `sbt` prompt, run clean, compile, test. This will run all tests.
  		- `sbt:uclid> clean; compile`
  		- `sbt:uclid> "set fork:=true"; test`
    - Finally, you can build the `UCLID5` binary by invoking `universal:packageBin` from the `sbt` prompt or run `UCLID5` on examples directly from within the `sbt` prompt.

---

3. Running `UCLID5` on the examples:
   - We have provided a self-contained directory - `tool_paper_examples` - with all prebult binaries and examples. This does not require you to perform steps 1 and 2 above.
   - Please enter this directory and refer to Section 2 of `artifact.pdf` for more details


---

### Availability statement:

The `UCLID5` tool is publicly available at https://github.com/uclid-org/uclid/tree/master. This repository includes the source code as well as a comprehensive set of tests.

---

### Badges:

We apply for all three badges: Functional, Reusable, Available.
