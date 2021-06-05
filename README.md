# ada-blake2 #

This is a SPARK83 implementation of the [BLAKE2s](https://www.blake2.net/) hash function. As SPARK83 is a strict subset of Ada 87 (ISO-8652:1987), this package should be usable with any standard-compliant Ada compiler.

## Build instructions for GNAT ##

To compile the ada-blake2 library and executables, you will need a copy of GCC within your path that includes the GNAT Ada front-end.

To use the included Makefile, run "cd gnat && make" .

## SPARK and Isabelle verification ##

This project uses a combination of the original, annotation-based SPARK tool set (search [AdaCore Libre](https://libre.adacore.com/) for the 2012 GPL release) and the HOL-SPARK library bundled within [Isabelle](https://isabelle.in.tum.de/) 2021 to prove the absence of runtime errors.

To verify the proofs, check the Makefile within the project root first to ensure that you have the necessary programs (including the 'isabelle' command) installed within your path.

## Ada 87 compatibility note ##

This package utilizes the Ada 95 pragma "Pure" in the following package specifications:

* BLAKE2S (common/blake2s.ads)
* Octets (common/octets.ads)
* Octet_Arrays (common/octearra.ads)

Per section 2.8 of the Ada 87 Language Reference Manual, "[a] pragma that is not language-defined has no effect if its identifier is not recognized by the (current) implementation." However, as the pragma is merely advisory to the compiler, it may be removed without adverse effect from these files should it cause any issues.

## Credits

Thanks to Aumasson et al. for releasing the excellent BLAKE hash functions into the public domain, and the [GNAT, SPARK](https://libre.adacore.com/), [Isabelle](https://isabelle.in.tum.de/), and [AdaControl](https://www.adalog.fr/en/adacontrol.html) developers for publishing their tremendously helpful [free software](https://www.gnu.org/philosophy/free-sw.html).