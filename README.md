[![Alire](https://img.shields.io/endpoint?url=https://alire.ada.dev/badges/blake2s.json)](https://alire.ada.dev/crates/blake2s.html)

# BLAKE2s for Ada

This is a SPARK83 implementation of the [BLAKE2s][1] hash function.
As SPARK83 is a strict subset of Ada 1987 (ISO-8652:1987), this
package should be usable with any standard-compliant Ada compiler.

## BLAKE2s advantages

Like SHA-256, BLAKE2s operates on 32-bit words, but is not susceptible
to the length extension attacks of the former.  Although the FIPS hash
functions SHA-512/256 and SHA-3 mitigate the length extension
vulnerability of SHA-256, they require 64-bit words for decent
performance.  Thus, BLAKE2s fills a niche for resource-constrained
platforms. It also enjoys a high security margin, as each of the ten
BLAKE2s rounds is the equivalent of two ChaCha rounds.

## Build instructions for GNAT

To compile the BLAKE2s library and executables, you will need to have
installed and accessible within your path copies of [AST NMAKE][2]
with Ada support and the GCC compiler built with the GNAT Ada
front-end enabled.

Once the prerequisites are available, simply run `cd gnat && nmake` .

## SPARK and Isabelle verification

This project uses a combination of the original, annotation-based
SPARK tool set (search [AdaCore Libre][3] for the 2012 GPL release)
and the HOL-SPARK library bundled within [Isabelle][4] 2021 to prove
the absence of runtime errors.

To verify the proofs, check the file named `makefile.nmk` within the
project root first to ensure that you have the necessary programs
(including the `isabelle` command) installed within your path.

If everything is functioning as it should, there should be no
undischarged verification conditions.

## Ada 1987 compatibility note

This package utilizes the Ada 1995 pragma "Pure" in the following
package specifications:

* BLAKE2S (common/blake2s.ads)
* Octets (common/octets.ads)
* Octet_Arrays (common/octearra.ads)

Per section 2.8 of the Ada 1987 Language Reference Manual, "[a] pragma
that is not language-defined has no effect if its identifier is not
recognized by the (current) implementation." However, as the pragma is
merely advisory to the compiler, it may be removed without adverse
effect from these files should it cause any issues.

## Acknowledgments

Thanks to Aumasson et al. for releasing the excellent BLAKE hash
functions into the public domain, and the [GNAT, SPARK][3],
[Isabelle][4], and [AdaControl][5] developers for publishing their
tremendously helpful [free software][6].

[1]: https://www.blake2.net/
[2]: https://sr.ht/~lev/ast/
[3]: https://libre.adacore.com/
[4]: https://isabelle.in.tum.de/
[5]: https://www.adalog.fr/en/adacontrol.html
[6]: https://www.gnu.org/philosophy/free-sw.html