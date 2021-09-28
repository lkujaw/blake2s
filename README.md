[![Alire](https://img.shields.io/endpoint?url=https://alire.ada.dev/badges/blake2s.json)](https://alire.ada.dev/crates/blake2s.html)

# BLAKE2s for Ada

This is a SPARK83 implementation of the [BLAKE2s][1] hash function.
As SPARK83 is a strict subset of Ada 1987 (ISO-8652:1987), this
package should be usable with any compiler compliant with the
1987 (or later) edition of the ISO Ada standard.

## BLAKE2s Advantages

Like SHA-256, BLAKE2s operates on 32-bit words, but is not susceptible
to the length extension attacks of the former.  Although the FIPS hash
functions SHA-512/256 and SHA-3 mitigate the length extension
vulnerability of SHA-256, they require 64-bit words for decent
performance.  Thus, BLAKE2s fills a niche for resource-constrained
platforms. It also enjoys a high security margin, as each of the ten
BLAKE2s rounds is the equivalent of two ChaCha rounds.

## Build Instructions for GNAT

To compile the BLAKE2s library and executables, you will need to have
installed and accessible within your path copies of [AST NMAKE][2]
with Ada support and the GCC compiler built with the GNAT Ada
front-end enabled.

Once the prerequisites are available, simply run `cd gnat && nmake` .

## SPARK and Isabelle Verification

This project uses a combination of the original, annotation-based
SPARK tool set (search [AdaCore Libre][3] for the 2012 GPL release)
and the HOL-SPARK library bundled within [Isabelle][4] 2021 to prove
the absence of runtime errors.

To verify the proofs, check the file named `makefile.nmk` within the
project root first to ensure that you have the necessary programs
(including the `isabelle` command) installed within your path.

If everything is functioning as it should, all verification conditions
should be discharged.

## Ada 1987 Compatibility Note

This package utilizes the Ada 1995 pragma "Pure" in the following
package specifications:

* BLAKE2S (common/blake2s.ads)
* Octets (common/octets.ads)
* Octet_Arrays (common/octearra.ads)

Per section 2.8 of the Ada 1987 Language Reference Manual, "[a] pragma
that is not language-defined has no effect if its identifier is not
recognized by the (current) implementation."  However, as the pragma
is merely advisory to the compiler, it may be removed without adverse
effect from these files should it cause any issues.

## SPARK83 Rationale

For the 1987, 1995, and 2007 editions of the ISO Ada standard, the
corresponding SPARK language tools were based upon annotations.  The
placement of annotations within Ada comments has the advantage of not
requiring any special support for SPARK on the part of the compiler.

At the time of writing, the compiler support required by the post-2007
editions of the SPARK language is found only within the GNAT compiler.
Like the BLAKE2s reference source code, which targets the first
edition of the ISO C standard released in 1990, this project targets
the earliest release of the ISO Ada standard to maximize portability,
and for this same reason the annotation-based SPARK language tools are
ideal.

## License and Warranty

Licensing terms and important warranty information for the BLAKE2s
library may be found within the file named [license.txt][3].

`SPDX-License-Identifier: MIT-0`

Separate from the BLAKE2s library, the B2SSUM and B2STEST executables
are distributed under the terms of the GNU General Public License,
version 3.0; see the file [bin/copying.txt][4] for licensing terms
and important warranty information.

## Acknowledgments

Thanks to Aumasson et al. for releasing the excellent BLAKE hash
functions into the public domain, and the [GNAT, SPARK][5],
[Isabelle][6], and [AdaControl][7] developers for publishing their
tremendously helpful [free software][8].

[1]: https://www.blake2.net/
[2]: https://sr.ht/~lev/ast/
[3]: license.txt
[4]: bin/copying.txt
[5]: https://libre.adacore.com/
[6]: https://isabelle.in.tum.de/
[7]: https://www.adalog.fr/en/adacontrol.html
[8]: https://www.gnu.org/philosophy/free-sw.html
