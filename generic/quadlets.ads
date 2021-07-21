------------------------------------------------------------------------------
--  Copyright (c) 2021, Lev Kujawski.
--
--  Permission is hereby granted, free of charge, to any person obtaining a
--  copy of this software and associated documentation files (the "Software")
--  to deal in the Software without restriction, including without limitation
--  the rights to use, copy, modify, merge, publish, distribute, sublicense,
--  and sell copies of the Software, and to permit persons to whom the
--  Software is furnished to do so.
--
--  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
--  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
--  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
--  THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
--  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
--  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
--  DEALINGS IN THE SOFTWARE.
--
--  SPDX-License-Identifier: MIT-0
--
--  File:          quadlets.ads (Ada Package Specification)
--  Language:      SPARK83 [1] subset of Ada (1987) [2]
--  Author:        Lev Kujawski
--  Description:   Specification of the Quadlets type and related subprograms
--
--  References:
--  [1] SPARK Team, SPARK83 - The SPADE Ada83 Kernel, Altran Praxis, 17 Oct.
--      2011.
--  [2] Programming languages - Ada, ISO/IEC 8652:1987, 15 Jun. 1987.
------------------------------------------------------------------------------

with Octets;

--# inherit Octets,
--#         Unchecked_Conversion;
package Quadlets is
   pragma Pure;

   Bits : constant := 32;

   type T is range 0 .. 4294967295;
   --# assert T'Base is Long_Integer;
   for T'Size use Bits;

   function Negation (Value : in T) return T;
   --# return T'Last - Value;

   --  Logical AND operation on the bits of Left and Right.
   function Conjunction (Left  : in T;
                         Right : in T) return T;
   --# return Conjunction (Left, Right);

   --  Logical OR operation on the bits of Left and Right.
   function Inclusive_Disjunction (Left  : in T;
                                   Right : in T) return T;
   --# return Inclusive_Disjunction (Left, Right);

   --  Logical XOR operation on the bits of Left and Right.
   function Exclusive_Disjunction (Left  : in T;
                                   Right : in T) return T;
   --# return Exclusive_Disjunction (Left, Right);

   subtype Bit_Count_T is Natural range 0 .. Bits - 1;

   function Left_Shift (Value  : in T;
                        Amount : in Bit_Count_T) return T;
   --# return (Value * (2 ** Amount)) mod (2 ** Bits);

   function Right_Shift (Value  : in T;
                         Amount : in Bit_Count_T) return T;
   --# return Value / (2 ** Amount);

   function Right_Rotation (Value  : in T;
                            Amount : in Bit_Count_T) return T;

   subtype Octet_Index_T is Natural range 0 .. 3;

   function Octet (Value : in T;
                   Index : in Octet_Index_T) return Octets.T;

   function Modular_Sum (Augend : in T;
                         Addend : in T) return T;
   --# return (Augend + Addend) mod (2 ** Bits);

   procedure Chained_Modular_Sum (Addend       : in     T;
                                  Augend_Lower : in out T;
                                  Augend_Upper : in out T;
                                  Overflow     : in out Boolean);
   --# derives Augend_Lower,
   --#         Augend_Upper from *,
   --#                           Addend,
   --#                           Augend_Lower &
   --#         Overflow     from *,
   --#                           Addend,
   --#                           Augend_Lower,
   --#                           Augend_Upper;

   function Modular_Difference (Minuend    : in T;
                                Subtrahend : in T) return T;
   --# return (Minuend - Subtrahend) mod (2 ** Bits);

   function Modular_Product (Multiplicand : in T;
                             Multiplier   : in T) return T;
   --# return (Multiplicand * Multiplier) mod (2 ** Bits);

end Quadlets;
