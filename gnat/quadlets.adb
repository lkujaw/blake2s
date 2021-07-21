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
--  File:          quadlets.adb (Ada Package Body)
--  Language:      SPARK83 [1] subset of Ada (1987) [2]
--  Author:        Lev Kujawski
--  Description:   Implementation of Quadlets-related subprograms
--
--  References:
--  [1] SPARK Team, SPARK83 - The SPADE Ada83 Kernel, Altran Praxis, 17 Oct.
--      2011.
--  [2] Programming languages - Ada, ISO/IEC 8652:1987, 15 Jun. 1987.
------------------------------------------------------------------------------

with Interfaces;
with Unchecked_Conversion;

package body Quadlets is

   function "+" (Left  : in Interfaces.Unsigned_32;
                 Right : in Interfaces.Unsigned_32)
     return Interfaces.Unsigned_32 renames Interfaces."+";

   function "-" (Left  : in Interfaces.Unsigned_32;
                 Right : in Interfaces.Unsigned_32)
     return Interfaces.Unsigned_32 renames Interfaces."-";

   function "*" (Left  : in Interfaces.Unsigned_32;
                 Right : in Interfaces.Unsigned_32)
     return Interfaces.Unsigned_32 renames Interfaces."*";

   subtype Booleans32_Index_T is Natural range 0 .. Bits - 1;
   type Booleans32_T is array (Booleans32_Index_T) of Boolean;
   pragma Pack (Booleans32_T);
   for Booleans32_T'Size use T'Size;

   function Booleans32 is
      new Unchecked_Conversion (Source => T,
                                Target => Booleans32_T);
   pragma Inline_Always (Booleans32);

   function From_Booleans32 is
      new Unchecked_Conversion (Source => Booleans32_T,
                                Target => T);
   pragma Inline_Always (From_Booleans32);

   function Negation
     (Value : in T) return T
   is
   begin
      --# assert Negation (Value) = T'Last - Value;
      --# accept Warning_Message, 13, Booleans32,
      --#   "All bit patterns are valid for this function";
      return From_Booleans32 (not Booleans32 (Value));
   end Negation;

   function Conjunction
     (Left  : in T;
      Right : in T) return T
   is
   begin
      --# accept Warning_Message, 13, Booleans32,
      --#   "All bit patterns are valid for this function";
      return From_Booleans32 (Booleans32 (Left) and Booleans32 (Right));
   end Conjunction;

   function Inclusive_Disjunction
     (Left  : in T;
      Right : in T) return T
   is
   begin
      --# accept Warning_Message, 13, Booleans32,
      --#   "All bit patterns are valid for this function";
      return From_Booleans32 (Booleans32 (Left) or Booleans32 (Right));
   end Inclusive_Disjunction;

   function Exclusive_Disjunction
     (Left  : in T;
      Right : in T) return T
   is
   begin
      --# accept Warning_Message, 13, Booleans32,
      --#   "All bit patterns are valid for this function";
      return From_Booleans32 (Booleans32 (Left) xor Booleans32 (Right));
   end Exclusive_Disjunction;

   function Left_Shift
     (Value  : in T;
      Amount : in Bit_Count_T) return T
   is
   begin
      return T (Interfaces.Shift_Left
                  (Value  => Interfaces.Unsigned_32 (Value),
                   Amount => Amount));
   end Left_Shift;

   function Right_Shift
     (Value  : in T;
      Amount : in Bit_Count_T) return T
   is
   begin
      return T (Interfaces.Shift_Right
                  (Value  => Interfaces.Unsigned_32 (Value),
                   Amount => Amount));
   end Right_Shift;

   function Right_Rotation
     (Value  : in T;
      Amount : in Bit_Count_T) return T
   is
   begin
      return T (Interfaces.Rotate_Right
                  (Value  => Interfaces.Unsigned_32 (Value),
                   Amount => Amount));
   end Right_Rotation;

   function Octet
     (Value : in T;
      Index : in Octet_Index_T) return Octets.T
   is
   begin
      return Octets.T
        (Conjunction (Right_Shift (Value, Index * 8), 16#FF#));
   end Octet;

   function Modular_Sum
     (Augend : in T;
      Addend : in T) return T
   is
   begin
      return T (Interfaces.Unsigned_32 (Augend) +
                  Interfaces.Unsigned_32 (Addend));
   end Modular_Sum;

   procedure Chained_Modular_Sum
     (Addend       : in     T;
      Augend_Lower : in out T;
      Augend_Upper : in out T;
      Overflow     : in out Boolean)
   is
   begin
      Augend_Lower := Modular_Sum (Augend_Lower, Addend);

      if Augend_Lower < Addend then  --  Overflow
         if Augend_Upper < T'Last then
            Augend_Upper := Augend_Upper + 1;
         else
            Augend_Upper := 0;
            Overflow     := True;
         end if;
      end if;
   end Chained_Modular_Sum;

   function Modular_Difference
     (Minuend    : in T;
      Subtrahend : in T) return T
   is
   begin
      return T (Interfaces.Unsigned_32 (Minuend) -
                  Interfaces.Unsigned_32 (Subtrahend));
   end Modular_Difference;

   function Modular_Product
     (Multiplicand : in T;
      Multiplier   : in T) return T
   is
   begin
      return T (Interfaces.Unsigned_32 (Multiplicand) *
                  Interfaces.Unsigned_32 (Multiplier));
   end Modular_Product;

end Quadlets;
