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

with Unchecked_Conversion;

package body Quadlets is

   subtype Booleans32_Index_T is Natural range 0 .. Bits - 1;
   type Booleans32_T is array (Booleans32_Index_T) of Boolean;
   pragma Pack (Booleans32_T);
   for Booleans32_T'Size use T'Size;

   subtype Power_T is T range 1 .. 2147483648;
   type Powers_T is array (Bit_Count_T) of Power_T;
   Powers : constant Powers_T :=
     Powers_T'(1,          2,           4,           8,
              16,         32,          64,         128,
             256,        512,        1024,        2048,
            4096,       8192,       16384,       32768,
           65536,     131072,      262144,      524288,
         1048576,    2097152,     4194304,     8388608,
        16777216,   33554432,    67108864,   134217728,
       268435456,  536870912,  1073741824,  2147483648);
   --# for Powers declare Rule;
   --  The preceding annotation causes SPARK to generate a unique rule per
   --  array element, which is necessary for formal verification.
   for Powers'Size use (Bit_Count_T'Last + 1) * Bits;

   subtype Mask_T is T range 1 .. 4294967295;
   type Masks_T is array (Bit_Count_T) of Mask_T;
   Masks : constant Masks_T :=
     Masks_T'(4294967295,  2147483647,  1073741823,  536870911,
               268435455,   134217727,    67108863,   33554431,
                16777215,     8388607,     4194303,    2097151,
                 1048575,      524287,      262143,     131071,
                   65535,       32767,       16383,       8191,
                    4095,        2047,        1023,        511,
                     255,         127,          63,         31,
                      15,           7,           3,          1);
   --# for Masks declare Rule;
   for Masks'Size use (Bit_Count_T'Last + 1) * Bits;

   function Booleans32 is
      new Unchecked_Conversion (Source => T,
                                Target => Booleans32_T);

   function From_Booleans32 is
      new Unchecked_Conversion (Source => Booleans32_T,
                                Target => T);

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
      --# assert Masks (Amount) in Mask_T and
      --#        Masks (Amount) = (2 ** (Bits - Amount)) - 1 and
      --#        Powers (Amount) in Power_T and
      --#        Powers (Amount) = 2 ** Amount;
      return Conjunction (Value, Masks (Amount)) * Powers (Amount);
   end Left_Shift;

   function Right_Shift
     (Value  : in T;
      Amount : in Bit_Count_T) return T
   is
   begin
      --# assert Powers (Amount) in Power_T and
      --#        Powers (Amount) = 2 ** Amount;
      return Value / Powers (Amount);
   end Right_Shift;

   function Right_Rotation
     (Value  : in T;
      Amount : in Bit_Count_T) return T
   is
   begin
      return Inclusive_Disjunction
        (Right_Shift (Value, Amount),
         Left_Shift  (Value, Bit_Count_T
           (Conjunction (Bits - T (Amount), Bits - 1))));
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
      Result : T;
   begin
      Result := Negation (Augend);

      if Result < Addend then  --  Overflow
         Result := T'Pred (Addend - Result);
      else
         Result := Augend + Addend;
      end if;

      return Result;
   end Modular_Sum;

   procedure Chained_Modular_Sum
     (Addend         : in     T;
      Augend_Lower   : in out T;
      Augend_Upper   : in out T;
      Overflow       : in out Boolean)
   is
      Negated_Augend : T;
   begin
      Negated_Augend := Negation (Augend_Lower);

      if Negated_Augend < Addend then  --  Overflow
         Augend_Lower := T'Pred (Addend - Negated_Augend);
         if Augend_Upper < T'Last then
            Augend_Upper := Augend_Upper + 1;
         else
            Augend_Upper := 0;
            Overflow     := True;
         end if;
      else
         Augend_Lower := Augend_Lower + Addend;
      end if;
   end Chained_Modular_Sum;

   function Modular_Difference
     (Minuend    : in T;
      Subtrahend : in T) return T
   is
      Result     : T;
   begin
      if Subtrahend > Minuend then  --  Underflow
         Result := T'Succ (Negation (Subtrahend) + Minuend);
      else
         Result := Minuend - Subtrahend;
      end if;

      return Result;
   end Modular_Difference;

   function Modular_Product
     (Multiplicand : in T;
      Multiplier   : in T) return T
   is
      X_Lower      : T;  --  Multiplicand
      Y_Lower      : T;  --  Multiplier
      Result       : T;
   begin
      X_Lower := Conjunction (Multiplicand, 16#FFFF#);
      Y_Lower := Conjunction (Multiplier, 16#FFFF#);

      --  X_Upper * X_Upper is out of the range of Result.
      Result := Right_Shift (Multiplier, 16) * X_Lower;
      Result := Modular_Sum (Result, Y_Lower *
                  Right_Shift (Multiplicand, 16));
      Result := Left_Shift (Result, 16);
      Result := Modular_Sum (Result, Y_Lower * X_Lower);

      return Result;
   end Modular_Product;

end Quadlets;
