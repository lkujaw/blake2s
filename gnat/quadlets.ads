with Octets;

--# inherit Interfaces,
--#         Octets,
--#         Unchecked_Conversion;
package Quadlets is
   pragma Pure;

   Bits : constant := 32;

   type T is range 0 .. 4294967295;
   --# assert T'Base is Long_Integer;
   for T'Size use Bits;

   function Negation (Value : in T) return T;
   --# return T'Last - Value;
   pragma Inline_Always (Negation);

   --  Logical AND operation on the bits of Left and Right.
   function Conjunction (Left  : in T;
                         Right : in T) return T;
   --# return Conjunction (Left, Right);
   pragma Inline_Always (Conjunction);

   --  Logical OR operation on the bits of Left and Right.
   function Inclusive_Disjunction (Left  : in T;
                                   Right : in T) return T;
   --# return Inclusive_Disjunction (Left, Right);
   pragma Inline_Always (Inclusive_Disjunction);

   --  Logical XOR operation on the bits of Left and Right.
   function Exclusive_Disjunction (Left  : in T;
                                   Right : in T) return T;
   --# return Exclusive_Disjunction (Left, Right);
   pragma Inline_Always (Exclusive_Disjunction);

   subtype Bit_Count_T is Natural range 0 .. Bits - 1;

   function Left_Shift (Value  : in T;
                        Amount : in Bit_Count_T) return T;
   --# return (Value * (2 ** Amount)) mod (2 ** Bits);
   pragma Inline_Always (Left_Shift);

   function Right_Shift (Value  : in T;
                         Amount : in Bit_Count_T) return T;
   --# return Value / (2 ** Amount);
   pragma Inline_Always (Right_Shift);

   function Right_Rotation (Value  : in T;
                            Amount : in Bit_Count_T) return T;
   pragma Inline_Always (Right_Rotation);

   function Concatenation (Octet_1 : in Octets.T;
                           Octet_2 : in Octets.T;
                           Octet_3 : in Octets.T;
                           Octet_4 : in Octets.T) return T;
   pragma Inline_Always (Concatenation);

   subtype Octet_Index_T is Natural range 0 .. 3;

   function Octet (Value : in T;
                   Index : in Octet_Index_T) return Octets.T;
   pragma Inline_Always (Octet);

   function Modular_Sum (Augend : in T;
                         Addend : in T) return T;
   --# return (Augend + Addend) mod (2 ** Bits);
   pragma Inline_Always (Modular_Sum);

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
   pragma Inline_Always (Chained_Modular_Sum);

   function Modular_Difference (Minuend    : in T;
                                Subtrahend : in T) return T;
   --# return (Minuend - Subtrahend) mod (2 ** Bits);
   pragma Inline_Always (Modular_Difference);

   function Modular_Product (Multiplicand : in T;
                             Multiplier   : in T) return T;
   --# return (Multiplicand * Multiplier) mod (2 ** Bits);
   pragma Inline_Always (Modular_Product);

end Quadlets;
