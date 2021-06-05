--  NOTE: Unlike the rest of the Ada-BLAKE2 package, b2ssum is written in
--        full ISO Ada 95 so that streaming I/O may be utilized.

with Ada.Command_Line;

with Ada.Streams;
use type Ada.Streams.Stream_Element_Offset;

with Ada.Streams.Stream_IO;
with Ada.Text_IO;
with Ada.Unchecked_Conversion;

with BLAKE2S;

with Octets;
use type Octets.T;

with Octet_Arrays;

procedure B2SSum is
   function "=" (Left  : in BLAKE2S.Status_T;
                 Right : in BLAKE2S.Status_T) return Boolean
     renames BLAKE2S."=";

   package ACL renames Ada.Command_Line;
   package ATI renames Ada.Text_IO;
   package AST renames Ada.Streams;
   package ASI renames Ada.Streams.Stream_IO;

   subtype Hex_Index_T is Positive range 1 .. 2;
   subtype Hex_T is String (Hex_Index_T);
   subtype Hex_Digit_T is Natural range 0 .. 15;

   function Hex_Digit_To_Character
     (Hex_Digit : in Hex_Digit_T) return Character
   is
      Result    : Character;
   begin
      case Hex_Digit is
         when  0 =>
            Result := '0';
         when  1 =>
            Result := '1';
         when  2 =>
            Result := '2';
         when  3 =>
            Result := '3';
         when  4 =>
            Result := '4';
         when  5 =>
            Result := '5';
         when  6 =>
            Result := '6';
         when  7 =>
            Result := '7';
         when  8 =>
            Result := '8';
         when  9 =>
            Result := '9';
         when 10 =>
            Result := 'a';
         when 11 =>
            Result := 'b';
         when 12 =>
            Result := 'c';
         when 13 =>
            Result := 'd';
         when 14 =>
            Result := 'e';
         when 15 =>
            Result := 'f';
      end case;

      return Result;
   end Hex_Digit_To_Character;

   function Hex
     (Value : in Octets.T) return Hex_T
   is
   begin
      return Hex_T'(1 => Hex_Digit_To_Character (Hex_Digit_T (Value / 16)),
                    2 => Hex_Digit_To_Character (Hex_Digit_T (Value mod 16)));
   end Hex;

   Buffer_Size : constant := 16384;

   subtype Buffer_Index_T is Positive range 1 .. Buffer_Size;
   subtype SEA_Buffer_Index_T is AST.Stream_Element_Offset
     range 1 .. Buffer_Size;

   subtype Buffer_T     is Octet_Arrays.T            (Buffer_Index_T);
   subtype SEA_Buffer_T is AST.Stream_Element_Array (SEA_Buffer_Index_T);

   function SEA_To_Octet_Array is
      new Ada.Unchecked_Conversion (Source => SEA_Buffer_T,
                                    Target => Buffer_T);

   File    : ASI.File_Type;
   Buffer  : SEA_Buffer_T;
   First   : constant Positive := Positive (Buffer'First);
   Last    : AST.Stream_Element_Offset;
   Context : BLAKE2S.T;
   Digest  : BLAKE2S.Digest_Default_T;
begin  --  B2SSum
   pragma Assert (BLAKE2S.Self_Test = BLAKE2S.Success);

   Context := BLAKE2S.Initial (BLAKE2S.Digest_Length_Default);

   for I in Positive range 1 .. ACL.Argument_Count loop
      ASI.Open (File, ASI.In_File, ACL.Argument (I));

      loop
         ASI.Read (File, Buffer, Last);
         BLAKE2S.Incorporate_Flex
           (Context, SEA_To_Octet_Array (Buffer), First, Natural (Last));
         exit when Last < Buffer'Last;
      end loop;

      ASI.Close (File);
      BLAKE2S.Finalize (Context, Digest);
      for J in Digest'Range loop
         ATI.Put (Item => Hex (Digest (J)));
      end loop;
      ATI.Put ("  ");
      ATI.Put (ACL.Argument (I));
      ATI.New_Line;
   end loop;
end B2SSum;
