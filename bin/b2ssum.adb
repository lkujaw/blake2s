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
--  File:          b2ssum.adb (Ada Subprogram Body)
--  Language:      Ada (1995) [1]
--  Author:        Lev Kujawski
--  Description:   BLAKE2s [2] file hashing utility
--
--  References:
--  [1] Information technology - Programming languages - Ada,
--      ISO/IEC 8652:1995(E), 15 Feb. 1995.
--  [3] M-J. Saarinen and J-P. Aumasson, "The BLAKE2 Cryptographic Hash and
--      Message Authentication Code (MAC)," RFC 7693, Nov. 2015.
------------------------------------------------------------------------------
--  NOTE: Unlike the rest of the BLAKE2s for Ada package, b2ssum is written
--        in non-SPARK Ada (1995) so that streaming I/O may be utilized.
--! rule off Exception_Rule

with Ada.Characters.Handling;
with Ada.Command_Line;

with Ada.Streams;
use type Ada.Streams.Stream_Element_Offset;

with Ada.Streams.Stream_IO;
with Ada.Text_IO;
with Ada.Text_IO.Text_Streams;
with Ada.Strings.Unbounded;

with BLAKE2S;
use type BLAKE2S.Digest_T;
--  Quash false positive from AdaControl:
--! rule off Use_Rule
use type BLAKE2S.Status_T;
--! rule on Use_Rule

with Octets;
use type Octets.T;

with Octet_Arrays;

procedure B2SSum is

   package ACH renames Ada.Characters.Handling;
   package ACL renames Ada.Command_Line;
   package ATI renames Ada.Text_IO;
   package ATS renames Ada.Text_IO.Text_Streams;
   package AST renames Ada.Streams;
   package ASI renames Ada.Streams.Stream_IO;
   package UST renames Ada.Strings.Unbounded;

   subtype Hex_Index_T is Positive range 1 .. 2;
   subtype Hex_T is String (Hex_Index_T);
   subtype Hex_Digit_T is Natural range 0 .. 15;

   function Character_To_Hex_Digit
     (Hex_Character : in Character) return Hex_Digit_T
   is
      Normal : constant Character := ACH.To_Upper (Hex_Character);
      Result : Hex_Digit_T;
   begin
      case Normal is
         when '0' =>
            Result := 0;
         when '1' =>
            Result := 1;
         when '2' =>
            Result := 2;
         when '3' =>
            Result := 3;
         when '4' =>
            Result := 4;
         when '5' =>
            Result := 5;
         when '6' =>
            Result := 6;
         when '7' =>
            Result := 7;
         when '8' =>
            Result := 8;
         when '9' =>
            Result := 9;
         when 'A' =>
            Result := 10;
         when 'B' =>
            Result := 11;
         when 'C' =>
            Result := 12;
         when 'D' =>
            Result := 13;
         when 'E' =>
            Result := 14;
         when 'F' =>
            Result := 15;
         when others =>
            raise Constraint_Error;
      end case;

      return Result;
   end Character_To_Hex_Digit;

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

   Buffer_Octets : constant := 16384;
   Buffer_Bits   : constant := Buffer_Octets * Octets.Bits;

   subtype Buffer_Index_T is Positive range 1 .. Buffer_Octets;
   subtype SEA_Buffer_Index_T is AST.Stream_Element_Offset
     range 1 .. Buffer_Octets;

   subtype Buffer_T     is Octet_Arrays.T           (Buffer_Index_T);
   subtype SEA_Buffer_T is AST.Stream_Element_Array (SEA_Buffer_Index_T);

   Buffer : SEA_Buffer_T;
   for Buffer'Size use Buffer_Bits;
   View : Buffer_T;
   for View'Address use Buffer'Address;
   for View'Size use Buffer_Bits;

   Invalid_Hash_List : exception;

   Digest : BLAKE2S.Digest_Default_T;

   procedure Hash_File
     (File_Name : in String)
   is
      File      : ASI.File_Type;
      Stream    : ASI.Stream_Access;
      First     : constant Positive := Positive (Buffer'First);

      procedure Hash_Stream
      is
         Context : BLAKE2S.T;
         Last    : AST.Stream_Element_Offset;
      begin
         Context := BLAKE2S.Initial (BLAKE2S.Digest_Length_Default);
         loop
            AST.Read (Stream.all, Buffer, Last);
            BLAKE2S.Incorporate_Flex (Context, View, First, Natural (Last));
            exit when Last < Buffer'Last;
         end loop;
         BLAKE2S.Finalize (Context, Digest);
      end Hash_Stream;
   begin  --  Hash_File
      if File_Name = "-" then
         Stream := ASI.Stream_Access (ATS.Stream (ATI.Standard_Input));
         Hash_Stream;
      else
         ASI.Open (File, ASI.In_File, File_Name);
         Stream := ASI.Stream (File);
         Hash_Stream;
         ASI.Close (File);
      end if;
   end Hash_File;

   procedure Hash_Files
   is
      procedure Print_Hash
        (File_Name : in String)
      is
      begin
         for J in Digest'Range loop
            ATI.Put (Item => Hex (Digest (J)));
         end loop;
         ATI.Put ("  ");
         ATI.Put (File_Name);
         ATI.New_Line;
      end Print_Hash;
   begin  --  Hash_Files
      for I in Positive range 1 .. ACL.Argument_Count loop
         Hash_File (ACL.Argument (I));
         Print_Hash (ACL.Argument (I));
      end loop;
   end Hash_Files;

   procedure Verify_Lists
   is
      List_File : ATI.File_Type;

      procedure Verify_List
      is
         Hash  : BLAKE2S.Digest_Default_T;
         Hex_1 : Character;
         Hex_2 : Character;
      begin
         while not ATI.End_Of_Line loop
            for I in Positive range Hash'Range loop
               ATI.Get (Hex_1);
               ATI.Get (Hex_2);
               if
                 not ACH.Is_Hexadecimal_Digit (Hex_1) or else
                 not ACH.Is_Hexadecimal_Digit (Hex_2)
               then
                  raise Invalid_Hash_List;
               end if;

               Hash (I) :=
                 Octets.T (Character_To_Hex_Digit (Hex_1)) * 16 +
                 Octets.T (Character_To_Hex_Digit (Hex_2));
            end loop;

            ATI.Get (Hex_1);
            ATI.Get (Hex_2);

            if Hex_1 /= ' ' or else Hex_2 /= ' ' then
               raise Invalid_Hash_List;
            end if;

            declare
               subtype Partial_Index_T is Positive range 1 .. 256;
               Unbounded_File_Name : UST.Unbounded_String :=
                 UST.Null_Unbounded_String;
               Partial : String (Partial_Index_T);
               Last : Natural;
            begin
               loop
                  ATI.Get_Line (Partial, Last);
                  UST.Append (Unbounded_File_Name, Partial (1 .. Last));
                  exit when Last < Partial'Last;
               end loop;

               declare
                  File_Name : constant String :=
                    UST.To_String (Unbounded_File_Name);
               begin
                  ATI.Put (File_Name & ": ");
                  Hash_File (File_Name);
                  if Digest = Hash then
                     ATI.Put_Line ("OK");
                  else
                     ATI.Put_Line ("FAILED");
                  end if;
               end;
            end;
         end loop;
      end Verify_List;
   begin  --  Verify_Lists
      for I in Positive range 2 .. ACL.Argument_Count loop
         declare
         begin
            if ACL.Argument (I) = "-" then
               Verify_List;
            else
               ATI.Open (List_File, ATI.In_File, ACL.Argument (I));
               ATI.Set_Input (List_File);
               Verify_List;
               ATI.Set_Input (ATI.Standard_Input);
               ATI.Close (List_File);
            end if;
         exception
            when Invalid_Hash_List =>
               ATI.Put_Line
                 ("Error on line " & ATI.Positive_Count'Image (ATI.Line) &
                  ", skipping invalid hash list: " & ACL.Argument (I));
         end;
      end loop;
   end Verify_Lists;

begin  --  B2SSum
   pragma Assert (BLAKE2S.Self_Test = BLAKE2S.Success);

   if ACL.Argument_Count = 0 then
      --  Print usage
      ATI.Put_Line ("Usage: " & Ada.Command_Line.Command_Name &
                      " [OPTION]... [FILE]...");
   elsif ACL.Argument (1) = "-c" then
      Verify_Lists;
   else
      Hash_Files;
   end if;

end B2SSum;
