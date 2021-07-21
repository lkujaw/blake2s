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
--  File:          b2stest.adb (Ada Subprogram Body)
--  Language:      SPARK83 [1] subset of Ada (1987) [2]
--  Author:        Lev Kujawski
--  Description:   BLAKE2s [3] for Ada test vector verifier
--
--  References:
--  [1] SPARK Team, SPARK83 - The SPADE Ada83 Kernel, Altran Praxis, 17 Oct.
--      2011.
--  [2] Programming languages - Ada, ISO/IEC 8652:1987, 15 Jun. 1987.
--  [3] M-J. Saarinen and J-P. Aumasson, "The BLAKE2 Cryptographic Hash and
--      Message Authentication Code (MAC)," RFC 7693, Nov. 2015.
------------------------------------------------------------------------------

with BLAKE2S;

with Octets;
with Octet_Arrays;

with SPARK_IO;
with SPARK_IO_Standard;

--# inherit BLAKE2S,
--#         Octets,
--#         Octet_Arrays,
--#         SPARK_IO,
--#         SPARK_IO_Standard;
--# main_program;
procedure B2STest
--# global in     SPARK_IO_Standard.Output;
--#        in out SPARK_IO.Inputs;
--#        in out SPARK_IO.Outputs;
--#        in out SPARK_IO.State;
--# derives SPARK_IO.Inputs,
--#         SPARK_IO.State   from *,
--#                               SPARK_IO.State &
--#         SPARK_IO.Outputs from *,
--#                               SPARK_IO.Inputs,
--#                               SPARK_IO.State,
--#                               SPARK_IO_Standard.Output;
is
   function "=" (Left  : in BLAKE2S.Digest_T;
                 Right : in BLAKE2S.Digest_T) return Boolean
     renames BLAKE2S."=";

   function ">" (Left  : in Octets.T;
                 Right : in Octets.T) return Boolean
     renames Octets.">";

   function "+" (Left  : in Octets.T;
                 Right : in Octets.T) return Octets.T
     renames Octets."+";

   function "*" (Left  : in Octets.T;
                 Right : in Octets.T) return Octets.T
     renames Octets."*";

   function "=" (Left  : in SPARK_IO.File_Status_T;
                 Right : in SPARK_IO.File_Status_T) return Boolean
     renames SPARK_IO."=";

   Tests_Passed : Natural := 0;
   Tests_Failed : Natural := 0;
   File_Name    : constant String := "blake2s.txt";
   File         : SPARK_IO.File_T;
   File_Status  : SPARK_IO.File_Status_T;
   File_Parsed  : Boolean;

   procedure Pass
   --# global in     SPARK_IO_Standard.Output;
   --#        in out SPARK_IO.Outputs;
   --#        in out Tests_Passed;
   --# derives SPARK_IO.Outputs from *,
   --#                               SPARK_IO_Standard.Output &
   --#         Tests_Passed     from *;
   is
   begin
      if Tests_Passed < Natural'Last then
         Tests_Passed := Tests_Passed + 1;
      end if;
      SPARK_IO.Put_Line (SPARK_IO_Standard.Output, ": PASS", 0);
   end Pass;

   procedure Fail
   --# global in     SPARK_IO_Standard.Output;
   --#        in out SPARK_IO.Outputs;
   --#        in out Tests_Failed;
   --# derives SPARK_IO.Outputs from *,
   --#                               SPARK_IO_Standard.Output &
   --#         Tests_Failed     from *;
   is
   begin
      if Tests_Failed < Natural'Last then
         Tests_Failed := Tests_Failed + 1;
      end if;
      SPARK_IO.Put_Line (SPARK_IO_Standard.Output, ": FAIL", 0);
   end Fail;

   procedure Parse_File
     (Parsed_File : out Boolean)
   --# global in     File;
   --#        in     SPARK_IO_Standard.Output;
   --#        in out SPARK_IO.Inputs;
   --#        in out SPARK_IO.Outputs;
   --#        in out Tests_Failed;
   --#        in out Tests_Passed;
   --# derives Parsed_File,
   --#         SPARK_IO.Inputs  from File,
   --#                               SPARK_IO.Inputs &
   --#         SPARK_IO.Outputs from *,
   --#                               File,
   --#                               SPARK_IO.Inputs,
   --#                               SPARK_IO_Standard.Output &
   --#         Tests_Failed,
   --#         Tests_Passed     from *,
   --#                               File,
   --#                               SPARK_IO.Inputs;
   is
      subtype Line_Index_T is Positive range 1 .. 1024;
      subtype Line_T is String (Line_Index_T);

      subtype Message_Length_T is Natural range 0 .. 256;
      subtype Message_Index_T is Message_Length_T range 1 .. 256;
      subtype Message_T is Octet_Arrays.T (Message_Index_T);

      subtype Key_Octet_Array_T is Octet_Arrays.T (BLAKE2S.Key_Index_T);

      Test_Number    : Positive := 1;
      Line           : Line_T;
      Line_Last      : Natural;
      Line_Parsed    : Boolean := False;
      Message        : Message_T := Message_T'(others => 0);
      Message_Length : Message_Length_T := 0;
      Key_Prefix     : constant String := "key:" & ASCII.HT;
      Key            : Key_Octet_Array_T := Key_Octet_Array_T'(others => 0);

      procedure Read_Hex
        (Source_First  : in     Positive;
         Source_Last   : in     Positive;
         Target_Length : in     Positive;
         Target        :    out Octet_Arrays.T;
         Parsed_Hex    :    out Natural)
      --# global in Line;
      --# derives Parsed_Hex,
      --#         Target     from Line,
      --#                         Source_First,
      --#                         Source_Last,
      --#                         Target_Length;
      --# pre Source_Last in Line'Range and
      --#       Target'First = Positive'First and
      --#         Target_Length = Target'Length;
      --# post Parsed_Hex <= Target_Length;
      is
         Source_Index : Positive;
         Target_Index : Positive;
         Upper_Hex    : Octets.T;
         Lower_Hex    : Octets.T;

         function Hex_Digit
           (Digit  : in Character) return Octets.T
         is
            Result : Octets.T;
         begin
            case Digit is
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
               when 'a' =>
                  Result := 10;
               when 'b' =>
                  Result := 11;
               when 'c' =>
                  Result := 12;
               when 'd' =>
                  Result := 13;
               when 'e' =>
                  Result := 14;
               when 'f' =>
                  Result := 15;
               when others =>
                  Result := 255;
            end case;

            return Result;
         end Hex_Digit;
      begin  --  Read_Hex
         Target       := (others => 0);
         Source_Index := Source_First;
         Target_Index := Positive'First;

         if ((Source_Last - Source_First) + 1) mod 2 = 0 and then
           ((Source_Last - Source_First) + 1) / 2 <= Target_Length
         then

            while Source_Index < Source_Last loop
               --# assert
               --#   Source_Index >= Source_First and
               --#   Source_Last <= Line'Last and
               --#   Source_Index < Source_Last and
               --#   Target_Length = Target'Last and
               --#   Target_Length >= ((Source_Last - Source_First) + 1) / 2
               --#     and
               --#   Target_Index >= Target'First and
               --#   Target_Index = (Source_Index - Source_First) / 2 + 1;
               Upper_Hex := Hex_Digit (Line (Source_Index));
               exit when Upper_Hex > 15;
               Source_Index := Source_Index + 1;

               Lower_Hex := Hex_Digit (Line (Source_Index));
               exit when Lower_Hex > 15;
               Source_Index := Source_Index + 1;

               Target (Target_Index) := Upper_Hex * 16 + Lower_Hex;
               Target_Index := Target_Index + 1;
            end loop;
         end if;
         --# assert Target_Index <= Target_Length + 1;

         Parsed_Hex := Target_Index - 1;
      end Read_Hex;

      function Is_Prefix
        (Prefix : in String) return Boolean
      --# global in Line;
      --# pre Prefix'Length < 10;
      is
         Result : Boolean := True;
      begin
         for I in Positive range Positive'First .. Prefix'Last loop
            --# assert I in Prefix'Range and I in Line'Range;
            if Line (I) /= Prefix (I) then
               Result := False;
               exit;
            end if;
         end loop;

         return Result;
      end Is_Prefix;

      procedure Parse_Line
        (Parsed_Line : out Boolean)
      --# global in     Line;
      --#        in     Line_Last;
      --#        in     SPARK_IO_Standard.Output;
      --#        in out Key;
      --#        in out Message;
      --#        in out Message_Length;
      --#        in out SPARK_IO.Outputs;
      --#        in out Tests_Failed;
      --#        in out Tests_Passed;
      --#        in out Test_Number;
      --# derives Key,
      --#         Message,
      --#         Message_Length,
      --#         Test_Number      from *,
      --#                               Line,
      --#                               Line_Last &
      --#         Tests_Failed,
      --#         Tests_Passed     from *,
      --#                               Key,
      --#                               Line,
      --#                               Line_Last,
      --#                               Message,
      --#                               Message_Length &
      --#         Parsed_Line      from Line,
      --#                               Line_Last &
      --#         SPARK_IO.Outputs from *,
      --#                               Key,
      --#                               Line,
      --#                               Line_Last,
      --#                               Message,
      --#                               Message_Length,
      --#                               SPARK_IO_Standard.Output,
      --#                               Test_Number;
      --# pre Line_Last <= Line'Last;
      is
         subtype Digest_Octet_Array_T is
           Octet_Arrays.T (BLAKE2S.Digest_Index_T);

         Final           : Natural;
         Message_Digest  : BLAKE2S.Digest_Default_T;
         Expected_Digest : Digest_Octet_Array_T;
         Context         : BLAKE2S.T;
      begin
         --# assert Message_Length <= Message'Last;
         Parsed_Line := True;

         if Line_Last > 3 then
            if Is_Prefix ("in:" & ASCII.HT) then
               Read_Hex (5, Line_Last, Message'Length,
                         Message, Message_Length);
               if Message_Length /= (Line_Last - 4) / 2 then
                  Parsed_Line := False;
               end if;
            elsif Is_Prefix (Key_Prefix) then
               Read_Hex (6, Line_Last, Key'Length, Key, Final);
               if Final /= BLAKE2S.Digest_Length_Default then
                  Parsed_Line := False;
               end if;
            elsif Is_Prefix ("hash:" & ASCII.HT) then
               Read_Hex (7, Line_Last, Expected_Digest'Length,
                         Expected_Digest, Final);
               if Final = BLAKE2S.Key_Length_Default then
                  SPARK_IO.Put_String (SPARK_IO_Standard.Output,
                                       " Test ", 0);
                  SPARK_IO.Put_Integer (File  => SPARK_IO_Standard.Output,
                                        Item  => Test_Number,
                                        Width => 3,
                                        Base  => 10);
                  BLAKE2S.Hash_Keyed_Flex
                    (Key           => BLAKE2S.Key_Default_T (Key),
                     Key_Length    => BLAKE2S.Key_Length_Default,
                     Message       => Message,
                     Message_First => Message'First,
                     Message_Last  => Message_Length,
                     Digest_Length => BLAKE2S.Digest_Length_Default,
                     Digest        => Message_Digest);

                  if Message_Digest =
                    BLAKE2S.Digest_Default_T (Expected_Digest)
                  then
                     Context := BLAKE2S.Initial_Keyed_Flex
                       (Digest_Length => BLAKE2S.Digest_Length_Default,
                        Key           => BLAKE2S.Key_Default_T (Key),
                        Key_Length    => BLAKE2S.Key_Length_Default);
                     BLAKE2S.Incorporate_Flex
                       (Context       => Context,
                        Message       => Message,
                        Message_First => Message'First,
                        Message_Last  => Message_Length);

                     --# accept Flow_Message, 10, Context,
                     --#   "The hash state is no longer needed";
                     BLAKE2S.Finalize
                       (Context => Context,
                        Digest  => Message_Digest);
                     --# end accept;

                     if Message_Digest =
                       BLAKE2S.Digest_Default_T (Expected_Digest)
                     then
                        Pass;
                     else
                        Fail;
                     end if;
                  else
                     Fail;
                  end if;

                  if Test_Number < Positive'Last then
                     Test_Number := Test_Number + 1;
                  end if;
               else
                  Parsed_Line := False;
               end if;
            else
               Parsed_Line := False;
            end if;
         end if;
      end Parse_Line;
   begin  --  Parse_File
      while not SPARK_IO.End_Of_File (File) loop
         --# assert True;
         SPARK_IO.Get_Line (File, Line, Line_Last);
         Parse_Line (Line_Parsed);
         exit when not Line_Parsed;
      end loop;

      Parsed_File := Line_Parsed;
   end Parse_File;
begin  --  B2STest
   SPARK_IO.Put_Line (SPARK_IO_Standard.Output,
                      "==== BLAKE2s for Ada Tests ====", 0);
   SPARK_IO.Put_Line
     (SPARK_IO_Standard.Output,
      "NOTE: Expect 257 tests to pass for a conformant build.", 0);
   SPARK_IO.New_Line (SPARK_IO_Standard.Output, 1);

   -------  BLAKE2S SELF TEST -------
   SPARK_IO.Put_String (SPARK_IO_Standard.Output,
                        "Self-test", 0);
   --# accept Flow_Message, 22, "Check for errors outside of the SPARK model";
   case BLAKE2S.Self_Test is
      when BLAKE2S.Success =>
         Pass;
      when BLAKE2S.Failure =>
         Fail;
   end case;
   --# end accept;

   SPARK_IO.Open (File, SPARK_IO.In_File, File_Name, "", File_Status);

   if File_Status = SPARK_IO.Success then
      Parse_File (File_Parsed);

      if File_Parsed then
         SPARK_IO.New_Line (SPARK_IO_Standard.Output, 1);
         SPARK_IO.Put_Line (SPARK_IO_Standard.Output,
                            "==== BLAKE2s for Ada Summary ====", 0);
         SPARK_IO.Put_String (SPARK_IO_Standard.Output, "Tests passed: ", 0);
         SPARK_IO.Put_Integer (File  => SPARK_IO_Standard.Output,
                               Item  => Integer'(Tests_Passed),
                               Width => 3,
                               Base  => 10);
         SPARK_IO.New_Line (SPARK_IO_Standard.Output, 1);
         SPARK_IO.Put_String (SPARK_IO_Standard.Output, "Tests failed: ", 0);
         SPARK_IO.Put_Integer (File  => SPARK_IO_Standard.Output,
                               Item  => Integer'(Tests_Failed),
                               Width => 3,
                               Base  => 10);
         SPARK_IO.New_Line (SPARK_IO_Standard.Output, 1);
      else
         SPARK_IO.Put_Line
           (SPARK_IO_Standard.Output,
            "ERROR: Could not parse the file '" & File_Name & "'.", 0);
      end if;
   else
      SPARK_IO.Put_Line
        (SPARK_IO_Standard.Output,
         "ERROR: Could not open the file '" & File_Name & "'.", 0);
   end if;
end B2STest;
