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
--  File:          blake2s.adb (Ada Package Body)
--  Language:      SPARK83 [1] subset of Ada (1987) [2]
--  Author:        Lev Kujawski
--  Description:   Implementation of the BLAKE2s hash function [3]
--
--  References:
--  [1] SPARK Team, SPARK83 - The SPADE Ada83 Kernel, Altran Praxis, 17 Oct.
--      2011.
--  [2] Programming languages - Ada, ISO/IEC 8652:1987, 15 Jun. 1987.
--  [3] M-J. Saarinen and J-P. Aumasson, "The BLAKE2 Cryptographic Hash and
--      Message Authentication Code (MAC)," RFC 7693, Nov. 2015.
------------------------------------------------------------------------------

package body BLAKE2S is

   Initialization_Vectors : constant Hash_State_T :=
     Hash_State_T'(16#6A09E667#, 16#BB67AE85#, 16#3C6EF372#, 16#A54FF53A#,
                   16#510E527F#, 16#9B05688C#, 16#1F83D9AB#, 16#5BE0CD19#);

   function Is_Overflowed
     (Context : in T) return Boolean
   --# return Context.Overflowed;
   is
   begin
      return Context.Overflowed;
   end Is_Overflowed;

   function Digest_Length_Of
     (Context : in T) return Digest_Index_T
   --# return Context.Digest_Length;
   is
   begin
      return Context.Digest_Length;
   end Digest_Length_Of;

   procedure Compress
    (Last_IV : in     Quadlets.T;
     Context : in out T)
   --# derives Context from *,
   --#                      Last_IV;
   --# post Context.Buffer_Index = Context~.Buffer_Index and
   --#      Context.Digest_Length = Context~.Digest_Length;
   is
      subtype Sigma_Major_T is Natural range 0 .. 9;
      subtype Quadlet_Octet_Index_T is Octets.T range 0 .. 15;
      type Sigma_T is array (Sigma_Major_T, Quadlet_Octet_Index_T) of
        Quadlet_Octet_Index_T;
      for Sigma_T'Size use 160 * Octets.Bits;

      Sigma : constant Sigma_T := Sigma_T'(
       0 => (00, 01, 02, 03, 04, 05, 06, 07, 08, 09, 10, 11, 12, 13, 14, 15),
       1 => (14, 10, 04, 08, 09, 15, 13, 06, 01, 12, 00, 02, 11, 07, 05, 03),
       2 => (11, 08, 12, 00, 05, 02, 15, 13, 10, 14, 03, 06, 07, 01, 09, 04),
       3 => (07, 09, 03, 01, 13, 12, 11, 14, 02, 06, 05, 10, 04, 00, 15, 08),
       4 => (09, 00, 05, 07, 02, 04, 10, 15, 14, 01, 11, 12, 06, 08, 03, 13),
       5 => (02, 12, 06, 10, 00, 11, 08, 03, 04, 13, 07, 05, 15, 14, 01, 09),
       6 => (12, 05, 01, 15, 14, 13, 04, 10, 00, 07, 06, 03, 09, 02, 08, 11),
       7 => (13, 11, 07, 14, 12, 01, 03, 09, 05, 00, 15, 04, 08, 06, 02, 10),
       8 => (06, 15, 14, 09, 11, 03, 00, 08, 12, 02, 13, 07, 01, 04, 10, 05),
       9 => (10, 02, 08, 04, 07, 06, 01, 05, 15, 11, 09, 14, 03, 12, 13, 00));

      V : Quadlet_Buffer_T;

      procedure Mix
        (A : in Buffer_Index_T;
         B : in Buffer_Index_T;
         C : in Buffer_Index_T;
         D : in Buffer_Index_T;
         X : in Quadlets.T;
         Y : in Quadlets.T)
      --# global in out V;
      --# derives V from *,
      --#                A,
      --#                B,
      --#                C,
      --#                D,
      --#                X,
      --#                Y;
      is
      begin
         V (A) := Quadlets.Modular_Sum
           (V (A), Quadlets.Modular_Sum (V (B), X));
         --# assert True;
         V (D) := Quadlets.Right_Rotation
           (Quadlets.Exclusive_Disjunction (V (D), V (A)), 16);
         --# assert True;
         V (C) := Quadlets.Modular_Sum (V (C), V (D));
         --# assert True;
         V (B) := Quadlets.Right_Rotation
           (Quadlets.Exclusive_Disjunction (V (B), V (C)), 12);
         --# assert True;
         V (A) := Quadlets.Modular_Sum
           (V (A), Quadlets.Modular_Sum (V (B), Y));
         --# assert True;
         V (D) := Quadlets.Right_Rotation
           (Quadlets.Exclusive_Disjunction (V (D), V (A)), 8);
         --# assert True;
         V (C) := Quadlets.Modular_Sum (V (C), V (D));
         --# assert True;
         V (B) := Quadlets.Right_Rotation
           (Quadlets.Exclusive_Disjunction (V (B), V (C)), 7);
      end Mix;
      pragma Inline (Mix);

      procedure Round (N : in Sigma_Major_T)
      --# global in     Context;
      --#        in out V;
      --# derives V from *,
      --#                Context,
      --#                N;
      is
      begin
         --# assert
         --#   for all I in Sigma_Major_T =>
         --#    (Sigma (I,  0) in Quadlet_Octet_Index_T and
         --#     Sigma (I,  1) in Quadlet_Octet_Index_T and
         --#     Sigma (I,  2) in Quadlet_Octet_Index_T and
         --#     Sigma (I,  3) in Quadlet_Octet_Index_T and
         --#     Sigma (I,  4) in Quadlet_Octet_Index_T and
         --#     Sigma (I,  5) in Quadlet_Octet_Index_T and
         --#     Sigma (I,  6) in Quadlet_Octet_Index_T and
         --#     Sigma (I,  7) in Quadlet_Octet_Index_T and
         --#     Sigma (I,  8) in Quadlet_Octet_Index_T and
         --#     Sigma (I,  9) in Quadlet_Octet_Index_T and
         --#     Sigma (I, 10) in Quadlet_Octet_Index_T and
         --#     Sigma (I, 11) in Quadlet_Octet_Index_T and
         --#     Sigma (I, 12) in Quadlet_Octet_Index_T and
         --#     Sigma (I, 13) in Quadlet_Octet_Index_T and
         --#     Sigma (I, 14) in Quadlet_Octet_Index_T and
         --#     Sigma (I, 15) in Quadlet_Octet_Index_T);
         Mix (A => 0, B => 4, C =>  8, D => 12,
              X => Context.Input_Buffer (Natural (Sigma (N,  0))),
              Y => Context.Input_Buffer (Natural (Sigma (N,  1))));
         Mix (A => 1, B => 5, C =>  9, D => 13,
              X => Context.Input_Buffer (Natural (Sigma (N,  2))),
              Y => Context.Input_Buffer (Natural (Sigma (N,  3))));
         Mix (A => 2, B => 6, C => 10, D => 14,
              X => Context.Input_Buffer (Natural (Sigma (N,  4))),
              Y => Context.Input_Buffer (Natural (Sigma (N,  5))));
         Mix (A => 3, B => 7, C => 11, D => 15,
              X => Context.Input_Buffer (Natural (Sigma (N,  6))),
              Y => Context.Input_Buffer (Natural (Sigma (N,  7))));
         Mix (A => 0, B => 5, C => 10, D => 15,
              X => Context.Input_Buffer (Natural (Sigma (N,  8))),
              Y => Context.Input_Buffer (Natural (Sigma (N,  9))));
         Mix (A => 1, B => 6, C => 11, D => 12,
              X => Context.Input_Buffer (Natural (Sigma (N, 10))),
              Y => Context.Input_Buffer (Natural (Sigma (N, 11))));
         Mix (A => 2, B => 7, C =>  8, D => 13,
              X => Context.Input_Buffer (Natural (Sigma (N, 12))),
              Y => Context.Input_Buffer (Natural (Sigma (N, 13))));
         Mix (A => 3, B => 4, C =>  9, D => 14,
              X => Context.Input_Buffer (Natural (Sigma (N, 14))),
              Y => Context.Input_Buffer (Natural (Sigma (N, 15))));
      end Round;
      pragma Inline (Round);
   begin  --  Compress
      V := Quadlet_Buffer_T'
         (0 => Context.Hash_State (0),
          1 => Context.Hash_State (1),
          2 => Context.Hash_State (2),
          3 => Context.Hash_State (3),
          4 => Context.Hash_State (4),
          5 => Context.Hash_State (5),
          6 => Context.Hash_State (6),
          7 => Context.Hash_State (7),
          8 => Initialization_Vectors (0),
          9 => Initialization_Vectors (1),
         10 => Initialization_Vectors (2),
         11 => Initialization_Vectors (3),
         12 => Quadlets.Exclusive_Disjunction (Initialization_Vectors (4),
                                               Context.Input_Octets_Lower),
         13 => Quadlets.Exclusive_Disjunction (Initialization_Vectors (5),
                                               Context.Input_Octets_Upper),
         14 => Last_IV,
         15 => Initialization_Vectors (7));

      Round (0);
      Round (1);
      Round (2);
      Round (3);
      Round (4);
      Round (5);
      Round (6);
      Round (7);
      Round (8);
      Round (9);

      Context.Hash_State (0) := Quadlets.Exclusive_Disjunction
        (Context.Hash_State (0),
         Quadlets.Exclusive_Disjunction (V (0), V  (8)));
      Context.Hash_State (1) := Quadlets.Exclusive_Disjunction
        (Context.Hash_State (1),
         Quadlets.Exclusive_Disjunction (V (1), V  (9)));
      Context.Hash_State (2) := Quadlets.Exclusive_Disjunction
        (Context.Hash_State (2),
         Quadlets.Exclusive_Disjunction (V (2), V (10)));
      Context.Hash_State (3) := Quadlets.Exclusive_Disjunction
        (Context.Hash_State (3),
         Quadlets.Exclusive_Disjunction (V (3), V (11)));
      Context.Hash_State (4) := Quadlets.Exclusive_Disjunction
        (Context.Hash_State (4),
         Quadlets.Exclusive_Disjunction (V (4), V (12)));
      Context.Hash_State (5) := Quadlets.Exclusive_Disjunction
        (Context.Hash_State (5),
         Quadlets.Exclusive_Disjunction (V (5), V (13)));
      Context.Hash_State (6) := Quadlets.Exclusive_Disjunction
        (Context.Hash_State (6),
         Quadlets.Exclusive_Disjunction (V (6), V (14)));
      Context.Hash_State (7) := Quadlets.Exclusive_Disjunction
        (Context.Hash_State (7),
         Quadlets.Exclusive_Disjunction (V (7), V (15)));
   end Compress;

   procedure Incorporate_Flex
     (Context       : in out T;
      Message       : in     Octet_Arrays.T;
      Message_First : in     Positive;
      Message_Last  : in     Natural)
   --# pre Message_First in Message'Range and
   --#     Message_Last <= Message'Last;
   --# post Context.Digest_Length = Context~.Digest_Length;
   is
      subtype Buffer_Position_T is Natural range 0 .. 16;
      subtype Switch_T is Natural range 0 .. 3;
      Message_Index : Natural;
      Position      : Buffer_Position_T;
      Switch        : Switch_T;

      procedure Read_Quadlet
        (N : in Buffer_Index_T)
      --# global in     Message;
      --#        in out Context;
      --#        in out Message_Index;
      --# derives Context       from *,
      --#                            Message,
      --#                            Message_Index,
      --#                            N &
      --#         Message_Index from *;
      --# pre Message_Index >= Message'First - 1 and
      --#     Message_Index <= Message'Last - 4;
      --# post Context.Buffer_Index = Context~.Buffer_Index and
      --#      Context.Digest_Length = Context~.Digest_Length and
      --#      Message_Index = Message_Index~ + 4;
      is
      begin
         Message_Index := Message_Index + 1;
         Context.Input_Buffer (N) := Quadlets.T (Message (Message_Index));
         Message_Index := Message_Index + 1;
         Context.Input_Buffer (N) := Quadlets.Inclusive_Disjunction
           (Context.Input_Buffer (N),
            Quadlets.Left_Shift
              (Quadlets.T (Message (Message_Index)), 8));
         Message_Index := Message_Index + 1;
         Context.Input_Buffer (N) := Quadlets.Inclusive_Disjunction
           (Context.Input_Buffer (N),
            Quadlets.Left_Shift
              (Quadlets.T (Message (Message_Index)), 16));
         Message_Index := Message_Index + 1;
         Context.Input_Buffer (N) := Quadlets.Inclusive_Disjunction
           (Context.Input_Buffer (N),
            Quadlets.Left_Shift
              (Quadlets.T (Message (Message_Index)), 24));
      end Read_Quadlet;
      pragma Inline (Read_Quadlet);

      --  Process a block of input quickly.
      procedure Process_Block
      --# global in     Message;
      --#        in     Message_Last;
      --#        in out Context;
      --#        in out Message_Index;
      --# derives Context       from *,
      --#                            Message,
      --#                            Message_Index,
      --#                            Message_Last &
      --#         Message_Index from *,
      --#                            Message_Last;
      --# pre Message_Index >= Message'First - 1 and
      --#     Message_Last <= Message'Last;
      --# post Context.Buffer_Index = Context~.Buffer_Index and
      --#      Context.Digest_Length = Context~.Digest_Length and
      --#      (((Message_Last - Message_Index~ <= Buffer_Octets) and
      --#        (Message_Index = Message_Index~))
      --#      or
      --#       ((Message_Last - Message_Index~ > Buffer_Octets) and
      --#        (Message_Index < Message_Last))) and
      --#      Message_Index >= Message_Last - Buffer_Octets;
      is
      begin
         --  We need at least one more octet to justify calling Compress.
         while Message_Last - Message_Index > Buffer_Octets loop
            --# assert
            --#   Context.Buffer_Index = Context~.Buffer_Index and
            --#   Context.Digest_Length = Context~.Digest_Length and
            --#   Message_Last - Message_Index~ > Buffer_Octets and
            --#   Message_Last <= Message'Last and
            --#   Message_Index >= Message_Index~ and
            --#   Message_Index >= Message'First - 1 and
            --#   Message_Index < Message_Last - 64 and
            --#   Message_Index < Message'Last - 64;
            Read_Quadlet (0);
            Read_Quadlet (1);
            Read_Quadlet (2);
            Read_Quadlet (3);
            --  These extra cutpoints speed up the SPARK examiner.
            --# assert
            --#   Context.Buffer_Index = Context~.Buffer_Index and
            --#   Context.Digest_Length = Context~.Digest_Length and
            --#   Message_Last - Message_Index~ > Buffer_Octets and
            --#   Message_Last <= Message'Last and
            --#   Message_Index >= Message_Index~ and
            --#   Message_Index >= Message'First + 15 and
            --#   Message_Index < Message_Last - 48 and
            --#   Message_Index < Message'Last - 48;
            Read_Quadlet (4);
            Read_Quadlet (5);
            Read_Quadlet (6);
            Read_Quadlet (7);
            --# assert
            --#   Context.Buffer_Index = Context~.Buffer_Index and
            --#   Context.Digest_Length = Context~.Digest_Length and
            --#   Message_Last - Message_Index~ > Buffer_Octets and
            --#   Message_Last <= Message'Last and
            --#   Message_Index >= Message_Index~ and
            --#   Message_Index >= Message'First + 31 and
            --#   Message_Index < Message_Last - 32 and
            --#   Message_Index < Message'Last - 32;
            Read_Quadlet (8);
            Read_Quadlet (9);
            Read_Quadlet (10);
            Read_Quadlet (11);
            --# assert
            --#   Context.Buffer_Index = Context~.Buffer_Index and
            --#   Context.Digest_Length = Context~.Digest_Length and
            --#   Message_Last - Message_Index~ > Buffer_Octets and
            --#   Message_Last <= Message'Last and
            --#   Message_Index >= Message_Index~ and
            --#   Message_Index >= Message'First + 47 and
            --#   Message_Index < Message_Last - 16 and
            --#   Message_Index < Message'Last - 16;
            Read_Quadlet (12);
            Read_Quadlet (13);
            Read_Quadlet (14);
            Read_Quadlet (15);
            --# assert
            --#   Context.Buffer_Index = Context~.Buffer_Index and
            --#   Context.Digest_Length = Context~.Digest_Length and
            --#   Message_Last - Message_Index~ > Buffer_Octets and
            --#   Message_Last <= Message'Last and
            --#   Message_Index >= Message_Index~ and
            --#   Message_Index >= Message'First + 63 and
            --#   Message_Index < Message_Last and
            --#   Message_Index < Message'Last;

            Quadlets.Chained_Modular_Sum
              (Addend       => Buffer_Octets,
               Augend_Lower => Context.Input_Octets_Lower,
               Augend_Upper => Context.Input_Octets_Upper,
               Overflow     => Context.Overflowed);
            Compress (Initialization_Vectors (6), Context); --  Not last
         end loop;
      end Process_Block;
   begin  --  Incorporate_Flex
      Message_Index := Message_First - 1;

      if Context.Buffer_Index = Buffer_Index_T'First then
         Process_Block;
      end if;

      Position := Context.Buffer_Index / 4;
      Switch   := Context.Buffer_Index mod 4;

      while Message_Index < Message_Last loop
         --# assert
         --#   Context.Digest_Length = Context~.Digest_Length and
         --#   Message_First in Message'Range and
         --#   Message_Last <= Message'Last and
         --#   Message_Index >= Message_First - 1 and
         --#   Message_Index < Message_Last and
         --#   Message_Index < Message'Last and
         --#   Position = Context.Buffer_Index / 4 and
         --#   Switch = Context.Buffer_Index mod 4;
         if Context.Buffer_Index = Buffer_Octets then
            Quadlets.Chained_Modular_Sum
              (Addend       => Buffer_Octets,
               Augend_Lower => Context.Input_Octets_Lower,
               Augend_Upper => Context.Input_Octets_Upper,
               Overflow     => Context.Overflowed);
            Compress (Initialization_Vectors (6), Context); --  Not last
            Context.Buffer_Index := Buffer_Index_T'First;
            Process_Block;
            Position := 0;
            Switch   := 0;
            --# assert
            --#   Context.Buffer_Index = Buffer_Index_T'First and
            --#   Context.Digest_Length = Context~.Digest_Length and
            --#   Message_First in Message'Range and
            --#   Message_Last <= Message'Last and
            --#   Message_Index >= Message_First - 1 and
            --#   Message_Index < Message_Last and
            --#   Message_Index < Message'Last and
            --#   Position = 0 and Switch = 0;
         end if;
         --# assert
         --#   Context.Buffer_Index < Buffer_Octets and
         --#   Context.Digest_Length = Context~.Digest_Length and
         --#   Message_First in Message'Range and
         --#   Message_Last <= Message'Last and
         --#   Message_Index >= Message_First - 1 and
         --#   Message_Index < Message_Last and
         --#   Message_Index < Message'Last and
         --#   Message_Index + 1 <= Message'Last and
         --#   Position = Context.Buffer_Index / 4 and
         --#   Position in Buffer_Index_T and
         --#   Switch = Context.Buffer_Index mod 4;

         case Switch is
            when 0 =>
               if Message_Last - Message_Index >= 4 then
                  Read_Quadlet (Position);
                  Context.Buffer_Index := Context.Buffer_Index + 4;
                  Position             := Position + 1;
               else
                  Message_Index := Message_Index + 1;
                  Context.Input_Buffer (Position) :=
                    Quadlets.T (Message (Message_Index));
                  Context.Buffer_Index := Context.Buffer_Index + 1;
                  Switch := 1;
               end if;
            when 1 =>
               Message_Index := Message_Index + 1;
               Context.Input_Buffer (Position) :=
                 Quadlets.Inclusive_Disjunction
                 (Context.Input_Buffer (Position),
                  Quadlets.Left_Shift (Quadlets.T
                                         (Message (Message_Index)), 8));
               Context.Buffer_Index := Context.Buffer_Index + 1;
               Switch := 2;
            when 2 =>
               Message_Index := Message_Index + 1;
               Context.Input_Buffer (Position) :=
                 Quadlets.Inclusive_Disjunction
                 (Context.Input_Buffer (Position),
                  Quadlets.Left_Shift (Quadlets.T
                                         (Message (Message_Index)), 16));
               Context.Buffer_Index := Context.Buffer_Index + 1;
               Switch := 3;
            when 3 =>
               Message_Index := Message_Index + 1;
               Context.Input_Buffer (Position) :=
                 Quadlets.Inclusive_Disjunction
                 (Context.Input_Buffer (Position),
                  Quadlets.Left_Shift (Quadlets.T
                                         (Message (Message_Index)), 24));
               Context.Buffer_Index := Context.Buffer_Index + 1;
               Position := Position + 1;
               Switch   := 0;
         end case;
      end loop;
   end Incorporate_Flex;

   procedure Incorporate
     (Context : in out T;
      Message : in     Octet_Arrays.T)
   --# post Context.Digest_Length = Context~.Digest_Length;
   is
   begin
      Incorporate_Flex (Context, Message, Message'First, Message'Last);
   end Incorporate;

   function Initial
     (Digest_Length : in Digest_Index_T) return T
   --# return Context => Context.Digest_Length = Digest_Length and
   --#                   Context.Buffer_Index = 0;
   is
   begin
      return T'(Hash_State_T'
                  (0 => Quadlets.Exclusive_Disjunction
                     (Quadlets.Exclusive_Disjunction
                        (Initialization_Vectors (0), 16#01010000#),
                      Quadlets.T (Digest_Length)),
                   1 => Initialization_Vectors (1),
                   2 => Initialization_Vectors (2),
                   3 => Initialization_Vectors (3),
                   4 => Initialization_Vectors (4),
                   5 => Initialization_Vectors (5),
                   6 => Initialization_Vectors (6),
                   7 => Initialization_Vectors (7)),
                0, 0,  --  Input octets
                Quadlet_Buffer_T'(others => 0),
                Buffer_Index_T'First,
                Digest_Length,
                False);  --  Is overflowed
   end Initial;

   function Initial_Keyed_Flex
     (Digest_Length : in Digest_Index_T;
      Key           : in Key_T;
      Key_Length    : in Key_Index_T) return T
   --# pre Key_Length <= Key'Length;
   --# return Context => Context.Digest_Length = Digest_Length;
   is
      subtype Key_Position_T is Natural range 0 .. Key_Index_T'Last;
      Context       : T;
      Key_Index     : Key_Position_T;
      Key_Last      : Key_Index_T;
      Position      : Buffer_Index_T;
   begin
      Context := Initial (Digest_Length);

      Context.Hash_State (0) := Quadlets.Exclusive_Disjunction
        (Context.Hash_State (0), Quadlets.Left_Shift
           (Quadlets.T (Key_Length), 8));

      Key_Index := Key'First - 1;
      Key_Last  := Key_Index + Key_Length;
      Position  := Buffer_Index_T'First;

      while Key_Index <= Key_Last - 4 loop
         --# assert
         --#   Context.Digest_Length = Digest_Length and
         --#   Key'Length = (Key'Last - Key'First) + 1 and
         --#   Key_Length <= Key'Length and
         --#   Key_Last = (Key'First - 1) + Key_Length and
         --#   Key_Last <= Key'Last and
         --#   Key_Index >= Key'First - 1 and
         --#   Key_Index + 1 >= Key'First and
         --#   Key_Index <= Key_Last - 4 and
         --#   Key_Index + 1 <= Key'Last - 3 and
         --#   Key_Index <= Key'Last - 4 and
         --#   (Key_Index - (Key'First - 1)) mod 4 = 0 and
         --#   Position = (Key_Index - (Key'First - 1)) / 4;
         Key_Index := Key_Index + 1;
         Context.Input_Buffer (Position) := Quadlets.T (Key (Key_Index));
         Key_Index := Key_Index + 1;
         Context.Input_Buffer (Position) :=
           Quadlets.Inclusive_Disjunction
           (Context.Input_Buffer (Position),
            Quadlets.Left_Shift
              (Quadlets.T (Key (Key_Index)), 8));
         Key_Index := Key_Index + 1;
         Context.Input_Buffer (Position) :=
           Quadlets.Inclusive_Disjunction
           (Context.Input_Buffer (Position),
            Quadlets.Left_Shift
              (Quadlets.T (Key (Key_Index)), 16));
         Key_Index := Key_Index + 1;
         Context.Input_Buffer (Position) :=
           Quadlets.Inclusive_Disjunction
           (Context.Input_Buffer (Position),
            Quadlets.Left_Shift
              (Quadlets.T (Key (Key_Index)), 24));
         Position := Position + 1;
      end loop;
      --# assert
      --#   Context.Digest_Length = Digest_Length and
      --#   Key'Length = (Key'Last - Key'First) + 1 and
      --#   Key_Length <= Key'Length and
      --#   Key_Last = (Key'First - 1) + Key_Length and
      --#   Key_Last <= Key'Last and
      --#   Key_Index >= Key'First - 1 and
      --#   Key_Index > Key_Last - 4 and
      --#   Key_Index <= Key_Last and
      --#   (Key_Index - (Key'First - 1)) mod 4 = 0 and
      --#   Position = (Key_Index - (Key'First - 1)) / 4;

      if Key_Index < Key_Last then
         Key_Index := Key_Index + 1;
         --# assert
         --#   Context.Digest_Length = Digest_Length and
         --#   Key_Last <= Key'Last and
         --#   Key_Index >= Key'First and
         --#   Key_Index <= Key'Last and
         --#   (Key_Index - (Key'First - 1)) mod 4 = 1 and
         --#   Position = (Key_Index - (Key'First - 1)) / 4;
         Context.Input_Buffer (Position) := Quadlets.T (Key (Key_Index));
         if Key_Index < Key_Last then
            Key_Index := Key_Index + 1;
            --# assert
            --#   Context.Digest_Length = Digest_Length and
            --#   Key_Last <= Key'Last and
            --#   Key_Index >= Key'First + 1 and
            --#   Key_Index <= Key'Last and
            --#   (Key_Index - (Key'First - 1)) mod 4 = 2 and
            --#   Position = (Key_Index - (Key'First - 1)) / 4;
            Context.Input_Buffer (Position) :=
              Quadlets.Inclusive_Disjunction
              (Context.Input_Buffer (Position),
               Quadlets.Left_Shift (Quadlets.T (Key (Key_Index)), 8));
            if Key_Index < Key_Last then
               Key_Index := Key_Index + 1;
               --# assert
               --#   Context.Digest_Length = Digest_Length and
               --#   Key_Last <= Key'Last and
               --#   Key_Index >= Key'First + 2 and
               --#   Key_Index <= Key'Last and
               --#   (Key_Index - (Key'First - 1)) mod 4 = 3 and
               --#   Position = (Key_Index - (Key'First - 1)) / 4;
               Context.Input_Buffer (Position) :=
                 Quadlets.Inclusive_Disjunction
                 (Context.Input_Buffer (Position),
                  Quadlets.Left_Shift (Quadlets.T (Key (Key_Index)), 16));
            end if;
         end if;
      end if;

      Context.Buffer_Index := Buffer_Octets;

      return Context;
   end Initial_Keyed_Flex;

   function Initial_Keyed
     (Digest_Length : in Digest_Index_T;
      Key           : in Key_T) return T
   --# pre Key'Length >= 1;
   --# return Context =>
   --#   Context = Initial_Keyed_Flex (Digest_Length, Key, Key'Length) and
   --#   Digest_Length_Of (Context) = Digest_Length;
   is
   begin
      --  The use of defensive coding (e.g., substituting Initial when
      --  Key'Length = 0) is deliberately avoided here as it is better
      --  to raise an exception than undermine the intent of the
      --  client to use the keyed mode of BLAKE2S (which is distinct
      --  even with a null key).
      return Initial_Keyed_Flex (Digest_Length, Key, Key'Length);
   end Initial_Keyed;

   procedure Finalize
     (Context      : in out T;
      Digest       :    out Digest_T)
   --# pre Digest'First = Digest_Index_T'First and
   --#     Digest'Length >= Context.Digest_Length;
   --# post Context.Digest_Length = Context~.Digest_Length;
   is
      Digest_Index : Digest_Index_T         := Digest_Index_T'First;
      K            : Hash_State_Index_T     := Hash_State_Index_T'First;
      L            : Quadlets.Octet_Index_T := Quadlets.Octet_Index_T'First;
      Temp         : Quadlets.T;  --  Forestall a SPARK aliasing warning.
   begin
      Temp := Quadlets.T (Context.Buffer_Index);
      Quadlets.Chained_Modular_Sum
        (Addend       => Temp,
         Augend_Lower => Context.Input_Octets_Lower,
         Augend_Upper => Context.Input_Octets_Upper,
         Overflow     => Context.Overflowed);

      for I in Buffer_Index_T range
        (Context.Buffer_Index + 3) / 4 .. Context.Input_Buffer'Last
      loop
         --# assert
         --#   I in Buffer_Index_T and
         --#   Context.Digest_Length = Context~.Digest_Length and
         --#   Digest'First = Digest_Index_T'First and
         --#   Digest'Length >= Context.Digest_Length and
         --#   Digest_Index = Digest'First and
         --#   K = Hash_State_Index_T'First and
         --#   L = Quadlets.Octet_Index_T'First;
         Context.Input_Buffer (I) := 0;
      end loop;

      Compress (Quadlets.Negation (Initialization_Vectors (6)), Context);
      Digest := (others => 0);

      loop
         Digest (Digest_Index) :=
           Quadlets.Octet (Context.Hash_State (K), L);
         exit when Digest_Index = Context.Digest_Length;
         Digest_Index := Digest_Index + 1;
         L := L + 1;
         Digest (Digest_Index) :=
           Quadlets.Octet (Context.Hash_State (K), L);
         exit when Digest_Index = Context.Digest_Length;
         Digest_Index := Digest_Index + 1;
         L := L + 1;
         Digest (Digest_Index) :=
           Quadlets.Octet (Context.Hash_State (K), L);
         exit when Digest_Index = Context.Digest_Length;
         Digest_Index := Digest_Index + 1;
         L := L + 1;
         Digest (Digest_Index) :=
           Quadlets.Octet (Context.Hash_State (K), L);
         exit when Digest_Index = Context.Digest_Length;
         Digest_Index := Digest_Index + 1;
         L := Quadlets.Octet_Index_T'First;

         K := K + 1;
         --# assert
         --#   Context.Digest_Length = Context~.Digest_Length and
         --#   Digest'First = Digest_Index_T'First and
         --#   Digest'Length >= Context.Digest_Length and
         --#   Digest_Index > Digest'First and
         --#   Digest_Index <= Context.Digest_Length and
         --#   Digest_Index <= Digest'Last and
         --#   (Digest_Index - 1) mod 4 = 0 and
         --#   K = (Digest_Index - 1) / 4 and
         --#   L = Quadlets.Octet_Index_T'First;
      end loop;
   end Finalize;

   procedure Hash_Flex
     (Message       : in     Octet_Arrays.T;
      Message_First : in     Positive;
      Message_Last  : in     Natural;
      Digest_Length : in     Digest_Index_T;
      Digest        :    out Digest_T)
   is
      Context       : T;
   begin
      Context := Initial (Digest_Length);
      Incorporate_Flex (Context, Message, Message_First, Message_Last);
      pragma Assert (not Is_Overflowed (Context));
      --# accept Flow_Message, 10, Context,
      --#   "The hash state is no longer needed";
      Finalize (Context, Digest);
      --# end accept;
   end Hash_Flex;

   procedure Hash
     (Message       : in     Octet_Arrays.T;
      Digest_Length : in     Digest_Index_T;
      Digest        :    out Digest_T)
   is
   begin
      Hash_Flex (Message       => Message,
                 Message_First => Message'First,
                 Message_Last  => Message'Last,
                 Digest_Length => Digest_Length,
                 Digest        => Digest);
   end Hash;

   procedure Hash_Keyed_Flex
     (Key           : in     Key_T;
      Key_Length    : in     Key_Index_T;
      Message       : in     Octet_Arrays.T;
      Message_First : in     Positive;
      Message_Last  : in     Natural;
      Digest_Length : in     Digest_Index_T;
      Digest        :    out Digest_T)
   is
      Context       : T;
   begin
      Context := Initial_Keyed_Flex (Digest_Length, Key, Key_Length);
      --# check Context.Digest_Length = Digest_Length;
      Incorporate_Flex (Context, Message, Message_First, Message_Last);
      pragma Assert (not Is_Overflowed (Context));
      --# accept Flow_Message, 10, Context,
      --#   "The hash state is no longer needed";
      Finalize (Context, Digest);
      --# end accept;
   end Hash_Keyed_Flex;

   procedure Hash_Keyed
     (Key           : in     Key_T;
      Message       : in     Octet_Arrays.T;
      Digest_Length : in     Digest_Index_T;
      Digest        :    out Digest_T)
   is
   begin
      Hash_Keyed_Flex (Digest        => Digest,
                       Digest_Length => Digest_Length,
                       Key           => Key,
                       Key_Length    => Key'Length,
                       Message       => Message,
                       Message_First => Message'First,
                       Message_Last  => Message'Last);
   end Hash_Keyed;

   function Self_Test return Status_T
   is
      subtype Test_Buffer_Length_T is Natural range 0 .. 1024;

      subtype Test_Digest_Length_Index_T is Positive range 1 .. 4;
      type Test_Digest_Length_T is array (Test_Digest_Length_Index_T)
        of Digest_Index_T;
      Test_Digest_Length : constant Test_Digest_Length_T :=
        Test_Digest_Length_T'(16, 20, 28, 32);

      subtype Test_Input_Length_Index_T is Positive range 1 .. 6;
      type Test_Input_Length_T is
        array (Test_Input_Length_Index_T) of Test_Buffer_Length_T;
      Test_Input_Length : constant Test_Input_Length_T :=
        Test_Input_Length_T'(0, 3, 64, 65, 255, 1024);

      subtype Test_Buffer_Index_T is Test_Buffer_Length_T range 1 .. 1024;
      subtype Test_Buffer_T is Octet_Arrays.T (Test_Buffer_Index_T);

      subtype Key_Octet_Array_T is Octet_Arrays.T (Key_Index_T);
      subtype Digest_Octet_Array_T is Octet_Arrays.T (Digest_Index_T);

      Test_Result : constant Digest_Default_T := Digest_Default_T'
        (16#6A#, 16#41#, 16#1F#, 16#08#, 16#CE#, 16#25#, 16#AD#, 16#CD#,
         16#FB#, 16#02#, 16#AB#, 16#A6#, 16#41#, 16#45#, 16#1C#, 16#EC#,
         16#53#, 16#C5#, 16#98#, 16#B2#, 16#4F#, 16#4F#, 16#C7#, 16#87#,
         16#FB#, 16#DC#, 16#88#, 16#79#, 16#7F#, 16#4C#, 16#1D#, 16#FE#);

      Test_Buffer : Test_Buffer_T;
      Test_Digest : Digest_Default_T;
      Test_Key    : Key_Octet_Array_T;
      Context     : T;
      Result      : Status_T;

      procedure Self_Test_Sequences
        (Seed         : in     Quadlets.T;
         Message_Last : in     Natural;
         Message      :    out Octet_Arrays.T)
      --# derives Message from Message_Last,
      --#                      Seed;
      --# pre Message_Last <= Message'Last;
      is
         X            : Quadlets.T;
         Y            : Quadlets.T := 1;
      begin  --  Self_Test_Sequences
         X := Quadlets.Modular_Product (16#DEAD4BAD#, Seed);

         Message := (others => 0);

         for I in Positive range Message'First .. Message_Last loop
            --# assert I >= Message'First and I <= Message'Last;
            Y := Quadlets.Modular_Sum (X, Y);
            X := Quadlets.Modular_Difference (Y, X);
            Message (I) := Quadlets.Octet
              (Quadlets.Right_Shift (Y, 24),
               Quadlets.Octet_Index_T'First);
         end loop;
      end Self_Test_Sequences;
   begin  --  Self_Test
      Context := Initial (Digest_Length_Default);
      --# check Context.Digest_Length = Digest_Length_Default;

      for I in Test_Digest_Length_Index_T loop
         --# assert I in Test_Digest_Length_Index_T and
         --#        Context.Digest_Length = Digest_Length_Default;
         for J in Test_Input_Length_Index_T loop
            --# assert I in Test_Digest_Length_Index_T and
            --#        J in Test_Input_Length_Index_T and
            --#        Context.Digest_Length = Digest_Length_Default;
            Self_Test_Sequences
              (Seed         => Quadlets.T (Test_Input_Length (J)),
               Message_Last => Test_Input_Length (J),
               Message      => Test_Buffer);
            Hash_Flex
              (Message       => Test_Buffer,
               Message_First => Test_Buffer'First,
               Message_Last  => Test_Input_Length (J),
               Digest_Length => Test_Digest_Length (I),
               Digest        => Test_Digest);
            Incorporate_Flex
              (Context, Digest_Octet_Array_T (Test_Digest),
               Test_Digest'First, Test_Digest_Length (I));

            Self_Test_Sequences
              (Seed         => Quadlets.T (Test_Digest_Length (I)),
               Message_Last => Test_Digest_Length (I),
               Message      => Test_Key);
            Hash_Keyed_Flex
              (Key           => Key_Default_T (Test_Key),
               Key_Length    => Test_Digest_Length (I),
               Message       => Test_Buffer,
               Message_First => Test_Buffer'First,
               Message_Last  => Test_Input_Length (J),
               Digest_Length => Test_Digest_Length (I),
               Digest        => Test_Digest);
            Incorporate_Flex
              (Context, Digest_Octet_Array_T (Test_Digest),
               Test_Digest'First, Test_Digest_Length (I));
         end loop;
      end loop;

      --# accept Flow_Message, 10, Context,
      --#   "The hash state is no longer needed";
      Finalize (Context, Test_Digest);
      --# end accept;

      --  Although SPARK is correct to question why one would expect
      --  the result of a pure function that takes no arguments to change,
      --  the self-test is designed to flag instances, such as
      --  miscompilation or faulty memory, that could violate such
      --  assumptions.

      --# accept Flow_Message, 22,
      --#   "Check for errors outside the SPARK model.";
      case Test_Digest = Test_Result is
         when True  =>
            Result := Success;
         when False =>
            Result := Failure;
      end case;
      --# end accept;

      return Result;
   end Self_Test;

end BLAKE2S;
