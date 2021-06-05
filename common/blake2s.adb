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
   --# post Context.Digest_Length = Context~.Digest_Length;
   is
      subtype Sigma_Major_T is Natural range 0 .. 9;
      subtype Quadlet_Octet_Index_T is Octets.T range 0 .. 15;
      type Sigma_T is array (Sigma_Major_T, Quadlet_Octet_Index_T) of
        Quadlet_Octet_Index_T;
      for Sigma_T'Size use 160 * Octets.Bits;

      subtype Quadlet_Buffer_Index_T is Natural range 0 .. 15;
      type Quadlet_Buffer_T is array (Quadlet_Buffer_Index_T) of Quadlets.T;
      for Quadlet_Buffer_T'Size use
        (Quadlet_Buffer_Index_T'Last + 1) * Quadlets.Bits;

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
      M : Quadlet_Buffer_T;

      procedure Mix
        (A : in Quadlet_Buffer_Index_T;
         B : in Quadlet_Buffer_Index_T;
         C : in Quadlet_Buffer_Index_T;
         D : in Quadlet_Buffer_Index_T;
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
         V (D) := Quadlets.Right_Rotation
                    (Quadlets.Exclusive_Disjunction (V (D), V (A)), 16);
         V (C) := Quadlets.Modular_Sum (V (C), V (D));
         V (B) := Quadlets.Right_Rotation
                    (Quadlets.Exclusive_Disjunction (V (B), V (C)), 12);
         V (A) := Quadlets.Modular_Sum
                    (V (A), Quadlets.Modular_Sum (V (B), Y));
         V (D) := Quadlets.Right_Rotation
                    (Quadlets.Exclusive_Disjunction (V (D), V (A)), 8);
         V (C) := Quadlets.Modular_Sum (V (C), V (D));
         V (B) := Quadlets.Right_Rotation
                    (Quadlets.Exclusive_Disjunction (V (B), V (C)), 7);
      end Mix;
      pragma Inline (Mix);

      procedure Round (N : in Sigma_Major_T)
      --# global in     M;
      --#        in out V;
      --# derives V from *,
      --#                M,
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
              X => M (Natural (Sigma (N,  0))),
              Y => M (Natural (Sigma (N,  1))));
         Mix (A => 1, B => 5, C =>  9, D => 13,
              X => M (Natural (Sigma (N,  2))),
              Y => M (Natural (Sigma (N,  3))));
         Mix (A => 2, B => 6, C => 10, D => 14,
              X => M (Natural (Sigma (N,  4))),
              Y => M (Natural (Sigma (N,  5))));
         Mix (A => 3, B => 7, C => 11, D => 15,
              X => M (Natural (Sigma (N,  6))),
              Y => M (Natural (Sigma (N,  7))));
         Mix (A => 0, B => 5, C => 10, D => 15,
              X => M (Natural (Sigma (N,  8))),
              Y => M (Natural (Sigma (N,  9))));
         Mix (A => 1, B => 6, C => 11, D => 12,
              X => M (Natural (Sigma (N, 10))),
              Y => M (Natural (Sigma (N, 11))));
         Mix (A => 2, B => 7, C =>  8, D => 13,
              X => M (Natural (Sigma (N, 12))),
              Y => M (Natural (Sigma (N, 13))));
         Mix (A => 3, B => 4, C =>  9, D => 14,
              X => M (Natural (Sigma (N, 14))),
              Y => M (Natural (Sigma (N, 15))));
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

      M := Quadlet_Buffer_T'
        (0 => Quadlets.Concatenation
           (Context.Input_Buffer (0),  Context.Input_Buffer (1),
            Context.Input_Buffer (2),  Context.Input_Buffer (3)),
         1 => Quadlets.Concatenation
           (Context.Input_Buffer (4),  Context.Input_Buffer (5),
            Context.Input_Buffer (6),  Context.Input_Buffer (7)),
         2 => Quadlets.Concatenation
           (Context.Input_Buffer (8),  Context.Input_Buffer (9),
            Context.Input_Buffer (10), Context.Input_Buffer (11)),
         3 => Quadlets.Concatenation
           (Context.Input_Buffer (12), Context.Input_Buffer (13),
            Context.Input_Buffer (14), Context.Input_Buffer (15)),
         4 => Quadlets.Concatenation
           (Context.Input_Buffer (16), Context.Input_Buffer (17),
            Context.Input_Buffer (18), Context.Input_Buffer (19)),
         5 => Quadlets.Concatenation
           (Context.Input_Buffer (20), Context.Input_Buffer (21),
            Context.Input_Buffer (22), Context.Input_Buffer (23)),
         6 => Quadlets.Concatenation
           (Context.Input_Buffer (24), Context.Input_Buffer (25),
            Context.Input_Buffer (26), Context.Input_Buffer (27)),
         7 => Quadlets.Concatenation
           (Context.Input_Buffer (28), Context.Input_Buffer (29),
            Context.Input_Buffer (30), Context.Input_Buffer (31)),
         8 => Quadlets.Concatenation
           (Context.Input_Buffer (32), Context.Input_Buffer (33),
            Context.Input_Buffer (34), Context.Input_Buffer (35)),
         9 => Quadlets.Concatenation
           (Context.Input_Buffer (36), Context.Input_Buffer (37),
            Context.Input_Buffer (38), Context.Input_Buffer (39)),
         10 => Quadlets.Concatenation
           (Context.Input_Buffer (40), Context.Input_Buffer (41),
            Context.Input_Buffer (42), Context.Input_Buffer (43)),
         11 => Quadlets.Concatenation
           (Context.Input_Buffer (44), Context.Input_Buffer (45),
            Context.Input_Buffer (46), Context.Input_Buffer (47)),
         12 => Quadlets.Concatenation
           (Context.Input_Buffer (48), Context.Input_Buffer (49),
            Context.Input_Buffer (50), Context.Input_Buffer (51)),
         13 => Quadlets.Concatenation
           (Context.Input_Buffer (52), Context.Input_Buffer (53),
            Context.Input_Buffer (54), Context.Input_Buffer (55)),
         14 => Quadlets.Concatenation
           (Context.Input_Buffer (56), Context.Input_Buffer (57),
            Context.Input_Buffer (58), Context.Input_Buffer (59)),
         15 => Quadlets.Concatenation
           (Context.Input_Buffer (60), Context.Input_Buffer (61),
            Context.Input_Buffer (62), Context.Input_Buffer (63)));

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
   begin
      for I in Positive range Message_First .. Message_Last loop
         --# assert
         --#   Context.Digest_Length = Context~.Digest_Length and
         --#   Message_First in Message'Range and
         --#   Message_Last <= Message'Last and
         --#   I >= Message_First and I <= Message_Last;
         if Context.Buffer_Index > Context.Input_Buffer'Last then
            Quadlets.Chained_Modular_Sum
              (Addend       => Buffer_Octets,
               Augend_Lower => Context.Input_Octets_Lower,
               Augend_Upper => Context.Input_Octets_Upper,
               Overflow     => Context.Overflowed);
            Compress (Initialization_Vectors (6), Context);  --  Not last
            Context.Buffer_Index := Buffer_Index_T'First;
         end if;
         Context.Input_Buffer (Context.Buffer_Index) := Message (I);
         Context.Buffer_Index := Context.Buffer_Index + 1;
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
      Context       : T;
   begin
      Context := T'(Initialization_Vectors,  --  Hash state
                    0, 0,  --  Input octets
                    Buffer_T'(others => 0),
                    Buffer_Index_T'First,
                    Digest_Length,
                    False);  --  Is overflowed

      Context.Hash_State (0) := Quadlets.Exclusive_Disjunction
        (Quadlets.Exclusive_Disjunction
           (Context.Hash_State (0), 16#01010000#),
            Quadlets.T (Digest_Length));

      return Context;
   end Initial;

   function Initial_Keyed_Flex
     (Digest_Length : in Digest_Index_T;
      Key           : in Key_T;
      Key_Length    : in Key_Index_T) return T
   --# pre Key_Length <= Key'Length;
   --# return Context => Context.Digest_Length = Digest_Length;
   is
      Context       : T;
      I             : Key_Index_T;
   begin
      Context := Initial (Digest_Length);

      Context.Hash_State (0) := Quadlets.Exclusive_Disjunction
        (Context.Hash_State (0), Quadlets.Left_Shift
           (Quadlets.T (Key_Length), 8));

      I := Key'First;
      loop
         --# assert
         --#  Key_Length <= Key'Length and
         --#  (Key'First + Key_Length - 1) <= Key'Last and
         --#  I >= Key'First and I <= (Key'First + Key_Length) - 1 and
         --#  Context.Buffer_Index = I - Key'First and
         --#  Context.Digest_Length = Digest_Length;
         Context.Input_Buffer (Context.Buffer_Index) := Key (I);

         if I = (Key'First + Key_Length) - 1 then
            --  A for loop is avoided to resolve a dead path when
            --  Buffer_Index is incremented only to be set herein.
            Context.Buffer_Index := Buffer_Index_T'Last + 1;
            exit;
         end if;

         I := I + 1;
         Context.Buffer_Index := Context.Buffer_Index + 1;
      end loop;

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

      for I in Natural range
        Context.Buffer_Index .. Context.Input_Buffer'Last
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
