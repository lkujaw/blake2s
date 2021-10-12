-----------------------------------------------------------------------
--  Copyright 2012 Altran Praxis Limited                             --
--  Copyright 2021 Lev Kujawski                                      --
--                                                                   --
--                  This file is part of B2STEST.                    --
--                                                                   --
--     B2STEST is free software: you can redistribute it and/or      --
--  modify it under the terms of the GNU General Public License as   --
--  published by the Free Software Foundation, either version 3 of   --
--       the License, or (at your option) any later version.         --
--                                                                   --
--    B2STEST is distributed in the hope that it will be useful,     --
--  but WITHOUT ANY WARRANTY; without even the implied warranty of   --
--  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the    --
--           GNU General Public License for more details.            --
--                                                                   --
--              You should have received a copy of the               --
--          GNU General Public License along with B2STEST.           --
--           If not, see <https://www.gnu.org/licenses/>.            --
--                                                                   --
--  SPDX-License-Identifier: GPL-3.0-or-later                        --
--                                                                   --
--  File:          spark_io.ads (Ada Package Specification)          --
--  Language:      SPARK83 [1] subset of Ada (1987) [2]              --
--  Description:   Ada Text_IO binding for SPARK83                   --
--                                                                   --
--  References:                                                      --
--  [1] SPARK Team, SPARK83 - The SPADE Ada83 Kernel,                --
--      Altran Praxis, 17 Oct. 2011.                                 --
--  [2] Programming languages - Ada, ISO/IEC 8652:1987,              --
--      15 Jun. 1987.                                                --
-----------------------------------------------------------------------

with Text_IO;

package SPARK_IO
--# own Inputs  : Inputs_Type;
--#     Outputs : Outputs_Type;
--#     State   : State_Type;
--# initializes Inputs,
--#             Outputs,
--#             State;
is
   --# type State_Type is abstract;
   --# type Inputs_Type is abstract;
   --# type Outputs_Type is abstract;

   type File_T is limited private;

   type File_Mode_T is (In_File, Out_File);

   --  From the Ada 83 Language Reference Manual:
   type File_Status_T is
     (Success, Status_Error, Mode_Error, Name_Error, Use_Error,
      Device_Error, End_Error, Data_Error, Layout_Error,
      Standard_Storage_Error, Standard_Program_Error);

   subtype Number_Base_T is Positive range 2 .. 16;

   function End_Of_File
     (File : in File_T)
      return Boolean;
   --# global Inputs;

   procedure Standard_Input
     (File : out File_T);
   --# global in out State;
   --# derives File,
   --#         State from State;

   procedure Standard_Output
     (File : out File_T);
   --# global in out State;
   --# derives File,
   --#         State from State;

   --! rule off Parameter_Rule
   procedure Open
     (File      :    out File_T;
      File_Mode : in     File_Mode_T;
      File_Name : in     String;
      File_Form : in     String;
      Status    :    out File_Status_T);
   --! rule on Parameter_Rule
   --# global in out State;
   --# derives File,
   --#         State,
   --#         Status from File_Form,
   --#                     File_Mode,
   --#                     File_Name,
   --#                     State;

   procedure Close
     (File   : in out File_T;
      Status :    out File_Status_T);
   --# global in out State;
   --# derives File,
   --#         State,
   --#         Status from File,
   --#                     State;

   procedure New_Line
     (File    : in File_T;
      Spacing : in Positive);
   --# global in out Outputs;
   --# derives Outputs from *,
   --#                      File,
   --#                      Spacing;

   procedure Put_String
     (File : in File_T;
      Item : in String;
      Stop : in Natural);
   --# global in out Outputs;
   --# derives Outputs from *,
   --#                      File,
   --#                      Item,
   --#                      Stop;

   procedure Get_Line
     (File : in     File_T;
      Item :    out String;
      Stop :    out Natural);
   --# global in out Inputs;
   --# derives Inputs,
   --#         Item,
   --#         Stop   from File,
   --#                     Inputs;
   --# post Stop <= Item'Last;

   procedure Put_Line
     (File : in File_T;
      Item : in String;
      Stop : in Natural);
   --# global in out Outputs;
   --# derives Outputs from *,
   --#                      File,
   --#                      Item,
   --#                      Stop;

   procedure Put_Integer
     (File  : in File_T;
      Item  : in Integer;
      Width : in Natural;
      Base  : in Number_Base_T);
   --# global in out Outputs;
   --# derives Outputs from *,
   --#                      Base,
   --#                      File,
   --#                      Item,
   --#                      Width;

private
   --# hide SPARK_IO;

   type Kind_T is (Empty, Input_Stream, Output_Stream, Regular_File);

   type File_T is
      record
         Kind   : Kind_T := Empty;
         Actual : Text_IO.File_Type;
      end record;

end SPARK_IO;
