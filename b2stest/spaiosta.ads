-----------------------------------------------------------------------
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
--  File:          spaiosta.ads (Ada Package Specification)          --
--  Language:      SPARK83 [1] subset of Ada (1987) [2]              --
--  Author:        Lev Kujawski                                      --
--  Description:   Ada Text_IO binding for SPARK83                   --
--                                                                   --
--  References:                                                      --
--  [1] SPARK Team, SPARK83 - The SPADE Ada83 Kernel,                --
--      Altran Praxis, 17 Oct. 2011.                                 --
--  [2] Programming languages - Ada, ISO/IEC 8652:1987,              --
--      15 Jun. 1987.                                                --
-----------------------------------------------------------------------

with SPARK_IO;

pragma Elaborate_All (SPARK_IO);

--# inherit SPARK_IO;
package SPARK_IO_Standard
--# own Input,
--#     Output;
--# initializes Input,
--#             Output;
is
   --# accept Warning_Message, 407, "Elaborate_Body given";
   pragma Elaborate_Body;

   Input  : SPARK_IO.File_T;
   Output : SPARK_IO.File_T;

end SPARK_IO_Standard;
