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
