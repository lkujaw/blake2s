package body SPARK_IO is
   --# hide SPARK_IO;

   function "=" (Left  : in Text_IO.File_Mode;
                 Right : in Text_IO.File_Mode) return Boolean
     renames Text_IO."=";

   package Integer_IO is new Text_IO.Integer_IO (Num => Integer);

   function Is_Input_File
     (File : in File_T) return Boolean
   is
   begin
      return File.Kind = Input_Stream or else
        (File.Kind = Regular_File and then
           Text_IO.Mode (File.Actual) = Text_IO.In_File);
   exception
      when others =>
         return False;
   end Is_Input_File;

   function Is_Output_File
     (File : in File_T) return Boolean
   is
   begin
      return File.Kind = Output_Stream or else
        (File.Kind = Regular_File and then
           Text_IO.Mode (File.Actual) = Text_IO.Out_File);
   exception
      when others =>
         return False;
   end Is_Output_File;

   function End_Of_File
     (File : in File_T) return Boolean
   is
   begin
      return not Is_Input_File (File) or else
        Text_IO.End_Of_File (File.Actual);
   exception
      when others =>
         return True;
   end End_Of_File;

   procedure Standard_Input
     (File : out File_T)
   is
   begin
      File.Kind := Input_Stream;
   end Standard_Input;

   procedure Standard_Output
     (File : out File_T)
   is
   begin
      File.Kind := Output_Stream;
   end Standard_Output;

   procedure Open
     (File      :    out File_T;
      File_Mode : in     File_Mode_T;
      File_Name : in     String;
      File_Form : in     String;
      Status    :    out File_Status_T)
   is
      Ada_Mode  : Text_IO.File_Mode;
   begin
      case File_Mode is
         when In_File  =>
            Ada_Mode := Text_IO.In_File;
         when Out_File =>
            Ada_Mode := Text_IO.Out_File;
      end case;

      Text_IO.Open (File.Actual, Ada_Mode, File_Name, File_Form);
      File.Kind := Regular_File;
      Status    := Success;
   exception
      when Text_IO.Status_Error =>
         Status := Status_Error;
      when Text_IO.Mode_Error =>
         Status := Mode_Error;
      when Text_IO.Name_Error =>
         Status := Name_Error;
      when Text_IO.Use_Error =>
         Status := Use_Error;
      when Text_IO.Device_Error =>
         Status := Device_Error;
      when Text_IO.End_Error =>
         Status := End_Error;
      when Text_IO.Data_Error =>
         Status := Data_Error;
      when Text_IO.Layout_Error =>
         Status := Layout_Error;
      when Storage_Error =>
         Status := Standard_Storage_Error;
      when others =>
         Status := Standard_Program_Error;
   end Open;

   procedure Close
     (File   : in out File_T;
      Status :    out File_Status_T)
   is
   begin
      if File.Kind = Regular_File then
         Text_IO.Close (File.Actual);
         File.Kind := Empty;
         Status    := Success;
      else
         Status := Status_Error;
      end if;
   exception
      when Text_IO.Status_Error =>
         Status := Status_Error;
      when Text_IO.Mode_Error =>
         Status := Mode_Error;
      when Text_IO.Name_Error =>
         Status := Name_Error;
      when Text_IO.Use_Error =>
         Status := Use_Error;
      when Text_IO.Device_Error =>
         Status := Device_Error;
      when Text_IO.End_Error =>
         Status := End_Error;
      when Text_IO.Data_Error =>
         Status := Data_Error;
      when Text_IO.Layout_Error =>
         Status := Layout_Error;
      when Constraint_Error =>
         Status := Use_Error;
      when Storage_Error =>
         Status := Standard_Storage_Error;
      when others =>
         Status := Standard_Program_Error;
   end Close;

   procedure New_Line
     (File    : in File_T;
      Spacing : in Positive)
   is
   begin
      case File.Kind is
         when Output_Stream =>
            Text_IO.New_Line (Text_IO.Standard_Output,
                              Text_IO.Positive_Count (Spacing));
         when Regular_File =>
            if Text_IO.Mode (File.Actual) = Text_IO.Out_File then
               Text_IO.New_Line (File.Actual,
                                 Text_IO.Positive_Count (Spacing));
            end if;
         when Empty =>
            null;
         when Input_Stream =>
            null;
      end case;
   exception
      when others =>
         null;
   end New_Line;

   procedure Put
     (File : in File_T;
      Item : in String)
   is
   begin
      if Is_Output_File (File) then
         if File.Kind = Output_Stream then
            Text_IO.Put (Text_IO.Standard_Output, Item);
         else
            Text_IO.Put (File.Actual, Item);
         end if;
      end if;
   end Put;

   procedure Put_String
     (File : in File_T;
      Item : in String;
      Stop : in Natural)
   is
   begin
      if Stop = 0 then
         Put (File, Item);
      elsif Stop <= Item'Last then
         Put (File, Item (Item'First .. Stop));
      else
         Put (File, Item);

         for I in Natural range 0 .. Stop - Item'Last loop
            Put (File, " ");
         end loop;
      end if;
   exception
      when others =>
         null;
   end Put_String;

   procedure Get_Line
     (File : in     File_T;
      Item :    out String;
      Stop :    out Natural)
   is
      Line_Stop : Natural;
   begin
      if Is_Input_File (File) then
         if File.Kind = Input_Stream then
            Text_IO.Get_Line (Text_IO.Standard_Input, Item, Line_Stop);
         else
            Text_IO.Get_Line (File.Actual, Item, Line_Stop);
         end if;

         if Line_Stop <= Item'Last then
            Stop := Line_Stop;
         else
            --  This should never occur.
            Stop := Item'Last;
         end if;
      else
         Stop := Item'First - 1;
      end if;
   exception
      when others =>
         Stop := Item'First - 1;
   end Get_Line;

   procedure Put_Line
     (File : in File_T;
      Item : in String)
   is
   begin
      if Is_Output_File (File) then
         if File.Kind = Output_Stream then
            Text_IO.Put_Line (Text_IO.Standard_Output, Item);
         else
            Text_IO.Put_Line (File.Actual, Item);
         end if;
      end if;
   end Put_Line;

   procedure Put_Line
     (File : in File_T;
      Item : in String;
      Stop : in Natural)
   is
   begin
      if Is_Output_File (File) then
         if Stop = 0 then
            Put_Line (File, Item);
         else
            Put_Line (File, Item (Item'First .. Stop));
         end if;
      end if;
   exception
      when others =>
         null;
   end Put_Line;

   procedure Put_Integer
     (File  : in File_T;
      Item  : in Integer;
      Width : in Natural;
      Base  : in Number_Base_T)
   is
   begin
      if Is_Output_File (File) then
         if File.Kind = Output_Stream then
            Integer_IO.Put (Text_IO.Standard_Output, Item, Width, Base);
         else
            Integer_IO.Put (File.Actual, Item, Width, Base);
         end if;
      end if;
   exception
      when others =>
         null;
   end Put_Integer;

end SPARK_IO;
