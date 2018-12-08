pragma SPARK_Mode(On);
--with Ada.Text_IO; use Ada.Text_IO;

package body Free_Lists is

   procedure Initialize (List: out Free_List_Type) is
   begin
      List.Top := 1;
      List.Next := (others => 0);
      for i in 1 .. Capacity - 1 loop
         List.Next(i) := i + 1;
      end loop;
      List.Next(Capacity) := 0;
   end Initialize;

   procedure Allocate (List: in out Free_List_Type;
                       Pointer: out Pointer_Type) is
   begin
      Pointer := List.Top;
      List.Top := List.Next(Pointer);
      List.Next(Pointer) := 0;
   end Allocate;




end Free_Lists;
