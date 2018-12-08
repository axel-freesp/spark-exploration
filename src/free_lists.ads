pragma SPARK_Mode(On);
--with Ada.Text_IO; use Ada.Text_IO;

generic
   Capacity: Positive;

package Free_Lists is
   --Capacity: constant Positive := 10;
   subtype Pointer_Type is Natural range 0 .. Capacity;

   type Free_List_Type is private;

   procedure Initialize (List: out Free_List_Type)
     with
       Global => null,
       Post => (Is_Consistent(List));

   procedure Allocate (List: in out Free_List_Type;
                       Pointer: out Pointer_Type)
     with
       Global => null,
       Depends => ((List, Pointer) => List),
       Pre  => (Is_Consistent (List) and
                not Is_Empty (List)),
       Post => (Is_Consistent (List) and
                (Pointer /= 0 and then
                     ((for all i in 1 .. Capacity =>
                          (if i /= Pointer then
                               Is_Allocated (List, i) = Is_Allocated (List'Old, i))) and
                      Is_Allocated (List, Pointer) and
                      not Is_Allocated (List'Old, Pointer))));

   function Is_Empty  (List: in Free_List_Type) return Boolean
     with
       inline,
       Global => null;

   function Is_Consistent  (List: in Free_List_Type) return Boolean
     with
       inline,
       Global => null,
       Ghost => True;

   function Is_Allocated (List: in Free_List_Type;
                          Pointer: in Pointer_Type) return Boolean
     with
       inline,
       Global => null,
       Ghost => True;

private
   type Pointer_Array_Type is array (1 .. Capacity) of Pointer_Type;
   type Free_List_Type is
      record
         Top: Pointer_Type;
         Next: Pointer_Array_Type;
      end record;

   function Is_Empty  (List: in Free_List_Type) return Boolean is
      (List.Top = 0);

   function Is_Consistent  (List: in Free_List_Type) return Boolean is
     (for all i in 1 .. Capacity =>
        (if List.Next(i) /= 0 then
             ((List.Top /= List.Next(i)) and
              (for all j in 1 .. Capacity =>
                 (if List.Next(j) /= 0 then
                      (if i /= j then List.Next(i) /= List.Next(j)))))
         else
           (for all j in 1 .. Capacity =>
                (for all k in 1 .. Capacity =>
                     (if List.Next(j) = i and List.Next(k) = i then j = k)))));

   function Is_Allocated (List: in Free_List_Type;
                          Pointer: in Pointer_Type) return Boolean is
     (List.Top /= Pointer and
        not (for some i in 1 .. Capacity =>
            (List.Next(i) = Pointer)));

end Free_Lists;
