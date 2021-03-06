pragma SPARK_Mode(On);
with Free_Lists;

-- Validates only with --level=4.

--generic
--   type Key_Type   is private;
--   type Value_Type is private;
--   Capacity:     Positive;
--   Sentinel_Key: Key_Type;
--   Default_Value: Value_Type;
--   with function "<" (L, R: Key_Type) return Boolean is <>;
--   with procedure Put_Key   (Item: Key_Type) is <>;
--   with procedure Put_Value (Item: Value_Type) is <>;

package Trees is
   --
   subtype Key_Type   is Integer;
   subtype Value_Type is Integer;
   Capacity:     constant Positive := 10;
   Sentinel_Key: constant Key_Type := 0;
   Default_Value: constant Value_Type := Integer'First;


   type Tree_Type is private;
   --  with
   --    Type_Invariant => (Is_Consistent(Tree_Type));

   type Tree_Status_Type is (Ok, OutOfMemory);

   procedure Initialize (Tree: out Tree_Type)
     with
       Post => (Is_Consistent(Tree) and
                Is_Empty (Tree));

   procedure Insert (Tree:  in out Tree_Type;
                     Key:   in     Key_Type;
                     Value: in     Value_Type;
                     Status:   out Tree_Status_Type)
     with
       Pre  => (Is_Consistent(Tree) and
                ((Key /= Sentinel_Key) and then not Is_KeyStored(Tree, Key))),
       Post => (Is_Consistent(Tree) and
                Is_Preserving (Tree, Tree'Old) and
                (if Status = Ok then Is_Stored(Tree, Key, Value)));

   -- Ghost functions:
   function Is_Empty       (Tree: in Tree_Type) return Boolean
     with
       inline,
       Ghost => True;

   function Is_KeyStored   (Tree: in Tree_Type;
                            Key:  in Key_Type) return Boolean
     with
       inline,
       Ghost => True,
       Pre => (Key /= Sentinel_Key);

   function Is_Stored   (Tree:  in Tree_Type;
                         Key:   in Key_Type;
                         Value: in Value_Type) return Boolean
     with
       inline,
       Ghost => True,
       Pre => (Key /= Sentinel_Key);

   function Is_Consistent  (Tree: in Tree_Type) return Boolean
     with
       inline,
       Ghost => True;

   function Is_Preserving  (Tree, Old_Tree: in Tree_Type) return Boolean
     with
       inline,
       Ghost => True;

private ---------------------------------------------------------

   subtype Index_Type   is Positive range 1 .. Capacity;
   subtype Pointer_Type is Natural range 0 .. Capacity;

   type Node_Type is
      record
         Key:    Key_Type     := Sentinel_Key;
         Value:  Value_Type   := Default_Value;
         Left:   Pointer_Type := 0;
         Right:  Pointer_Type := 0;
         Parent: Pointer_Type := 0;
      end record;

   type Nodes_Type is array (Index_Type) of Node_Type;

   package my_FreeLists is new Free_Lists (Capacity => Capacity);
   use my_FreeLists;

   type Tree_Type is
      record
         Root_Node: Pointer_Type;
         Nodes:     Nodes_Type;
         Free_List: Free_List_Type;
      end record;


   function Is_Empty (Tree: in Tree_Type) return Boolean is
     (Tree.Root_Node = 0 and
        (for all i in Index_Type'Range => Tree.Nodes(i).Key = Sentinel_Key));

   function Is_KeyStored   (Tree: in Tree_Type;
                            Key:  in Key_Type) return Boolean is
     (for some i in Index_Type'Range =>
        (Tree.Nodes(i).Key = Key));

   function Is_Stored   (Tree:  in Tree_Type;
                         Key:   in Key_Type;
                         Value: in Value_Type) return Boolean is
     (for some i in Index_Type'Range =>
        (Tree.Nodes(i).Key = Key and
         Tree.Nodes(i).Value = Value));




   ----------------------------------------------------------------------------
   -- Consistency
   ----------------------------------------------------------------------------

   function Is_UsedNode (Tree: in Tree_Type;
                         Node: in Index_Type) return Boolean is
     (Tree.Nodes(Node).Key /= Sentinel_Key)
       with inline, Ghost => True;

   function Is_FreeNode (Tree: in Tree_Type;
                         Node: in Index_Type) return Boolean is
     (Tree.Nodes(Node).Key = Sentinel_Key)
       with inline, Ghost => True;

   function Node_Key_Is_Unique (Tree: in Tree_Type;
                                Node: in Index_Type) return Boolean is
     (for all j in Index_Type'Range =>
        (if Is_UsedNode(Tree, j) and j /= Node then
              Tree.Nodes(Node).Key /= Tree.Nodes(j).Key))
       with inline, Ghost => True;

   function Each_Key_Is_Unique (Tree: in Tree_Type) return Boolean is
     (for all i in Index_Type'Range =>
        (if Is_UsedNode(Tree, i) then
              Node_Key_Is_Unique (Tree, i)))
       with inline, Ghost => True;

   function Node_Is_Referenced (Tree: in Tree_Type;
                                Node: in Index_Type) return Boolean is
     (if Tree.Root_Node /= Node then
         (for some i in Index_Type'Range =>
              (Is_UsedNode(Tree, i) and
              (Tree.Nodes(i).Left = Node or
               Tree.Nodes(i).Right = Node))))
       with inline, Ghost => True;

   function Node_Is_Not_Referenced (Tree: in Tree_Type;
                                    Node: in Index_Type) return Boolean is
     (Tree.Root_Node /= Node and
      (for all i in Index_Type'Range =>
           (if Is_UsedNode(Tree, i) then
                   Tree.Nodes(i).Left /= Node and
                   Tree.Nodes(i).Right /= Node)))
       with inline, Ghost => True;

   function Node_Has_Parent (Tree: in Tree_Type;
                             Node: in Index_Type) return Boolean is
     (if Tree.Nodes(Node).Parent = 0 then
           Tree.Root_Node = Node
      else
        (for some i in Index_Type'Range =>
             (Is_UsedNode(Tree, i) and
              (Tree.Nodes(i).Left = Node or Tree.Nodes(i).Right = Node) and
              (Tree.Nodes(Node).Parent = i))))
       with inline, Ghost => True;

   function Each_Used_Node_Has_Parent (Tree: in Tree_Type) return Boolean is
     (for all i in Index_Type'Range =>
        (if Is_UsedNode(Tree, i) then
              Node_Has_Parent (Tree, i)))
       with
           inline,
           Ghost => True;

   function Node_Is_Referenced_At_Most_Once (Tree: Tree_Type;
                                             Node: Index_Type) return Boolean is
      (for all j in Index_Type'Range =>
         (if Is_UsedNode(Tree, j) then
              (for all k in Index_Type'Range =>
                   (if Is_UsedNode(Tree, k) then
                      (if (Tree.Nodes(j).Left = Node or Tree.Nodes(j).Right = Node) and
                         (Tree.Nodes(k).Left = Node or Tree.Nodes(k).Right = Node) then
                            j = k)))))
          with
            inline,
            Ghost => True;

   function Each_Used_Node_Is_Referenced_At_Most_Once (Tree: in Tree_Type) return Boolean is
     (for all i in Index_Type'Range =>
        (if Is_UsedNode(Tree, i) then
              Node_Is_Referenced_At_Most_Once (Tree, i)))
            with
           inline,
           Ghost => True;

   function Used_Nodes_Do_Not_Self_Reference (Tree: in Tree_Type) return Boolean is
     (for all i in Index_Type'Range =>
        (if Is_UsedNode(Tree, i) then
              Tree.Nodes(i).Left /= i and
              Tree.Nodes(i).Right /= i and
              Tree.Nodes(i).Parent /= i))
         with
           inline,
           Ghost => True;

   function Referenced_Nodes_Are_Used (Tree: in Tree_Type) return Boolean is
     (for all i in Index_Type'Range =>
        (if Node_Is_Referenced (Tree, i) then
                Is_UsedNode(Tree, i)))
       with
           inline,
           Ghost => True;

   function Used_Nodes_Cannot_Be_Allocated (Tree: in Tree_Type) return Boolean is
     (for all i in Index_Type'Range =>
        (if Is_UsedNode(Tree, i) then Is_Allocated (Tree.Free_List, i)))
         with
           inline,
         Ghost => True,
         Pre => (Is_Consistent (Tree.Free_List));

   function Is_UsedNodeConsistent (Tree: in Tree_Type;
                                   Node: in Index_Type) return Boolean is
     (Is_UsedNode (Tree, Node) and
      (if Tree.Nodes(Node).Parent = 0 then Node = Tree.Root_Node) and
      (if Node = Tree.Root_Node then Tree.Nodes(Node).Parent = 0))
       with
         inline,
         Ghost => True;

   function Is_Ordered (Tree: in Tree_Type) return Boolean is
     (for all i in Index_Type'Range =>
        (if Is_UsedNode (Tree, i) then
             ((if Tree.Nodes(i).Left /= 0 then Tree.Nodes(Tree.Nodes(i).Left).Key < Tree.Nodes(i).Key) and
              (if Tree.Nodes(i).Right /= 0 then Tree.Nodes(i).Key < Tree.Nodes(Tree.Nodes(i).Right).Key))))
         with
           inline,
           Ghost => True;

   function Is_Consistent  (Tree: in Tree_Type) return Boolean is
     (Is_Consistent (Tree.Free_List) and then
      (Each_Key_Is_Unique (Tree) and
      Is_Ordered (Tree) and
      Used_Nodes_Cannot_Be_Allocated (Tree) and
      Each_Used_Node_Has_Parent (Tree) and
      Each_Used_Node_Is_Referenced_At_Most_Once (Tree) and
      Used_Nodes_Do_Not_Self_Reference (Tree) and
      Referenced_Nodes_Are_Used (Tree) and
      (if Tree.Root_Node /= 0 then not Is_FreeNode (Tree, Tree.Root_Node)) and
      (if Tree.Root_Node = 0 then Is_Empty (Tree)) and
      (for all i in Index_Type'Range =>
           (if Is_UsedNode (Tree, i) then
                   Is_UsedNodeConsistent (Tree, i)))));

   function Is_Preserving  (Tree, Old_Tree: in Tree_Type) return Boolean is
     (if not Is_Empty(Old_Tree) then
          (for all i in Index_Type'Range =>
               (if Is_UsedNode(Old_Tree, i) then
                  (Is_Stored (Tree, Old_Tree.Nodes(i).Key, Old_Tree.Nodes(i).Value)))));


   procedure Lemma_Is_Consistent_FreeListConsistency (Tree: in Tree_Type)
     with
       Ghost => True,
       Pre =>  (Is_Consistent (Tree)),
       Post => (Is_Consistent (Tree.Free_List));

   procedure Lemma_Is_Consistent_Each_Key_Is_Unique (Tree: in Tree_Type)
     with
       Ghost => True,
       Pre =>  (Is_Consistent (Tree)),
       Post => (Each_Key_Is_Unique (Tree));

   procedure Lemma_Is_Consistent_Is_Ordered (Tree: in Tree_Type)
     with
       Ghost => True,
       Pre =>  (Is_Consistent (Tree)),
       Post => (Is_Ordered (Tree));

   procedure Lemma_Is_Consistent_Used_Nodes_Cannot_Be_Allocated (Tree: in Tree_Type)
     with
       Ghost => True,
       Pre =>  (Is_Consistent (Tree)),
       Post => (Used_Nodes_Cannot_Be_Allocated (Tree));

   procedure Lemma_Is_Consistent_Each_Used_Node_Has_Parent (Tree: in Tree_Type)
     with
       Ghost => True,
       Pre =>  (Is_Consistent (Tree)),
       Post => (Each_Used_Node_Has_Parent (Tree));

   procedure Lemma_Is_Consistent_Each_Used_Node_Is_Referenced_At_Most_Once (Tree: in Tree_Type)
     with
       Ghost => True,
       Pre =>  (Is_Consistent (Tree)),
       Post => (Each_Used_Node_Is_Referenced_At_Most_Once (Tree));

   procedure Lemma_Is_Consistent_Used_Nodes_Do_Not_Self_Reference (Tree: in Tree_Type)
     with
       Ghost => True,
       Pre =>  (Is_Consistent (Tree)),
       Post => (Used_Nodes_Do_Not_Self_Reference (Tree));

   procedure Lemma_Is_Consistent_Referenced_Nodes_Are_Used (Tree: in Tree_Type)
     with
       Ghost => True,
       Pre =>  (Is_Consistent (Tree)),
       Post => (Referenced_Nodes_Are_Used (Tree));


end Trees;
