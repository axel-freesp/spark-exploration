pragma SPARK_Mode(On);
--with Ada.Text_IO; use Ada.Text_IO;

package body Trees is

   function Is_Ancestor_Of (Tree:     in Tree_Type;
                            Node:     in Index_Type;
                            Ancestor: in Index_Type) return Boolean
   is
      N: Pointer_Type := Node;
   begin
      pragma Assert (N /= 0);
      while N /= Tree.Root_Node loop
         pragma Loop_Invariant (N /= Tree.Root_Node);
         pragma Loop_Invariant (Is_Consistent (Tree));
         pragma Loop_Invariant (N /= 0);
         pragma Loop_Invariant (Is_UsedNode (Tree, N));
         if Tree.Nodes(N).Parent = Ancestor then
            return True;
         end if;
         pragma Assert (N /= Tree.Root_Node);
         pragma Assert (Tree.Nodes(N).Parent /= 0);
         pragma Assert (Is_UsedNode (Tree, N));
         N := Tree.Nodes(N).Parent;
      end loop;
      return False;
   end Is_Ancestor_Of;

   ----------------------------------------------------------------------------
   -- Initialize
   ----------------------------------------------------------------------------
   procedure Initialize (Tree: out Tree_Type) is
   begin
      Tree.Root_Node := 0;
      Initialize (Tree.Free_List);
      Tree.Nodes     := (others => (Key => Sentinel_Key,
                                    Value => Default_Value,
                                    Left => 0,
                                    Right => 0,
                                    Parent => 0));
   end Initialize;

   ----------------------------------------------------------------------------
   -- Insert
   ----------------------------------------------------------------------------
   procedure Insert (Tree:  in out Tree_Type;
                     Key:   in     Key_Type;
                     Value: in     Value_Type;
                     Status:   out Tree_Status_Type) is
      Node: Pointer_Type;
      Old_Tree: Tree_Type := Tree with Ghost => True;

      function Node_Is_Isolated (Tree: in Tree_Type;
                                 Node: in Index_Type) return Boolean is
        (Tree.Nodes(Node).Key /= Sentinel_Key and
            Tree.Nodes(Node).Left = 0 and
            Tree.Nodes(Node).Right = 0 and
            Tree.Nodes(Node).Parent = 0 and
            Tree.Root_Node /= Node and
            Node_Is_Not_Referenced (Tree, Node))
          with
            inline,
            Ghost => True;

      function Each_Used_Node_Except_Has_Parent (Tree: in Tree_Type;
                                                 Node: in Index_Type) return Boolean is
        (for all i in Index_Type'Range =>
           (if Is_UsedNode(Tree, i) and i /= Node then
              Node_Has_Parent (Tree, i)))
          with
            inline,
            Ghost => True;

      function Used_Nodes_Except_Do_Not_Self_Reference (Tree: in Tree_Type;
                                                        Node: in Index_Type) return Boolean is
        (for all i in Index_Type'Range =>
           (if Is_UsedNode(Tree, i) and i /= Node then
                 Tree.Nodes(i).Left /= i and
                 Tree.Nodes(i).Right /= i and
                 Tree.Nodes(i).Parent /= i))
          with
           inline,
           Ghost => True;

      function Referenced_Nodes_Except_Are_Used (Tree: in Tree_Type;
                                                 Node: in Index_Type) return Boolean is
        (for all i in Index_Type'Range =>
           (if Node_Is_Referenced (Tree, i) and i /= Node then
                Is_UsedNode(Tree, i)))
         with
           inline,
           Ghost => True;

      function Used_Nodes_Except_Cannot_Be_Allocated (Tree: in Tree_Type;
                                                      Node: in Index_Type) return Boolean is
        (for all i in Index_Type'Range =>
           (if Is_UsedNode(Tree, i) and i /= Node then Is_Allocated (Tree.Free_List, i)))
         with
           inline,
           Ghost => True;

      function Is_Ordered_Except (Tree: in Tree_Type;
                                  Node: in Index_Type) return Boolean is
        (for all i in Index_Type'Range =>
           (if Is_UsedNode (Tree, i) and i /= Node then
                ((if Tree.Nodes(i).Left /= 0 then Tree.Nodes(Tree.Nodes(i).Left).Key < Tree.Nodes(i).Key) and
                 (if Tree.Nodes(i).Right /= 0 then Tree.Nodes(i).Key < Tree.Nodes(Tree.Nodes(i).Right).Key))))
         with
           inline,
           Ghost => True;

      function Is_Consistent_Except (Tree: in Tree_Type;
                                     Node: in Index_Type) return Boolean is
        (Is_Consistent (Tree.Free_List) and
         Each_Key_Is_Unique (Tree) and
         Is_Ordered_Except (Tree, Node) and
         Used_Nodes_Cannot_Be_Allocated (Tree) and
         Each_Used_Node_Except_Has_Parent (Tree, Node) and
         Each_Used_Node_Is_Referenced_At_Most_Once (Tree) and
         Node_Is_Not_Referenced (Tree, Node) and
         Used_Nodes_Except_Do_Not_Self_Reference (Tree, Node) and
         Referenced_Nodes_Except_Are_Used (Tree, Node) and
         (if Tree.Root_Node /= 0 then not Is_FreeNode (Tree, Tree.Root_Node)) and
         not Is_Empty (Tree) and
         (for all i in Index_Type'Range =>
              (if Is_UsedNode (Tree, i) and i /= Node then
                      Is_UsedNodeConsistent (Tree, i))))
          with
            inline,
            Ghost => True;

      function Is_Ancestor_Of_Internal (Tree:     in Tree_Type;
                                        Node:     in Index_Type;
                                        Ancestor: in Index_Type;
                                        Excl:     in Index_Type) return Boolean
        with
          Ghost => True,
          Pre => (Is_Consistent_Except (Tree, Excl) and
                  Is_UsedNode (Tree, Node) and
                  Is_UsedNode (Tree, Ancestor) and
                  Excl /= Node and
                  Excl /= Ancestor)
      is
         N: Pointer_Type := Node;
      begin
         pragma Assert (N /= 0);
         while N /= Tree.Root_Node loop
            pragma Loop_Invariant (N /= Tree.Root_Node);
            pragma Loop_Invariant (Is_Consistent_Except (Tree, Excl));
            pragma Loop_Invariant (N /= 0);
            pragma Loop_Invariant (N /= Excl);
            pragma Loop_Invariant (Is_UsedNode (Tree, N));
            if Tree.Nodes(N).Parent = Ancestor then
               return True;
            end if;
            if Tree.Nodes(N).Parent = Excl then
               return False;
            end if;
            pragma Assert (N /= Tree.Root_Node);
            pragma Assert (Tree.Nodes(N).Parent /= 0);
            pragma Assert (Tree.Nodes(N).Parent /= Excl);
            pragma Assert (Is_UsedNode (Tree, N));
            N := Tree.Nodes(N).Parent;
         end loop;
      return False;
   end Is_Ancestor_Of_Internal;

   function All_Used_Nodes_Except_Are_In_Tree (Tree: in Tree_Type;
                                               Node: in Index_Type) return Boolean is
        (if Tree.Root_Node /= 0 then
            (for all i in Index_Type'Range =>
                 (if Is_UsedNode (Tree, i) and i /= Node then
                         Is_Ancestor_Of_Internal (Tree, i, Tree.Root_Node, Node))))
       with
         inline,
         Ghost => True,
         Pre => (Is_Consistent_Except(Tree, Node));

   procedure Insert_Node (Tree: in out Tree_Type;
                          Node: in     Index_Type)
        with
          Pre => (Is_Consistent_Except(Tree, Node) and then
                  All_Used_Nodes_Except_Are_In_Tree (Tree, Node) and then
                  Tree.Root_Node /= 0 and then
                  Is_UsedNode (Tree, Node) and then
                  Node_Is_Isolated (Tree, Node)),
          Post => (Is_Consistent(Tree) and then
                   Is_Preserving (Tree, Tree'Old) and then
                   Is_Stored(Tree, Tree.Nodes(Node).Key, Tree.Nodes(Node).Value) and then
                   Tree.Nodes(Node).Key = Tree'Old.Nodes(Node).Key and then
                   Tree.Nodes(Node).Value = Tree'Old.Nodes(Node).Value and then
                   All_Used_Nodes_Are_In_Tree (Tree))
        is
         Parent: Pointer_Type := Tree.Root_Node;
         Old_Tree: Tree_Type := Tree with Ghost => True;
      begin
         while TRUE loop
            pragma Loop_Invariant (Parent /= 0);
            pragma Loop_Invariant (Is_UsedNode(Tree, Node));
            pragma Loop_Invariant (Is_UsedNode(Tree, Parent));
            pragma Loop_Invariant (Parent /= Tree.Nodes(Parent).Left);
            pragma Loop_Invariant (Parent /= Tree.Nodes(Parent).Right);
            pragma Loop_Invariant (Node /= Parent);
            pragma Loop_Invariant (Tree.Nodes(Node).Key /= Tree.Nodes(Parent).Key);
            pragma Loop_Invariant (Tree = Old_Tree);

            -- pre-conditions
            pragma Loop_Invariant (Is_Consistent (Tree.Free_List));
            pragma Loop_Invariant (Each_Key_Is_Unique (Tree));
            pragma Loop_Invariant (Is_Ordered_Except (Tree, Node));
            pragma Loop_Invariant (Used_Nodes_Cannot_Be_Allocated (Tree));
            pragma Loop_Invariant (Each_Used_Node_Except_Has_Parent (Tree, Node));
            pragma Loop_Invariant (Each_Used_Node_Is_Referenced_At_Most_Once (Tree));
            pragma Loop_Invariant (Node_Is_Not_Referenced (Tree, Node));
            pragma Loop_Invariant (Used_Nodes_Except_Do_Not_Self_Reference (Tree, Node));
            pragma Loop_Invariant (Referenced_Nodes_Except_Are_Used (Tree, Node));
            pragma Loop_Invariant (if Tree.Root_Node /= 0 then not Is_FreeNode (Tree, Tree.Root_Node));
            pragma Loop_Invariant (for all i in Index_Type'Range =>
                                     (if Is_UsedNode (Tree, i) and i /= Node then
                                           Is_UsedNodeConsistent (Tree, i)));
            pragma Loop_Invariant (Is_Consistent_Except (Tree, Node));
            pragma Loop_Invariant (All_Used_Nodes_Except_Are_In_Tree (Tree, Node));

            if Tree.Nodes(Node).Key < Tree.Nodes(Parent).Key then
               if Tree.Nodes(Parent).Left = 0 then
                  pragma Assert (Tree = Old_Tree);
                  pragma Assert (for all i in Index_Type'Range =>
                                   (if Is_UsedNode(Old_Tree, i) then
                                        (Is_Stored (Tree, Old_Tree.Nodes(i).Key, Old_Tree.Nodes(i).Value))));
                  pragma Assert (Referenced_Nodes_Except_Are_Used (Tree, Node));
                  pragma Assert (Node_Is_Not_Referenced (Tree, Node) and then
                                 Is_UsedNode (Tree, Node));
                  pragma Assert (Node_Is_Referenced (Tree, Parent) and then
                                 Is_UsedNode (Tree, Parent));
                  pragma Assert (Each_Used_Node_Except_Has_Parent (Tree, Node));
                  pragma Assert (Each_Used_Node_Is_Referenced_At_Most_Once (Tree));
                  pragma Assert (All_Used_Nodes_Except_Are_In_Tree (Tree, Node));

                  Tree.Nodes(Parent).Left := Node;
                  Tree.Nodes(Node).Parent := Parent;

                  pragma Assert (for all i in Index_Type'Range =>
                                   (if Is_UsedNode(Tree, i) and i /= Node and i /= Parent then
                                         Tree.Nodes(i) = Old_Tree.Nodes(i)));
                  pragma Assert (Is_KeyStored(Tree, Tree.Nodes(Node).Key));
                  pragma Assert (Node_Is_Referenced_At_Most_Once (Tree, Node));
                  pragma Assert (Node_Is_Referenced_At_Most_Once (Tree, Parent));
                  pragma Assert (Tree.Nodes(Node).Left = 0 and Tree.Nodes(Node).Right = 0);
                  pragma Assert (for all i in Index_Type'Range =>
                                   (if Is_UsedNode(Tree, i) and i /= Node and i /= Parent then
                                         Node_Is_Referenced_At_Most_Once (Tree, i)));
                  pragma Assert (for all i in Index_Type'Range =>
                                   (if Is_UsedNode(Old_Tree, i) and i /= Node then
                                        (Is_Stored (Tree, Old_Tree.Nodes(i).Key, Old_Tree.Nodes(i).Value))));
                  pragma Assert (Node_Is_Referenced (Tree, Node) and then Is_UsedNode (Tree, Node));
                  pragma Assert (Node_Is_Referenced (Tree, Parent) and then Is_UsedNode (Tree, Parent));
                  pragma Assert (for all i in Index_Type'Range =>
                                   (if Node_Is_Referenced (Tree, i) and i /= Node and i /= Parent then
                                         Is_UsedNode(Tree, i)));
                  pragma Assert (Referenced_Nodes_Except_Are_Used (Tree, Node));
                  pragma Assert (Is_UsedNode (Tree, Node) and then
                                 Node_Has_Parent (Tree, Node));
                  pragma Assert (Is_UsedNode (Tree, Parent) and then
                                 Node_Has_Parent (Tree, Parent));
                  pragma Assert ((for all i in Index_Type'Range =>
                                    (if Is_UsedNode(Tree, i) and i /= Node and i /= Parent then
                                          Node_Has_Parent (Tree, i))));
                  -- assert consistency
                  pragma Assert (Is_Consistent (Tree.Free_List));
                  pragma Assert (Each_Key_Is_Unique (Tree));
                  pragma Assert (Used_Nodes_Cannot_Be_Allocated (Tree));
                  pragma Assert (Each_Used_Node_Has_Parent (Tree));
                  pragma Assert (Each_Used_Node_Is_Referenced_At_Most_Once (Tree));
                  pragma Assert (Used_Nodes_Do_Not_Self_Reference (Tree));
                  pragma Assert (Referenced_Nodes_Are_Used (Tree));
                  pragma Assert (if Tree.Root_Node /= 0 then not Is_FreeNode (Tree, Tree.Root_Node));
                  pragma Assert (if Tree.Root_Node = 0 then Is_Empty (Tree));
                  pragma Assert (for all i in Index_Type'Range =>
                                        (if Is_UsedNode (Tree, i) then
                                              Is_UsedNodeConsistent (Tree, i)));
                  pragma Assert (Is_Consistent (Tree));
                  pragma Assert (Is_Preserving (Tree, Old_Tree));
                  pragma Assert (Is_Consistent_Except (Tree, Node));
                  pragma Assert (All_Used_Nodes_Except_Are_In_Tree (Tree, Node));
                  pragma Assert (Is_Ancestor_Of (Tree, Node, Tree.Root_Node));
                  pragma Assert (All_Used_Nodes_Are_In_Tree (Tree));
                  exit;
               else
                  pragma Assert (Tree.Nodes(Parent).Left /= 0);
                  pragma Assert (Tree.Nodes(Parent).Left /= Parent);

                  Parent := Tree.Nodes(Parent).Left;
               end if;
            else
               pragma Assert (Parent /= 0 and Node /= 0);
               pragma Assert (Tree.Nodes(Parent).Key < Tree.Nodes(Node).Key);
               if Tree.Nodes(Parent).Right = 0 then
                  pragma Assert (Tree = Old_Tree);
                  pragma Assert (for all i in Index_Type'Range =>
                                   (if Is_UsedNode(Old_Tree, i) then
                                        (Is_Stored (Tree, Old_Tree.Nodes(i).Key, Old_Tree.Nodes(i).Value))));
                  pragma Assert (Referenced_Nodes_Except_Are_Used (Tree, Node));
                  pragma Assert (Node_Is_Not_Referenced (Tree, Node) and then
                                 Is_UsedNode (Tree, Node));
                  pragma Assert (Node_Is_Referenced (Tree, Parent) and then
                                 Is_UsedNode (Tree, Parent));
                  pragma Assert (Each_Used_Node_Except_Has_Parent (Tree, Node));
                  pragma Assert (Each_Used_Node_Is_Referenced_At_Most_Once (Tree));
                  pragma Assert (All_Used_Nodes_Except_Are_In_Tree (Tree, Node));

                  Tree.Nodes(Parent).Right := Node;
                  Tree.Nodes(Node).Parent := Parent;

                  pragma Assert (for all i in Index_Type'Range =>
                                   (if Is_UsedNode(Tree, i) and i /= Node and i /= Parent then
                                         Tree.Nodes(i) = Old_Tree.Nodes(i)));
                  pragma Assert (Is_KeyStored(Tree, Tree.Nodes(Node).Key));
                  pragma Assert (Node_Is_Referenced_At_Most_Once (Tree, Node));
                  pragma Assert (Node_Is_Referenced_At_Most_Once (Tree, Parent));
                  pragma Assert (Tree.Nodes(Node).Left = 0 and Tree.Nodes(Node).Right = 0);
                  pragma Assert (for all i in Index_Type'Range =>
                                   (if Is_UsedNode(Tree, i) and i /= Node and i /= Parent then
                                         Node_Is_Referenced_At_Most_Once (Tree, i)));
                  pragma Assert (for all i in Index_Type'Range =>
                                   (if Is_UsedNode(Old_Tree, i) and i /= Node then
                                        (Is_Stored (Tree, Old_Tree.Nodes(i).Key, Old_Tree.Nodes(i).Value))));
                  pragma Assert (Node_Is_Referenced (Tree, Node) and then Is_UsedNode (Tree, Node));
                  pragma Assert (Node_Is_Referenced (Tree, Parent) and then Is_UsedNode (Tree, Parent));
                  pragma Assert (for all i in Index_Type'Range =>
                                   (if Node_Is_Referenced (Tree, i) and i /= Node and i /= Parent then
                                         Is_UsedNode(Tree, i)));
                  pragma Assert (Referenced_Nodes_Except_Are_Used (Tree, Node));
                  pragma Assert (Is_UsedNode (Tree, Node) and then
                                 Node_Has_Parent (Tree, Node));
                  pragma Assert (Is_UsedNode (Tree, Parent) and then
                                 Node_Has_Parent (Tree, Parent));
                  pragma Assert ((for all i in Index_Type'Range =>
                                    (if Is_UsedNode(Tree, i) and i /= Node and i /= Parent then
                                          Node_Has_Parent (Tree, i))));
                  -- assert consistency
                  pragma Assert (Is_Consistent (Tree.Free_List));
                  pragma Assert (Each_Key_Is_Unique (Tree));
                  pragma Assert (Used_Nodes_Cannot_Be_Allocated (Tree));
                  pragma Assert (Each_Used_Node_Has_Parent (Tree));
                  pragma Assert (Each_Used_Node_Is_Referenced_At_Most_Once (Tree));
                  pragma Assert (Used_Nodes_Do_Not_Self_Reference (Tree));
                  pragma Assert (Referenced_Nodes_Are_Used (Tree));
                  pragma Assert (if Tree.Root_Node /= 0 then not Is_FreeNode (Tree, Tree.Root_Node));
                  pragma Assert (if Tree.Root_Node = 0 then Is_Empty (Tree));
                  pragma Assert (for all i in Index_Type'Range =>
                                        (if Is_UsedNode (Tree, i) then
                                              Is_UsedNodeConsistent (Tree, i)));
                  pragma Assert (Is_Consistent (Tree));
                  pragma Assert (Is_Preserving (Tree, Old_Tree));
                  pragma Assert (All_Used_Nodes_Except_Are_In_Tree (Tree, Node));
                  pragma Assert (Is_Ancestor_Of (Tree, Node, Tree.Root_Node));
                  pragma Assert (All_Used_Nodes_Are_In_Tree (Tree));
                  exit;
               else
                  pragma Assert (Tree.Nodes(Parent).Right /= 0);
                  pragma Assert (Tree.Nodes(Parent).Right /= Parent);

                  Parent := Tree.Nodes(Parent).Right;
               end if;
            end if;
         end loop;
      end Insert_Node;

      procedure Allocate_Node (Tree:  in out Tree_Type;
                               Node:     out Pointer_Type;
                               Key:   in     Key_Type;
                               Value: in     Value_Type)
        with
          Pre  => (not Is_Empty(Tree.Free_List) and
                   Is_Consistent(Tree) and
                   (Key /= Sentinel_Key and then not Is_KeyStored (Tree, Key))),
          Post => (((for all i in Index_Type'Range =>
                       (if i /= Node then
                            Tree.Nodes(i) = Tree'Old.Nodes(i))) and
                    Tree.Root_Node = Tree'Old.Root_Node and
                    Node /= 0) and then
                     (Is_UsedNode (Tree, Node) and
                      Tree.Nodes(Node).Key = Key and
                      Tree.Nodes(Node).Value = Value and
                      Node_Is_Not_Referenced (Tree, Node) and
                      Node_Is_Isolated (Tree, Node) and
                      Is_Consistent_Except(Tree, Node)))
        is
         Old_Tree: Tree_Type := Tree with Ghost => True;
      begin
         Allocate (Tree.Free_List, Node);

         pragma Assert (for all i in Index_Type'Range =>
                          Tree.Nodes(i) = Old_Tree.Nodes(i));
         pragma Assert (for all i in Index_Type'Range =>
                          (if i /= Node then
                              Is_Allocated (Tree.Free_List, i) = Is_Allocated(Old_Tree.Free_List, i)));
         pragma Assert (not Is_UsedNode (Tree, Node));
         pragma Assert (Node_Is_Not_Referenced (Tree, Node));

         pragma Assert (Is_Consistent (Tree.Free_List));
         pragma Assert (for all i in Index_Type'Range =>
                          (if i /= Node then
                              Tree.Nodes(i) = Old_Tree.Nodes(i)));
         pragma Assert ((for all i in Index_Type'Range =>
                           (if Is_UsedNode(Tree, i) then
                               Tree.Nodes(i).Left /= Node and
                               Tree.Nodes(i).Right /= Node and
                               Tree.Nodes(i).Parent /= Node)) and
                        Tree.Root_Node /= Node);

         Tree.Nodes(Node).Key    := Key;
         Tree.Nodes(Node).Value  := Value;
         Tree.Nodes(Node).Left   := 0;
         Tree.Nodes(Node).Right  := 0;
         Tree.Nodes(Node).Parent := 0;

         pragma Assert (for all i in Index_Type'Range =>
                          (if i /= Node then
                              Tree.Nodes(i) = Old_Tree.Nodes(i)));
         pragma Assert (Is_UsedNode (Tree, Node));
         pragma Assert (Tree.Nodes(Node).Left /= Node and
                        Tree.Nodes(Node).Right /= Node and
                        Tree.Nodes(Node).Parent /= Node);
         pragma Assert ((for all i in Index_Type'Range =>
                           (if Is_UsedNode(Tree, i) then
                               Tree.Nodes(i).Left /= Node and
                               Tree.Nodes(i).Right /= Node and
                               Tree.Nodes(i).Parent /= Node)) and
                        Tree.Root_Node /= Node);
         pragma Assert (Node_Is_Not_Referenced (Tree, Node));
         pragma Assert (Is_Consistent (Tree.Free_List));
         pragma Assert (for all i in Index_Type'Range =>
                          (if i /= Node then
                              Tree.Nodes(i) = Old_Tree.Nodes(i)));
         pragma Assert (Used_Nodes_Cannot_Be_Allocated (Tree));
         pragma Assert (Each_Used_Node_Except_Has_Parent (Tree, Node));
         -- This one is redundant, but needed for automatic proof:
         pragma Assert (for all i in Index_Type'Range =>
                          (if Is_UsedNode(Tree, i) and i /= Node then
                               (for all j in Index_Type'Range =>
                                    (if Is_UsedNode(Tree, j) and i /= Node then
                                       (for all k in Index_Type'Range =>
                                          (if Is_UsedNode(Tree, k) and i /= Node then
                                               (if (Tree.Nodes(j).Left = i or Tree.Nodes(j).Right = i) and
                                                    (Tree.Nodes(k).Left = i or Tree.Nodes(k).Right = i) then
                                                       j = k)))))));
         pragma Assert (Used_Nodes_Except_Do_Not_Self_Reference (Tree, Node));
         pragma Assert (for all i in Index_Type'Range =>
                          (if Node_Is_Referenced (Tree, i) and i /= Node then
                                Is_UsedNode(Tree, i)));
         pragma Assert (if Tree.Root_Node /= 0 then not Is_FreeNode (Tree, Tree.Root_Node));
         pragma Assert (for all i in Index_Type'Range =>
              (if Is_UsedNode (Tree, i) and i /= Node then
                      Is_UsedNodeConsistent (Tree, i)));
         pragma Assert (Is_Consistent_Except(Tree, Node));

      end Allocate_Node;

   begin
      pragma Assert (not Is_KeyStored(Tree, Key));
      if Is_Empty(Tree.Free_List) then
         pragma Assert (Is_Consistent(Tree));
         pragma Assert (Tree_Is_Ordered (Tree));
         Status := OutOfMemory;
      else
         pragma Assert (Is_Consistent(Tree));
         pragma Assert (Tree_Is_Ordered (Tree));

         Allocate_Node (Tree, Node, Key, Value);

         pragma Assert (Is_UsedNode (Tree, Node));
         pragma Assert (for all i in Index_Type'Range =>
                          (if i /= Node then
                              Tree.Nodes(i) = Old_Tree.Nodes(i)));
         pragma Assert (Is_Consistent_Except(Tree, Node));
         pragma Assert (Node_Is_Isolated (Tree, Node));

         if Tree.Root_Node = 0 then
            pragma Assert (Node_Is_Not_Referenced (Tree, Node));
            pragma Assert (Is_Empty(Old_Tree));

            Tree.Root_Node := Node;

            pragma Assert (Tree.Root_Node = Node);
            pragma Assert (Tree.Nodes(Tree.Root_Node).Parent = 0);
            pragma Assert (for all i in Index_Type'Range =>
                             (if Is_UsedNode(Tree, i) then
                                   Tree.Nodes(i).Left /= Node and
                                  Tree.Nodes(i).Right /= Node and
                                  Tree.Nodes(i).Parent /= Node));
            -- consistency
            pragma Assert (Is_Consistent (Tree.Free_List));
            pragma Assert (Tree_Is_Ordered (Tree));
            pragma Assert (Each_Key_Is_Unique (Tree));
            pragma Assert (Is_Ordered (Tree));
            pragma Assert (Used_Nodes_Cannot_Be_Allocated (Tree));
            pragma Assert (Each_Used_Node_Has_Parent (Tree));
            pragma Assert (Each_Used_Node_Is_Referenced_At_Most_Once (Tree));
            pragma Assert (Used_Nodes_Do_Not_Self_Reference (Tree));
            pragma Assert (Referenced_Nodes_Are_Used (Tree));
            pragma Assert (if Tree.Root_Node /= 0 then not Is_FreeNode (Tree, Tree.Root_Node));
            pragma Assert (if Tree.Root_Node = 0 then Is_Empty (Tree));
            pragma Assert (for all i in Index_Type'Range =>
                                (if Is_UsedNode (Tree, i) then
                                      Is_UsedNodeConsistent (Tree, i)));
         else
            pragma Assert (Tree.Root_Node /= 0);
            pragma Assert (Tree.Nodes(Node).Key = Key);

            Insert_Node(Tree, Node);

            pragma Assert (Tree.Nodes(Node).Key = Key);
         end if;

         pragma Assert (Is_Consistent(Tree));
         pragma Assert (Tree_Is_Ordered (Tree));
         pragma Assert (Is_KeyStored(Tree, Key));
         pragma Assert (Is_Preserving (Tree, Old_Tree));
         Status := Ok;
      end if;
      pragma Assert (Is_Preserving (Tree, Old_Tree));

   end Insert;


   ----------------------------------------------------------------------------
   function In_Order_FirstNode (Tree: in Tree_Type) return Pointer_Type
     with
       Pre => (Is_Consistent(Tree)),
       Post => (if In_Order_FirstNode'Result /= 0 then
                  (Is_KeyStored(Tree, Tree.Nodes(In_Order_FirstNode'Result).Key)
                   and Is_SmallestKey(Tree, Tree.Nodes(In_Order_FirstNode'Result).Key)))
     is
      Node: Pointer_Type := Tree.Root_Node;
   begin
      if Node /= 0 then
         while Tree.Nodes(Node).Left /= 0 loop
            pragma Loop_Invariant (Node /= 0);
            pragma Loop_Invariant (Tree.Nodes(Node).Left /= 0);
            pragma Loop_Invariant (Is_Consistent(Tree));
            pragma Loop_Invariant (Is_UsedNode(Tree, Node));
            pragma Loop_Invariant (Tree.Nodes(Tree.Nodes(Node).Left).Key < Tree.Nodes(Node).Key);
            pragma Loop_Invariant (if (for some i in Index_Type'Range =>
                                         (Tree.Nodes(i).Key < Tree.Nodes(Node).Key)) then
                                        Tree.Nodes(Node).Left /= 0);
            pragma Loop_Invariant (if Tree.Nodes(Node).Left /= 0 then
                                     (for some i in Index_Type'Range =>
                                         (Tree.Nodes(i).Key < Tree.Nodes(Node).Key)));
            pragma Loop_Invariant ((Tree.Nodes(Node).Left /= 0) =
                                     (for some i in Index_Type'Range =>
                                         (Tree.Nodes(i).Key < Tree.Nodes(Node).Key)));

            Node := Tree.Nodes(Node).Left;

            pragma Assert (Node /= 0);
            pragma Assert (Is_Consistent(Tree));
            pragma Assert (Is_UsedNode(Tree, Node));
            pragma Assert ((Tree.Nodes(Node).Left /= 0) =
                           (for some i in Index_Type'Range =>
                              (Tree.Nodes(i).Key < Tree.Nodes(Node).Key)));
         end loop;
         pragma Assert (Node /= 0);
         pragma Assert (Tree.Nodes(Node).Left = 0);
         pragma Assert (Is_Consistent(Tree));
         pragma Assert (Is_UsedNode(Tree, Node));
         pragma Assert (if (for some i in Index_Type'Range =>
                              (Tree.Nodes(i).Key < Tree.Nodes(Node).Key)) then
                             Tree.Nodes(Node).Left /= 0);
         pragma Assert ((Tree.Nodes(Node).Left /= 0) =
                        (for some i in Index_Type'Range =>
                           (Tree.Nodes(i).Key < Tree.Nodes(Node).Key)));
         pragma Assert (not (for some i in Index_Type'Range =>
                               (Tree.Nodes(i).Key < Tree.Nodes(Node).Key)));
         pragma Assert (Is_SmallestKey(Tree, Node));
      end if;
      return Node;
   end In_Order_FirstNode;

   ----------------------------------------------------------------------------
   function In_Order_First (Tree: in Tree_Type) return Key_Type is
      Node: Pointer_Type;
   begin
      Node  := In_Order_FirstNode(Tree);
      if Node = 0 then
         return Sentinel_Key;
      else
         return Tree.Nodes(Node).Key;
      end if;
   end In_Order_First;

   ----------------------------------------------------------------------------
   function Find_Node      (Tree: in Tree_Type;
                            Key:  in Key_Type) return Pointer_Type
     with
       Pre => (Is_Consistent(Tree) and Key /= Sentinel_Key),
       Post => ((if Find_Node'Result /= 0 then
                      Tree.Nodes(Find_Node'Result).Key = Key) and
                (if Find_Node'Result = 0 then
                     (not (for some i in Index_Type'Range =>
                               (Is_UsedNode(Tree, i) and
                                Tree.Nodes(i).Key = Key)))))
     is
      Node: Pointer_Type := Tree.Root_Node;
   begin
      while Node /= 0 loop
         pragma Assert (Is_Consistent(Tree) and Key /= Sentinel_Key);
         pragma Assert (Node /= 0);
         if Key < Tree.Nodes(Node).Key then
            pragma Assert (Key < Tree.Nodes(Node).Key);
            pragma Assert (if Tree.Nodes(Node).Left /= 0 then
                             (not (for some i in Index_Type'Range =>
                                       (Is_UsedNode(Tree, i) and
                                              Tree.Nodes(i).Key = Key))));
            Node := Tree.Nodes(Node).Left;
         elsif Tree.Nodes(Node).Key = Key then
            pragma Assert (Node /= 0);
            pragma Assert (Tree.Nodes(Node).Key = Key);
            exit;
         else
            pragma Assert (Tree.Nodes(Node).Key < Key);
            pragma Assert (if Tree.Nodes(Node).Right /= 0 then
                             (not (for some i in Index_Type'Range =>
                                       (Is_UsedNode(Tree, i) and
                                              Tree.Nodes(i).Key = Key))));
            Node := Tree.Nodes(Node).Right;
         end if;
         pragma Loop_Invariant (Is_Consistent(Tree) and Key /= Sentinel_Key);
      end loop;
      pragma Assert (Is_Consistent(Tree) and Key /= Sentinel_Key);
      pragma Assert (if Node /= 0 then
                        Tree.Nodes(Node).Key = Key);
      return Node;
   end Find_Node;

   ----------------------------------------------------------------------------
   function In_Order_NextNode(Tree: in Tree_Type;
                              Node: in Pointer_Type) return Pointer_Type
     with
       Pre => ((Is_Consistent(Tree) and Node /= 0) and then Is_UsedNode (Tree, Node)),
       Post => (if In_Order_NextNode'Result /= 0 then
                  (Is_KeyStored(Tree, Tree.Nodes(In_Order_NextNode'Result).Key) and
                     Tree.Nodes(Node).Key < In_Order_NextNode'Result))
     is
      This:   Pointer_Type := Node;
      Parent: Pointer_Type;
   begin
      if Tree.Nodes(This).Right = 0 then
         Parent := Tree.Nodes(This).Parent;
         if Parent = 0 then
            -- end of the traverse
            return 0;
         end if;
         pragma Assert (Parent /= 0);
         while This = Tree.Nodes(Parent).Right loop
            pragma Loop_Invariant ((Parent /= 0 and This /= 0) and then
                                     (Tree.Nodes(This).Key /= Sentinel_Key and
                                     Tree.Nodes(Parent).Key /= Sentinel_Key));
            This   := Parent;
            pragma Assert (This /= 0);
            Parent := Tree.Nodes(This).Parent;
            if Parent = 0 then
               -- end of the traverse
               return 0;
            end if;
            pragma Assert (Parent /= 0);
         end loop;
         pragma Assert (Parent /= 0 and This /= 0);
         pragma Assert (This = Tree.Nodes(Parent).Left or This = Tree.Nodes(Parent).Right);
         pragma Assert (This = Tree.Nodes(Parent).Left);
         This := Parent;
      else
         This := Tree.Nodes(This).Right;
         while Tree.Nodes(This).Left /= 0 loop
            pragma Loop_Invariant (This /= 0 and then Tree.Nodes(This).Left /= 0);
            This := Tree.Nodes(This).Left;
         end loop;
      end if;
      return This;
   end In_Order_NextNode;

   ----------------------------------------------------------------------------
   function In_Order_Next  (Tree: in Tree_Type;
                            Key:  in Key_Type) return Key_Type is
      Node: Pointer_Type;
   begin
      pragma Assert (Is_KeyStored (Tree, Key));
      Node := Find_Node (Tree, Key);
      pragma Assert (Node /= 0);
      Node := In_Order_NextNode(Tree, Node);
      If Node = 0 then
         return Sentinel_Key;
      else
         return Tree.Nodes(Node).Key;
      end if;
   end In_Order_Next;

   function Find_Key       (Tree: in Tree_Type;
                            Key:  in Key_Type) return Boolean is
   begin
      return Find_Node (Tree, Key) /= 0;
   end Find_Key;

   function Find_Value     (Tree: in Tree_Type;
                            Key:  in Key_Type) return Value_Type is
      Node: Pointer_Type;
   begin
      pragma Assert (Find_Key (Tree, Key));
      Node := Find_Node (Tree, Key);
      return Tree.Nodes(Node).Value;
   end Find_Value;

end Trees;
