pragma SPARK_Mode(On);
--with Ada.Text_IO; use Ada.Text_IO;

package body Trees is
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
            Ghost => True,
            Pre =>  (Is_Consistent_Except (Tree, Node));

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
        (Is_Consistent (Tree.Free_List) and then
         (Each_Key_Is_Unique (Tree) and
         Is_Ordered_Except (Tree, Node) and
         Used_Nodes_Cannot_Be_Allocated (Tree) and
         Each_Used_Node_Except_Has_Parent (Tree, Node) and
         Each_Used_Node_Is_Referenced_At_Most_Once (Tree) and
         Node_Is_Not_Referenced (Tree, Node) and
         Used_Nodes_Except_Do_Not_Self_Reference (Tree, Node) and
         Referenced_Nodes_Except_Are_Used (Tree, Node) and
         (if Tree.Root_Node /= 0 then not Is_FreeNode (Tree, Tree.Root_Node)) and
         (for all i in Index_Type'Range =>
              (if Is_UsedNode (Tree, i) and i /= Node then
                      Is_UsedNodeConsistent (Tree, i)))))
          with
            inline,
            Ghost => True;

   procedure Insert_Node (Tree: in out Tree_Type;
                          Node: in     Index_Type)
        with
          Pre => (Is_Consistent_Except(Tree, Node) and
                  Tree.Root_Node /= 0 and
                  Is_UsedNode (Tree, Node) and
                  Node_Is_Isolated (Tree, Node)),
          Post => (Is_Consistent(Tree) and
                   Is_Preserving (Tree, Tree'Old) and
                   Is_Stored(Tree, Tree.Nodes(Node).Key, Tree.Nodes(Node).Value) and
                   Tree.Nodes(Node).Key = Tree'Old.Nodes(Node).Key and
                   Tree.Nodes(Node).Value = Tree'Old.Nodes(Node).Value)
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
         Status := OutOfMemory;
      else
         pragma Assert (Is_Consistent(Tree));

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
         pragma Assert (Is_KeyStored(Tree, Key));
         pragma Assert (Is_Preserving (Tree, Old_Tree));
         Status := Ok;
      end if;
      pragma Assert (Is_Preserving (Tree, Old_Tree));

   end Insert;


end Trees;
