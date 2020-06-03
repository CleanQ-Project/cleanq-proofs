(*
 * Copyright (c) 2020, CleanQ Project - Systems Group, ETH Zurich
 * All rights reserved.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 *
 * See "LICENSE" for details.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)



section "CleanQ Abstract List Model"

text \<open>
  We define a first refinement of the abstract model based on sets. We redefine the
  transfer sets as lists in order to get the FIFO for the transfer from X to Y and
  vice versa. We define the model of this first refinement in the the following 
  Isabelle theory: 
\<close>

theory CleanQ_ListModel
(*<*)
  imports  "../Simpl/Vcg" "CleanQ_SetModel"
(*>*)
begin

(* ==================================================================================== *)
subsection \<open>State Definition\<close>
(* ==================================================================================== *)
text \<open>
  The model is similar to the set model except the change of the transfer sets.

  \<^item> TXY: this is a list of buffers in transfer from X to Y.
  \<^item> TYX: this is a list of buffers in transfer from Y to X.
\<close>

record 'a CleanQ_List_State =
  lSX  :: "'a set"
  lSY  :: "'a set"
  lTXY :: "'a list"
  lTYX :: "'a list"

(* ==================================================================================== *)
subsection \<open>CleanQ List Model Invariants\<close>
(* ==================================================================================== *)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Images of the previously defined invariants\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>The union of all sets is constant. Image for \verb+CleanQ_List+\<close>
fun I1_img :: "'a CleanQ_List_State \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1_img rb K \<longleftrightarrow> ((lSX rb) \<union> (lSY rb) \<union> set (lTXY rb) \<union> set (lTYX rb)) = K"

text \<open>All pairwise intersections are empty. Image for \verb+CleanQ_List+.\<close>
fun I2_img :: "'a CleanQ_List_State \<Rightarrow> bool"
  where "I2_img rb \<longleftrightarrow> lSX rb \<inter> lSY rb = {} \<and> lSX rb \<inter> set (lTXY rb) = {} \<and> lSX rb \<inter> set (lTYX rb) = {} \<and> 
    lSY rb \<inter> set (lTXY rb) = {} \<and> lSY rb \<inter> set (lTYX rb) = {} \<and> 
    set (lTXY rb) \<inter> set (lTYX rb) = {}"

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I3: the elements in the transfer lists are distinct\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>This invariant is required for the move from sets to lists. In sets an element
      occurs only once while in lists it can occur multiple times. If we map the
      list which contains twice the same element, it would be mapped to only
      a single set element. In order to avoid this the elements of the lists need
     to be distinct\<close>
fun I3 :: "'a CleanQ_List_State \<Rightarrow> bool"
  where "I3 st_list \<longleftrightarrow> distinct (lTXY st_list @ lTYX st_list)"

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>CleanQ List Invariants\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We combine all invariants for the abstract CleanQ list model and define the predicate 
  \verb+CleanQ_List_Invariants+.
\<close>

fun CleanQ_List_Invariants :: "'a set \<Rightarrow> 'a CleanQ_List_State \<Rightarrow> bool"
  where "CleanQ_List_Invariants K rb \<longleftrightarrow> I1_img rb K \<and> I2_img rb \<and> I3 rb"



(* ==================================================================================== *)
subsection \<open>State Transition Operations\<close>
(* ==================================================================================== *)

text \<open>
  The two agents can, independently from each other, perform one of two operations, 
  \verb+enqueue+ and \verb+dequeue+,  which trigger an ownership transfer of buffer 
  elements.  
\<close>

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue Operation\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  The enqueue operation is analogous to the Set operations except that the elements
  are added to the end of the queue instead of simply added to the set. 
\<close>

definition CleanQ_List_enq_x :: "'a \<Rightarrow> 'a CleanQ_List_State  \<Rightarrow> 'a CleanQ_List_State"
  where "CleanQ_List_enq_x b rb = rb  \<lparr>  lSX := (lSX rb) - {b},  lTXY := (lTXY rb @ [b]) \<rparr>"

definition CleanQ_List_enq_y :: "'a \<Rightarrow> 'a CleanQ_List_State  \<Rightarrow> 'a CleanQ_List_State"
  where "CleanQ_List_enq_y b rb = rb  \<lparr>  lSY := (lSY rb) - {b},  lTYX := (lTYX rb @ [b]) \<rparr>"

text \<open>
  These definitions are the same as producing a new record:
\<close>
lemma CleanQ_List_enq_x_upd :
  "CleanQ_List_enq_x b rb = \<lparr> lSX = (lSX rb) - {b},  lSY = (lSY rb), 
                             lTXY = (lTXY rb) @ [b],  lTYX = (lTYX rb) \<rparr>"
  by(simp add:CleanQ_List_enq_x_def)

lemma CleanQ_List_enq_y_upd :
  "CleanQ_List_enq_y b rb = \<lparr> lSX = (lSX rb), lSY = (lSY rb) - {b}, 
                             lTXY = (lTXY rb), lTYX = (lTYX rb) @ [b] \<rparr>"
  by(simp add:CleanQ_List_enq_y_def)


text \<open>
  The two operations \verb+CleanQ_Set_enq_x+ and \verb+CleanQ_Set_enq_y+ transition
  the model state. Thus we need to prove that invariants I1 and I2 are preserved for
  both of them.
\<close>

lemma CleanQ_List_enq_x_I1 :
  assumes I1_holds: "I1_img rb K"  and  I2_holds: "I2_img rb"  and  X_owned: "b \<in> lSX rb"
    shows "I1_img (CleanQ_List_enq_x b rb) K"
  unfolding CleanQ_List_enq_x_def 
  using I1_holds X_owned by auto

lemma CleanQ_List_enq_y_I1 :
  assumes I1_holds: "I1_img rb K"  and  I2_holds: "I2_img rb"  and  X_owned: "b \<in> lSY rb"
    shows "I1_img (CleanQ_List_enq_y b rb) K"
  unfolding CleanQ_List_enq_y_def 
  using I1_holds X_owned by auto

lemma CleanQ_List_enq_x_I2 :
  assumes I1_holds: "I1_img rb K"  and  I2_holds: "I2_img rb"  and  X_owned: "b \<in> lSX rb"
    shows "I2_img (CleanQ_List_enq_x b rb)"
  unfolding CleanQ_List_enq_x_def
  using I2_holds X_owned by auto

lemma CleanQ_List_enq_y_I2 :
  assumes I1_holds: "I1_img rb K"  and  I2_holds: "I2_img rb"  and  X_owned: "b \<in> lSY rb"
    shows "I2_img (CleanQ_List_enq_y b rb)"
  unfolding CleanQ_List_enq_y_def
  using I2_holds X_owned by auto

lemma CleanQ_List_enq_x_I3 :
  assumes I1_holds: "I1_img rb K"  and  I2_holds: "I2_img rb" and I3_holds: "I3 rb" and  X_owned: "b \<in> lSY rb"
    shows "I3 (CleanQ_List_enq_x b rb)"
  unfolding CleanQ_List_enq_x_def
  using I1_holds I2_holds I3_holds X_owned by auto

lemma CleanQ_List_enq_y_I3 :
  assumes I1_holds: "I1_img rb K"  and  I2_holds: "I2_img rb" and I3_holds: "I3 rb" and  X_owned: "b \<in> lSY rb"
    shows "I3 (CleanQ_List_enq_y b rb)"
  unfolding CleanQ_List_enq_y_def
  using I1_holds I2_holds I3_holds X_owned by(auto)




(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  The dequeue operation is analogous to the Set operations except that the elements
  are removed from the head of the queue instead of simply removed to the set. 
\<close>

definition CleanQ_List_deq_x :: "'a \<Rightarrow> 'a CleanQ_List_State  \<Rightarrow> 'a CleanQ_List_State"
  where "CleanQ_List_deq_x b rb = \<lparr> lSX = (lSX rb) \<union> {b}, lSY = (lSY rb), lTXY = (lTXY rb),  
                                   lTYX = (remove1 b (lTYX rb)) \<rparr>"

definition CleanQ_List_deq_y :: "'a \<Rightarrow> 'a CleanQ_List_State  \<Rightarrow> 'a CleanQ_List_State"
  where "CleanQ_List_deq_y b rb = \<lparr> lSX = (lSX rb),  lSY = (lSY rb) \<union> {b}, 
                                   lTXY = (remove1 b (lTXY rb)),  lTYX = (lTYX rb) \<rparr>"


text \<open>
  These definitions are the same as producing a new record:
\<close>

lemma CleanQ_List_deq_x_upd :
  "CleanQ_List_deq_x b rb = \<lparr> lSX = (lSX rb) \<union> {b},  lSY = (lSY rb), 
                             lTXY = (lTXY rb), lTYX = remove1 b (lTYX rb) \<rparr>"
  by(simp add:CleanQ_List_deq_x_def)

lemma CleanQ_List_deq_y_upd :
  "CleanQ_List_deq_y b rb = \<lparr> lSX = (lSX rb),  lSY = (lSY rb) \<union> {b},
                             lTXY = remove1 b (lTXY rb),  lTYX = (lTYX rb) \<rparr>"
  by(simp add:CleanQ_List_deq_y_def)


end