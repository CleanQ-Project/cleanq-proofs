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
  imports Main "../Simpl/Vcg"  "../Complx/OG_Hoare" "CleanQ_SetModel"
(*>*)
begin

(* ==================================================================================== *)
subsection \<open>State Definition\<close>
(* ==================================================================================== *)

text \<open>
  Similar to the abstract set model, We express a system with a single point-to-point 
  queue between two agents $X$ and $Y$. However, in contrast we now use lists instead
  of sets for the transfer between the two agents.  The state of the abstract CleanQ List
  model is captured in the Isabelle record \verb+CleanQ_List_State+. Like the previous
  model, we express the buffers owned by $X$ or $Y$ as sets.


  \<^item> lSX: this is the set of buffers owned by X.
  \<^item> lSY: this is the set of buffers owned by Y.
  \<^item> lTXY: this is a list of buffers in transfer from X to Y.
  \<^item> lTYX: this is a list of buffers in transfer from Y to X.
\<close>

record 'a CleanQ_List_State =
  lSX  :: "'a set"
  lSY  :: "'a set"
  lTXY :: "'a list"
  lTYX :: "'a list"

text \<open>
  Like the abstract set model,  we do not specify the representation of the buffer 
  elements. This can be a single, fixed-sized page frame, a variable-sized base-limit 
  segment, or a set of memory locations. 
\<close>

(*<*)
(* Define some global variables to make Simpl/Complex proofs work *)
record 'g CleanQ_List_State_vars = 
  ListRB_'  :: "nat CleanQ_List_State"
  ListB_'   ::  nat
(*>*)


(* ==================================================================================== *)
subsection \<open>State Lifting Function\<close>
(* ==================================================================================== *)

text \<open>
  The CleanQ List model is a data refinement of the CleanQ Set Model. We can define an
  interpretation function. That lifts the CleanQ list model state into the CleanQ
  set model state by taking the \verb+set+ of the transfer lists.
\<close>

definition CleanQ_List2Set :: "'a CleanQ_List_State  \<Rightarrow> 'a CleanQ_Set_State"
  where "CleanQ_List2Set l = \<lparr> SX = lSX l, SY = lSY l, 
                               TXY = set (lTXY l), TYX = set (lTYX l) \<rparr>"


(* ==================================================================================== *)
subsection \<open>CleanQ List Model Invariants\<close>
(* ==================================================================================== *)

text \<open>
  We now formulate the invariants I1 and I2 under the the CleanQ list model, and add
  an additional invariant I3.
\<close>

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I1: Constant Union (Image)\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  The union of all sets is constant. We formulate this as an image for 
  \verb+CleanQ_List+ where we take the set of the transfer lists and apply the 
  union.
\<close>

fun I1_list_img :: "'a CleanQ_List_State \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1_list_img rb K \<longleftrightarrow> ((lSX rb) \<union> (lSY rb) \<union> set (lTXY rb) \<union> set (lTYX rb)) = K"

text \<open>
  We can show that the image of the invariant satisfies the original invariant I1 when
  we apply the lifting function \verb+CleanQ_List2Set+ to the model state. We prove
  this in the following lemma.
\<close>

lemma I1_list_img_lift:
  "I1_list_img L K = I1 (CleanQ_List2Set L) K"
  unfolding CleanQ_List2Set_def by(simp)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I2: Pairwise Empty (Image)\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
 All pairwise intersections are empty. Again, we formulate this as an image for
 \verb+CleanQ_List+ by taking the set of the transfer lists.
\<close>

fun I2_list_img :: "'a CleanQ_List_State \<Rightarrow> bool"
  where "I2_list_img rb \<longleftrightarrow> lSX rb \<inter> lSY rb = {} \<and> lSX rb \<inter> set (lTXY rb) = {} \<and> 
                       lSX rb \<inter> set (lTYX rb) = {} \<and> lSY rb \<inter> set (lTXY rb) = {} \<and> 
                       lSY rb \<inter> set (lTYX rb) = {} \<and> set (lTXY rb) \<inter> set (lTYX rb) = {}"


text \<open>
  Finally, we can show that the image of the Invariant I2 is equivalent to the original
  invariant, when we lift the CleanQ List State to the CleanQ Set State. We prove this
  in the following lemma:
\<close>

lemma I2_list_img_lift:
  "I2_list_img L = I2 (CleanQ_List2Set L)"
  unfolding CleanQ_List2Set_def by(simp)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I3: Distinct Transferlists\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  In contrast to sets, an element can be in a list twice. Thus we need to rule out,
  that a buffer can be present in a list twice. This invariant is required for the 
  move from sets to lists. In sets an element occurs only once while in lists it can 
  occur multiple times. If we map the list which contains twice the same element, 
  it would be mapped to only a single set element. In order to avoid this the elements 
  of the lists need to be distinct
\<close>

fun I3 :: "'a CleanQ_List_State \<Rightarrow> bool"
  where "I3 st_list \<longleftrightarrow> distinct (lTXY st_list) \<and> distinct (lTYX st_list)"


text \<open>
  Form the invariant I3, we obtain that the cardinality of the sets in the lifted
  CleanQ set state is the same as the length of the lists.
\<close>

lemma I3_cardinality : 
  assumes I3_holds : "I3 L"  and  lift: "LS = CleanQ_List2Set L"
    shows "length (lTXY L) = card (TXY LS) \<and> length (lTYX L) = card (TYX LS)"
  using I3_holds lift unfolding CleanQ_List2Set_def
  by (metis CleanQ_List2Set_def CleanQ_Set_State.ext_inject CleanQ_Set_State.surjective 
            I3.simps assms(2) distinct_card)



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>All CleanQ List Invariants\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We combine all invariants for the abstract CleanQ list model and define the unified 
  predicate \verb+CleanQ_List_Invariants+.
\<close>

fun CleanQ_List_Invariants :: "'a set \<Rightarrow> 'a CleanQ_List_State \<Rightarrow> bool"
  where "CleanQ_List_Invariants K rb \<longleftrightarrow> I1_list_img rb K \<and> I2_list_img rb \<and> I3 rb"


text \<open>
  Finally, we can show that when the CleanQ List invariants are satisfied, this also
  satisfies the set invariants.
\<close>

lemma CleanQ_List_Invariants_Set_Invariants:
  "CleanQ_List_Invariants K L \<Longrightarrow> CleanQ_Set_Invariants K (CleanQ_List2Set L)"
  unfolding CleanQ_List2Set_def by simp


(* ==================================================================================== *)
subsection \<open>State Transition Operations\<close>
(* ==================================================================================== *)

text \<open>
  We now formulate the state transition operations in terms of the CleanQ List model
  state. Again,  the two agents can, independently from each other, perform one of 
  two operations, \verb+enqueue+ and \verb+dequeue+,  which trigger an ownership 
  transfer of buffer elements.  
\<close>

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue Operation\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  The \verb+enqueue+ operation is analogous to the Set operations except that the elements
  are added to the list instead of inserted to the set. Note, we always insert the 
  element at the end of the list. 
\<close>

definition CleanQ_List_enq_x :: "'a \<Rightarrow> 'a CleanQ_List_State  \<Rightarrow> 'a CleanQ_List_State"
  where "CleanQ_List_enq_x b rb = rb \<lparr> lSX := (lSX rb) - {b}, lTXY := lTXY rb @ [b] \<rparr>"

definition CleanQ_List_enq_y :: "'a \<Rightarrow> 'a CleanQ_List_State  \<Rightarrow> 'a CleanQ_List_State"
  where "CleanQ_List_enq_y b rb = rb \<lparr> lSY := (lSY rb) - {b}, lTYX := lTYX rb @ [b] \<rparr>"


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
  We can now show that the result of the enqueue operation is the same as the
  enqueue operation on the set model. 
\<close>

lemma CleanQ_List_enq_x_equal :
  "CleanQ_List2Set (CleanQ_List_enq_x b rb) = CleanQ_Set_enq_x b (CleanQ_List2Set rb)"
  unfolding CleanQ_List2Set_def CleanQ_Set_enq_x_def CleanQ_List_enq_x_def 
  by(auto)

lemma CleanQ_List_enq_y_equal :
  "CleanQ_List2Set (CleanQ_List_enq_y b rb) = CleanQ_Set_enq_y b (CleanQ_List2Set rb)"
  unfolding CleanQ_List2Set_def CleanQ_Set_enq_y_def CleanQ_List_enq_y_def 
  by(auto)


text \<open>
  The enqueue operations move buffers around different sets and lists. We define a 
  few helper lemmas, which allow us to talk about where the buffer ends up.
\<close>

lemma CleanQ_List_enq_x_result :
  assumes X_owned: "b \<in> lSX rb"  and  X_enq: "rb' = CleanQ_List_enq_x b rb"
    and I2_holds : "I2_list_img rb"
  shows  "b \<in> set (lTXY rb') \<and> b \<notin> lSX rb' \<and> b \<notin> lSY rb' \<and> b \<notin> set (lTYX rb')"
  using X_owned X_enq I2_holds unfolding CleanQ_List_enq_x_def by(auto)

lemma CleanQ_List_enq_y_result :
  assumes Y_owned: "b \<in> lSY rb"  and  X_enq: "rb' = CleanQ_List_enq_y b rb"
    and I2_holds : "I2_list_img rb"
  shows  "b \<in> set (lTYX rb') \<and> b \<notin> lSY rb' \<and> b \<notin> lSX rb' \<and> b \<notin> set (lTXY rb')"
  using Y_owned X_enq I2_holds unfolding CleanQ_List_enq_y_def by(auto)

text \<open>
  Not only we can say that it is in the set of the list, we can even say that
  the buffer is precisely at the end of it.
\<close>

lemma CleanQ_List_enq_x_result_p :
  assumes X_owned: "b \<in> lSX rb"  and  X_enq: "rb' = CleanQ_List_enq_x b rb"
    and I2_holds : "I2_list_img rb"
  shows  "b = last (lTXY rb') \<and> b \<notin> lSX rb' \<and> b \<notin> lSY rb' \<and> b \<notin> set (lTYX rb')"
  using X_owned X_enq I2_holds unfolding CleanQ_List_enq_x_def by(auto)

lemma CleanQ_List_enq_y_result_p :
  assumes Y_owned: "b \<in> lSY rb"  and  X_enq: "rb' = CleanQ_List_enq_y b rb"
    and I2_holds : "I2_list_img rb"
  shows  "b = last (lTYX rb') \<and> b \<notin> lSY rb' \<and> b \<notin> lSX rb' \<and> b \<notin> set (lTXY rb')"
  using Y_owned X_enq I2_holds unfolding CleanQ_List_enq_y_def by(auto)


text \<open>
  The two operations \verb+CleanQ_Set_enq_x+ and \verb+CleanQ_Set_enq_y+ transition
  the model state. Thus we need to prove that all invariants are preserved. We do this
  Individually first, then do the union. Note, the proofs are symmetric. 
\<close>

lemma CleanQ_List_enq_x_I1 :
  assumes I1_holds: "I1_list_img rb K"  and  X_owned: "b \<in> lSX rb"
    shows "I1_list_img (CleanQ_List_enq_x b rb) K"
  unfolding CleanQ_List_enq_x_def 
  using I1_holds X_owned by auto

lemma CleanQ_List_enq_y_I1 :
  assumes I1_holds: "I1_list_img rb K"  and  X_owned: "b \<in> lSY rb"
    shows "I1_list_img (CleanQ_List_enq_y b rb) K"
  unfolding CleanQ_List_enq_y_def 
  using I1_holds X_owned by auto

lemma CleanQ_List_enq_x_I2 :
  assumes  I2_holds: "I2_list_img rb"   and  X_owned: "b \<in> lSX rb"
    shows "I2_list_img (CleanQ_List_enq_x b rb)"
  unfolding CleanQ_List_enq_x_def
  using I2_holds X_owned by auto

lemma CleanQ_List_enq_y_I2 :
  assumes I2_holds: "I2_list_img rb"    and  X_owned: "b \<in> lSY rb"
    shows "I2_list_img (CleanQ_List_enq_y b rb)"
  unfolding CleanQ_List_enq_y_def
  using I2_holds X_owned by auto

lemma CleanQ_List_enq_x_I3 :
  assumes  I2_holds: "I2_list_img rb" and I3_holds: "I3 rb"  and  X_owned: "b \<in> lSY rb"
    shows "I3 (CleanQ_List_enq_x b rb)"
  unfolding CleanQ_List_enq_x_def
  using  I2_holds I3_holds X_owned by auto

lemma CleanQ_List_enq_y_I3 :
  assumes  I2_holds: "I2_list_img rb" and I3_holds: "I3 rb"  and  X_owned: "b \<in> lSY rb"
    shows "I3 (CleanQ_List_enq_y b rb)"
  unfolding CleanQ_List_enq_y_def
  using  I2_holds I3_holds X_owned by(auto)


text \<open>
  Invariants I1, I2, and I3 are preserved by \verb+enqueue+ operations, thus we can 
  combine them to obtain show that the combined predicate \verb+CleanQ_List_Invariants+ 
  always holds.
\<close>

lemma CleanQ_List_enq_x_Invariants :
  assumes I_holds : "CleanQ_List_Invariants K rb"  and  X_owned: "b \<in> lSX rb"
  shows "CleanQ_List_Invariants K (CleanQ_List_enq_x b rb)"  
  unfolding CleanQ_List_enq_x_def 
  using I_holds CleanQ_List_enq_x_I3 CleanQ_List_enq_x_I2 CleanQ_List_enq_x_I1 X_owned 
    by(auto)

lemma CleanQ_List_enq_y_Invariants :
  assumes I_holds : "CleanQ_List_Invariants K rb"  and  Y_owned: "b \<in> lSY rb"
  shows "CleanQ_List_Invariants K (CleanQ_List_enq_y b rb)"  
  unfolding CleanQ_List_enq_y_def
  using I_holds CleanQ_List_enq_y_I3 CleanQ_List_enq_y_I2 CleanQ_List_enq_y_I1 Y_owned
  by(auto)


text \<open>
  Finally, we can show that the invariants of the set model are preserved.
\<close>

lemma CleanQ_List_enq_x_Set_Invariants :
  assumes I_holds : "CleanQ_List_Invariants K rb"  and  X_owned: "b \<in> lSX rb"
      and RB_upd: "rb' = CleanQ_List_enq_x b rb"
  shows "CleanQ_Set_Invariants K (CleanQ_List2Set rb')"  
  by (metis CleanQ_List_Invariants_Set_Invariants CleanQ_List_enq_x_Invariants 
            I_holds RB_upd X_owned) 

lemma CleanQ_List_enq_y_Set_Invariants :
  assumes I_holds : "CleanQ_List_Invariants K rb"  and  Y_owned: "b \<in> lSY rb"
      and RB_upd: "rb' = CleanQ_List_enq_y b rb"
  shows "CleanQ_Set_Invariants K (CleanQ_List2Set rb')"  
  by (metis CleanQ_List_Invariants_Set_Invariants CleanQ_List_enq_y_Invariants 
            I_holds RB_upd Y_owned) 



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  The \verb+dequeue+ operation is analogous to the Set operations except that the elements
  are removed from the list instead of inserted to the set. Note, we always remove the 
  element at the front of the list.
\<close>

definition CleanQ_List_deq_x :: "'a CleanQ_List_State  \<Rightarrow> 'a CleanQ_List_State"
  where "CleanQ_List_deq_x rb = rb \<lparr> lSX := (lSX rb) \<union> {hd (lTYX rb)}, 
                                     lTYX := tl (lTYX rb) \<rparr>" 

definition CleanQ_List_deq_y :: "'a CleanQ_List_State  \<Rightarrow> 'a CleanQ_List_State"
  where "CleanQ_List_deq_y rb = rb \<lparr> lSY := (lSY rb) \<union> {hd (lTXY rb)}, 
                                     lTXY := tl (lTXY rb) \<rparr>" 


text \<open>
  These definitions are the same as producing a new record, instead of updating the old one
\<close>

lemma CleanQ_List_deq_x_upd :
  "CleanQ_List_deq_x rb = \<lparr> lSX = (lSX rb) \<union> {hd (lTYX rb)}, lSY = lSY rb, 
                            lTXY = lTXY rb, lTYX = tl (lTYX rb) \<rparr>"
  by (simp add: CleanQ_List_deq_x_def)

lemma CleanQ_List_deq_y_upd :
  "CleanQ_List_deq_y rb = \<lparr> lSX = lSX rb, lSY = (lSY rb) \<union> {hd (lTXY rb)}, 
                            lTXY = tl (lTXY rb), lTYX = lTYX rb \<rparr>"
  by(simp add:CleanQ_List_deq_y_def)


text \<open>
  The dequeue operations move buffers around different sets and lists. We define a 
  few helper lemmas, which allow us to talk about where the buffer ends up.
\<close>

lemma CleanQ_List_deq_x_result :
  assumes ne: "lTYX rb \<noteq> []"  and  X_deq: "rb' = CleanQ_List_deq_x rb"
    and I2_holds : "I2_list_img rb" and I3_holds : "I3 rb" and buf: "b = hd (lTYX rb)"
  shows  "b \<in> (lSX rb') \<and> b \<notin> lSY rb' \<and> b \<notin> set(lTXY rb') \<and> b \<notin> set (lTYX rb')"
  using ne X_deq I2_holds I3_holds buf unfolding CleanQ_List_deq_x_def
  apply(simp) 
  by (metis disjoint_iff_not_equal distinct.simps(2) hd_in_set list.collapse)

lemma CleanQ_List_deq_y_result :
  assumes ne: "lTXY rb \<noteq> []"  and  Y_deq: "rb' = CleanQ_List_deq_y rb"
    and I2_holds : "I2_list_img rb" and I3_holds : "I3 rb" and buf: "b = hd (lTXY rb)"
  shows  "b \<in> (lSY rb') \<and> b \<notin> lSX rb' \<and> b \<notin> set(lTXY rb') \<and> b \<notin> set (lTYX rb')"
  using ne Y_deq I2_holds I3_holds buf unfolding CleanQ_List_deq_y_def
  apply(simp) 
  by (metis disjoint_iff_not_equal distinct.simps(2) hd_in_set list.collapse)


text \<open>
  We can now show that the operations have the same outcome of when lifted to the 
  set model. We first define a helper lemma that lets us talk about the set subtraction
  when we lift the list to a set. 
\<close>


lemma list_set_hd_tl_union:
  "\<And>L. L\<noteq>[] \<Longrightarrow> set (L) =  set([hd L] @ (tl L))"
  by(simp)


lemma list_set_hd_tl_subtract: 
 assumes ne: "L \<noteq> []" and dist : "distinct L"
 shows "set (tl L) = set (L) - {hd L}"
proof -
  have X0 : "L = [hd L] @ tl L"
    by (simp add: ne)

  have X1: "set (L) = {hd L} \<union> set (tl L)"
    by(subst X0, simp)

  from dist X0 have dn :
    "{hd L} \<inter> set (tl L) = {}"
    apply(simp)
    using  distinct.simps(2) by fastforce

  show ?thesis 
    using ne dist X1 dn by(simp)
qed

text \<open>
  Using the helper lemma, we can now proof the commutativity
\<close>

lemma CleanQ_List_deq_x_equal : 
  assumes ne: "lTYX rb \<noteq> []" and  TYX_owned : "b = hd (lTYX rb)" and  I3_holds : "I3 rb"
  shows "CleanQ_List2Set (CleanQ_List_deq_x rb) = CleanQ_Set_deq_x b (CleanQ_List2Set rb)"
  unfolding CleanQ_List2Set_def CleanQ_Set_deq_x_def CleanQ_List_deq_x_def
  using I3_holds ne TYX_owned by(simp add: list_set_hd_tl_subtract) 
 
lemma CleanQ_List_deq_y_equal : 
  assumes ne: "lTXY rb \<noteq> []" and  TXY_owned : "b = hd (lTXY rb)" and  I3_holds : "I3 rb"
  shows "CleanQ_List2Set (CleanQ_List_deq_y rb) = CleanQ_Set_deq_y b (CleanQ_List2Set rb)"
  unfolding CleanQ_List2Set_def CleanQ_Set_deq_y_def CleanQ_List_deq_y_def
  using assms by(simp add: list_set_hd_tl_subtract)
  



text \<open>
  The two operations \verb+CleanQ_List_deq_x+ and \verb+CleanQ_List_deq_y+ transition
  the model state. Thus we need to prove that invariants \verb+I1_list_img+, \verb+I2_list_img+, and 
  I3 are preserved for both of them.
\<close>

lemma CleanQ_List_deq_x_I1 :
  assumes I1_holds : "I1_list_img rb K"  and   TYX_ne: "(lTYX rb) \<noteq> []"
  shows "I1_list_img (CleanQ_List_deq_x rb) K"
  using TYX_ne I1_holds list_set_hd_tl_union
  unfolding CleanQ_List_deq_x_def by(auto)

lemma CleanQ_List_deq_y_I1 :
  assumes I1_holds : "I1_list_img rb K"  and   TXY_ne: "(lTXY rb) \<noteq> []"
  shows "I1_list_img (CleanQ_List_deq_y rb) K"
  using TXY_ne I1_holds list_set_hd_tl_union
  unfolding CleanQ_List_deq_y_def by(auto)


lemma CleanQ_List_deq_x_I2 :
  assumes I2_holds : "I2_list_img rb"  and   TYX_ne: "(lTYX rb) \<noteq> []" and I3_holds: "I3 rb"
  shows "I2_list_img (CleanQ_List_deq_x rb)"
  unfolding CleanQ_List_deq_x_def
  apply(simp)
  using assms 
  by (metis I2_list_img.elims(2) I3.elims(2) disjoint_insert(1) distinct.simps(2) 
            list.exhaust_sel list.simps(15))

lemma CleanQ_List_deq_y_I2 :
  assumes I2_holds : "I2_list_img rb"  and   TXY_ne: "(lTXY rb) \<noteq> []" and I3_holds: "I3 rb"
  shows "I2_list_img (CleanQ_List_deq_y rb)"
  unfolding CleanQ_List_deq_y_def
  apply(simp)
  using assms 
  apply(simp)
  by (smt I2_list_img.elims(2) I3.elims(2) Int_commute distinct.simps(2) insert_disjoint(1) 
          list.exhaust_sel list.simps(15))
  


lemma CleanQ_List_deq_x_I3 :
  assumes I3_holds : "I3 rb"
  shows "I3 (CleanQ_List_deq_x rb)"
    unfolding CleanQ_List_deq_x_def using I3_holds distinct_tl by auto

lemma CleanQ_List_deq_y_I3 :
  assumes I3_holds : "I3 rb"
  shows "I3 (CleanQ_List_deq_y rb)"
    unfolding CleanQ_List_deq_y_def using I3_holds distinct_tl by auto


text \<open>
  Both invariants I1, I2, and I3 are preserved by dequeue operations, thus we can combine them 
  to obtain show that the predicate \verb+CleanQ_List_Invariants+ holds
\<close>

lemma CleanQ_List_deq_x_Invariants :
  assumes I_holds : "CleanQ_List_Invariants K rb"  and  TYX_ne: "[] \<noteq> (lTYX rb)"
    shows "CleanQ_List_Invariants K (CleanQ_List_deq_x rb)" 
  using assms CleanQ_List_deq_x_I1 CleanQ_List_deq_x_I2 CleanQ_List_deq_x_I3
  by (metis CleanQ_List_Invariants.elims(2) CleanQ_List_Invariants.elims(3))

lemma CleanQ_List_deq_y_Invariants :
  assumes I_holds : "CleanQ_List_Invariants K rb"  and  TYX_ne: "[] \<noteq> (lTXY rb)"
    shows "CleanQ_List_Invariants K (CleanQ_List_deq_y rb)" 
   using assms CleanQ_List_deq_y_I1 CleanQ_List_deq_y_I2 CleanQ_List_deq_y_I3
   by (metis CleanQ_List_Invariants.elims(2) CleanQ_List_Invariants.elims(3))


(* ==================================================================================== *)
subsection \<open>Integration in SIMPL\<close>
(* ==================================================================================== *)


text \<open>
  We now integrate the the CleanQ List Model into SIMPL. For each of the two operations,
  enqueue and dequeue, we specify a Hoare-triple with pre and post conditions, and
  the operation.
\<close>

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue Operation\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We first show, that we can define a Hoare triple for the enqueue operations from both
  agents X and Y, and that in both cases the invariant is preserved.
\<close>


lemma CleanQ_List_enq_x_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>ListRB \<and> CleanQ_List_Invariants K \<acute>ListRB \<and> b \<in> lSX \<acute>ListRB \<rbrace> 
        \<acute>ListRB :== (CleanQ_List_enq_x b \<acute>ListRB) 
      \<lbrace> CleanQ_List_Invariants K \<acute>ListRB \<rbrace>"
  by(vcg, simp only: CleanQ_List_enq_x_Invariants)


lemma CleanQ_List_enq_y_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>ListRB \<and> CleanQ_List_Invariants K \<acute>ListRB \<and> b \<in> lSY \<acute>ListRB \<rbrace> 
        \<acute>ListRB :== (CleanQ_List_enq_y b \<acute>ListRB) 
      \<lbrace> CleanQ_List_Invariants K \<acute>ListRB \<rbrace>"
  by(vcg, simp only: CleanQ_List_enq_y_Invariants)



(* ==================================================================================== *)
subsection \<open>Pre- and post- conditions\<close>
(* ==================================================================================== *)

definition CleanQ_List_enq_x_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_List_State, 'a CleanQ_List_State) Semantic.xstate set"
  where "CleanQ_List_enq_x_pre K b =  Semantic.Normal ` {rb. CleanQ_List_Invariants K rb \<and> b \<in> lSX rb \<and> b \<notin> set (lTXY rb)}"

definition CleanQ_List_enq_y_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_List_State, 'a CleanQ_List_State) Semantic.xstate set"
  where "CleanQ_List_enq_y_pre K b = Semantic.Normal ` {rb. CleanQ_List_Invariants K rb \<and> b \<in> lSY rb \<and> b \<notin> set (lTYX rb)}"

definition CleanQ_List_deq_x_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_List_State, 'a CleanQ_List_State) Semantic.xstate set"        
  where "CleanQ_List_deq_x_pre K buf = Semantic.Normal ` {rb. I1_list_img rb K \<and> I2_list_img rb \<and> I3 rb \<and>
                                                          (lTYX rb) \<noteq> [] \<and> buf = hd (lTYX rb) }"

definition CleanQ_List_deq_y_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_List_State, 'a CleanQ_List_State) Semantic.xstate set"        
  where "CleanQ_List_deq_y_pre K buf = Semantic.Normal ` {rb. I1_list_img rb K \<and> I2_list_img rb \<and> I3 rb \<and>
                                                          (lTXY rb) \<noteq> [] \<and> buf = hd (lTXY rb) }"


end



