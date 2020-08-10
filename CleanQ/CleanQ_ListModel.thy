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
  imports Main "../Simpl/Vcg"  "../Complx/OG_Hoare" CleanQ_SetModel CleanQ_Utils
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

definition I1_list_img :: "'a CleanQ_List_State \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1_list_img rb K \<longleftrightarrow> ((lSX rb) \<union> (lSY rb) \<union> set (lTXY rb) \<union> set (lTYX rb)) = K"

text \<open>
  We can show that the image of the invariant satisfies the original invariant I1 when
  we apply the lifting function \verb+CleanQ_List2Set+ to the model state. We prove
  this in the following lemma.
\<close>

lemma I1_list_img_lift:
  "I1_list_img L K = I1 (CleanQ_List2Set L) K"
  unfolding CleanQ_List2Set_def I1_def I1_list_img_def by(simp)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I2: Pairwise Empty (Image)\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
 All pairwise intersections are empty. Again, we formulate this as an image for
 \verb+CleanQ_List+ by taking the set of the transfer lists.
\<close>

definition I2_list_img :: "'a CleanQ_List_State \<Rightarrow> bool"
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
  unfolding CleanQ_List2Set_def I2_def I2_list_img_def  by(simp)


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

definition  I3 :: "'a CleanQ_List_State \<Rightarrow> bool"
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
            I3_def assms(2) distinct_card)

text \<open>
  Additionally we have to define the weak frame condition for the concurrency case 
  again similar to the set model.
\<close>

fun frame_list_weak ::
  "'a list \<times> 'a set \<times> 'a list \<times> 'a set \<Rightarrow> 'a list \<times> 'a set \<times> 'a list \<times> 'a set \<Rightarrow> bool"
  where "frame_list_weak (a',B',c',D') (a,B,c,D) \<longleftrightarrow> (\<exists>\<delta>aB \<delta>Bc.
    a' = \<delta>aB @ a \<and>
    B' \<union> set \<delta>aB = set \<delta>Bc \<union> B \<and>
    c' @ \<delta>Bc = c \<and>
    B \<inter> set \<delta>Bc = {} \<and>
    distinct \<delta>Bc)
  \<and> D' = D"

lemma frame2_s_w:
  "frame_strong (a',B',c',D') (a,B,c,D) \<Longrightarrow> frame_list_weak (a',B',c',D') (a,B,c,D)"
  by(auto)


text \<open>The second weak frame condition refines the first.\<close>
lemma frame2_w_1_w:
  fixes st st' K
  assumes I1: "I1 (CleanQ_List2Set st') K"
      and I2: "I2 (CleanQ_List2Set st')"
      and I3: "I3 st'"
      and frame: "frame_list_weak (lTXY st', lSY st', lTYX st', lSX st') (lTXY st, lSY st, lTYX st, lSX st)"
    shows "frame_weak (TXY (CleanQ_List2Set st'), SY (CleanQ_List2Set st'), TYX (CleanQ_List2Set st'), SX (CleanQ_List2Set st')) 
                      (TXY (CleanQ_List2Set st), SY (CleanQ_List2Set st), TYX (CleanQ_List2Set st), SX (CleanQ_List2Set st))"
proof -
  from frame obtain \<delta>aB \<delta>Bc where
    fA: "lTXY st' = \<delta>aB @ lTXY st" and
    fB: "lSY st' \<union> set \<delta>aB = set \<delta>Bc \<union> lSY st" and
    fC: "lTYX st' @ \<delta>Bc = lTYX st" and
    dBC: "lSY st \<inter> set \<delta>Bc = {}" and
    fD: "lSX st' = lSX st"
    by(auto)

  define \<Delta>AB where "\<Delta>AB = set \<delta>aB"
  define \<Delta>BC where "\<Delta>BC = set \<delta>Bc"

  from fA \<Delta>AB_def have fA': "set (lTXY st') = \<Delta>AB \<union> set (lTXY st)"
    by(simp)
  from fB \<Delta>AB_def \<Delta>BC_def have fB': "lSY st' \<union> \<Delta>AB = \<Delta>BC \<union> lSY st"
    by(simp)
  from fC \<Delta>BC_def have fC': "set (lTYX st') \<union> \<Delta>BC = set (lTYX st)"
    by (metis set_append)

  from fA I3 \<Delta>AB_def have dAB: "set (lTXY st) \<inter> \<Delta>AB = {}"
    by(auto simp: I3_def)

  from fB have dAC: "set (lTXY st) \<inter> \<Delta>BC = {}"
  proof(rule contrapos_pp)
    assume "set (lTXY st) \<inter> \<Delta>BC \<noteq> {}"
    then obtain x where xa: "x \<in> set (lTXY st)" and xBC: "x \<in> set \<delta>Bc"
      unfolding \<Delta>BC_def by(blast)

    from xa fA have "x \<in> set (lTXY st')" by(auto)
    with I2 have "x \<notin> (lSY st')"
      by (meson I2_list_img_def I2_list_img_lift disjoint_iff_not_equal)
    moreover from xa fA I3 have "x \<notin> set \<delta>aB" by(auto simp: I3_def)
    ultimately show "(lSY st') \<union> set \<delta>aB \<noteq> set \<delta>Bc \<union> (lSY st)"
      using xBC by(auto)
  qed

  from dBC \<Delta>BC_def fB have dBC': "lSY st \<inter> \<Delta>BC = {}"
    by(auto)

  from fA' fB' fC' dAB dAC dBC' fD show ?thesis
    unfolding frame_weak.simps CleanQ_List2Set_def
    apply(simp) 
    by (metis sup.commute)
qed


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>All CleanQ List Invariants\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We combine all invariants for the abstract CleanQ list model and define the unified 
  predicate \verb+CleanQ_List_Invariants+.
\<close>

definition CleanQ_List_Invariants :: "'a set \<Rightarrow> 'a CleanQ_List_State \<Rightarrow> bool"
  where "CleanQ_List_Invariants K rb \<longleftrightarrow> I1_list_img rb K \<and> I2_list_img rb \<and> I3 rb"


lemmas CleanQ_List_Invariants_simp = CleanQ_List_Invariants_def I1_list_img_def
                                     I2_list_img_def I3_def

text \<open>
  Finally, we can show that when the CleanQ List invariants are satisfied, this also
  satisfies the set invariants.
\<close>

lemma CleanQ_List_Invariants_Set_Invariants:
  "CleanQ_List_Invariants K L \<Longrightarrow> CleanQ_Set_Invariants K (CleanQ_List2Set L)"
  by (simp add: CleanQ_List_Invariants_def CleanQ_Set_Invariants_def 
                I1_list_img_lift I2_list_img_lift)


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
  using X_owned X_enq I2_holds unfolding CleanQ_List_enq_x_def by(auto simp:I2_list_img_def)

lemma CleanQ_List_enq_y_result :
assumes Y_owned: "b \<in> lSY rb"  and  X_enq: "rb' = CleanQ_List_enq_y b rb"
    and I2_holds : "I2_list_img rb"
  shows  "b \<in> set (lTYX rb') \<and> b \<notin> lSY rb' \<and> b \<notin> lSX rb' \<and> b \<notin> set (lTXY rb')"
  using Y_owned X_enq I2_holds unfolding CleanQ_List_enq_y_def by(auto simp:I2_list_img_def)

text \<open>
  Not only we can say that it is in the set of the list, we can even say that
  the buffer is precisely at the end of it.
\<close>

lemma CleanQ_List_enq_x_result_p :
assumes X_owned: "b \<in> lSX rb"  and  X_enq: "rb' = CleanQ_List_enq_x b rb"
    and I2_holds : "I2_list_img rb"
  shows  "b = last (lTXY rb') \<and> b \<notin> lSX rb' \<and> b \<notin> lSY rb' \<and> b \<notin> set (lTYX rb')"
  using X_owned X_enq I2_holds unfolding CleanQ_List_enq_x_def by(auto simp:I2_list_img_def)

lemma CleanQ_List_enq_y_result_p :
assumes Y_owned: "b \<in> lSY rb"  and  X_enq: "rb' = CleanQ_List_enq_y b rb"
    and I2_holds : "I2_list_img rb"
  shows  "b = last (lTYX rb') \<and> b \<notin> lSY rb' \<and> b \<notin> lSX rb' \<and> b \<notin> set (lTXY rb')"
  using Y_owned X_enq I2_holds unfolding CleanQ_List_enq_y_def by(auto simp:I2_list_img_def)


text \<open>
  The two operations \verb+CleanQ_Set_enq_x+ and \verb+CleanQ_Set_enq_y+ transition
  the model state. Thus we need to prove that all invariants are preserved. We do this
  Individually first, then do the union. Note, the proofs are symmetric. 
\<close>

lemma CleanQ_List_enq_x_I1 :
assumes I1_holds: "I1_list_img rb K"  and  X_owned: "b \<in> lSX rb"
  shows "I1_list_img (CleanQ_List_enq_x b rb) K"
  using I1_holds X_owned unfolding CleanQ_List_enq_x_def I1_list_img_def  by auto

lemma CleanQ_List_enq_y_I1 :
assumes I1_holds: "I1_list_img rb K"  and  X_owned: "b \<in> lSY rb"
  shows "I1_list_img (CleanQ_List_enq_y b rb) K"
  using I1_holds X_owned unfolding CleanQ_List_enq_y_def I1_list_img_def  by auto

lemma CleanQ_List_enq_x_I2 :
assumes  I2_holds: "I2_list_img rb"   and  X_owned: "b \<in> lSX rb"
  shows "I2_list_img (CleanQ_List_enq_x b rb)"
  using I2_holds X_owned unfolding CleanQ_List_enq_x_def I2_list_img_def  by auto

lemma CleanQ_List_enq_y_I2 :
assumes I2_holds: "I2_list_img rb"    and  X_owned: "b \<in> lSY rb"
  shows "I2_list_img (CleanQ_List_enq_y b rb)"
  using I2_holds X_owned unfolding CleanQ_List_enq_y_def I2_list_img_def  by auto

lemma CleanQ_List_enq_x_I3 :
assumes I2_holds: "I2_list_img rb" and I3_holds: "I3 rb"  and  X_owned: "b \<in> lSY rb"
  shows "I3 (CleanQ_List_enq_x b rb)"
  using I2_holds I3_holds X_owned  unfolding CleanQ_List_enq_x_def I3_def I2_list_img_def 
  by auto

lemma CleanQ_List_enq_y_I3 :
  assumes  I2_holds: "I2_list_img rb" and I3_holds: "I3 rb"  and  X_owned: "b \<in> lSY rb"
    shows "I3 (CleanQ_List_enq_y b rb)"
  using I2_holds I3_holds X_owned  unfolding CleanQ_List_enq_y_def I3_def I2_list_img_def 
  by auto

text \<open>
  Also for the weak frame condition we have to show that enqueue preserves
  invariant 3.\<close>

lemma  CleanQ_List_enq_x_weak_I3 :
  fixes st st' K x
  assumes I: "CleanQ_List_Invariants K st'"
      and enq: "st = CleanQ_List_enq_x x st'"
      and frame: "frame2_weak (lTXY st' @ [x], lSY st', lTYX st', lSX st' - {x}) (lTXY st, lSY st, lTYX st, lSX st)"
      and owns: "x \<in> lSX st'"
    shows "I3 st"
proof(unfold I3_def, intro conjI)
  from frame obtain \<delta>aB \<delta>Bc where
    fA: "(lTXY st') @ [x] = \<delta>aB @ (lTXY st)" and
    fB: "(lSY st') \<union> set \<delta>aB = set \<delta>Bc \<union> (lSY st)" and
    fC: "(lTYX st') @ \<delta>Bc = lTYX st" and
    dBC: "(lSY st) \<inter> set \<delta>Bc = {}" and
    dsBC: "distinct \<delta>Bc" and
    fD: "(lSX st') - {x} = lSX st"
    by (metis CleanQ_List_State.select_convs(1) CleanQ_List_State.select_convs(2) 
        CleanQ_List_State.select_convs(3) CleanQ_List_State.select_convs(4) CleanQ_List_enq_x_upd 
        Un_commute append.left_neutral append_Nil2 distinct.simps(1) empty_set enq inf_bot_right)

  from I owns have "x \<notin> set (lTXY st')" by(auto simp:CleanQ_List_Invariants_simp)
  with I have "distinct ((lTXY st') @ [x])" by(auto simp:CleanQ_List_Invariants_simp)
  hence "distinct (\<delta>aB @ (lTXY st))" by(simp add:fA)
  thus "distinct (lTXY st)" by(auto)

  from fA have "set (\<delta>aB @ (lTXY st)) = set ((lTXY st') @ [x])" by(simp)
  hence "set \<delta>aB \<subseteq> set (lTXY st') \<union> {x}" by(auto)
  with fB have "set \<delta>Bc \<subseteq> set (lTXY st') \<union> (lSY st') \<union> {x}" by(auto)
  with I owns have "set (lTYX st') \<inter> set \<delta>Bc = {}"by(auto simp:CleanQ_List_Invariants_simp)
  moreover from I have "distinct (lTYX st')" by(auto simp:CleanQ_List_Invariants_simp)
  ultimately show "distinct (lTYX st)"
    using dsBC fC
    by (metis distinct_append)
qed


lemma  CleanQ_List_enq_y_weak_I3 :
  fixes st st' K x
  assumes I: "CleanQ_List_Invariants K st'"
      and enq: "st = CleanQ_List_enq_y x st'"
      and frame: "frame2_weak (lTYX st' @ [x], lSX st', lTYX st', lSY st' - {x}) (lTYX st, lSX st, lTXY st, lSY st)"
      and owns: "x \<in> lSY st'"
    shows "I3 st"
proof(unfold I3_def, intro conjI)
  from frame obtain \<delta>aB \<delta>Bc where
    fA: "(lTYX st') @ [x] = \<delta>aB @ (lTYX st)" and
    fB: "(lSX st') \<union> set \<delta>aB = set \<delta>Bc \<union> (lSX st)" and
    fC: "(lTXY st') @ \<delta>Bc = lTXY st" and
    dBC: "(lSX st) \<inter> set \<delta>Bc = {}" and
    dsBC: "distinct \<delta>Bc" and
    fD: "(lSY st') - {x} = lSY st"
    by (metis CleanQ_List_State.select_convs(1) CleanQ_List_State.select_convs(2) 
        CleanQ_List_State.select_convs(3) CleanQ_List_State.select_convs(4) CleanQ_List_enq_y_upd 
        Un_commute append.left_neutral append_Nil2 assms(2) distinct.simps(1) empty_set inf_bot_right)

  from I owns have "x \<notin> set (lTYX st')" by(auto simp:CleanQ_List_Invariants_simp)
  with I have "distinct ((lTYX st') @ [x])" by(auto simp:CleanQ_List_Invariants_simp)
  hence "distinct (\<delta>aB @ (lTYX st))" by(simp add:fA)
  thus "distinct (lTYX st)" by(auto)

  from fA have "set (\<delta>aB @ (lTYX st)) = set ((lTYX st') @ [x])" by(simp)
  hence "set \<delta>aB \<subseteq> set (lTYX st') \<union> {x}" by(auto)
  with fB have "set \<delta>Bc \<subseteq> set (lTYX st') \<union> (lSX st') \<union> {x}" by(auto)
  with I owns have "set (lTXY st') \<inter> set \<delta>Bc = {}" by(auto simp:CleanQ_List_Invariants_simp)
  moreover from I have "distinct (lTXY st')" by(auto simp:CleanQ_List_Invariants_simp)
  ultimately show "distinct (lTXY st)"
    using dsBC fC
    by (metis distinct_append)
qed

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
    by(auto simp:CleanQ_List_Invariants_simp)

lemma CleanQ_List_enq_x_weak_Invariants :
  fixes st st' K b
  assumes I: "CleanQ_List_Invariants K st'"
      and rb: "st = CleanQ_List_enq_x b st'"
      and frame: "frame_list_weak ((lTXY st') @ [b],lSY st', lTYX st', (lSX st') - {b}) (lTXY st, lSY st, lTYX st, lSX st)"
      and owns: "b \<in> lSX st'"
    shows "CleanQ_List_Invariants K st"  
  by (metis CleanQ_List_enq_x_Invariants I owns rb)


lemma CleanQ_List_enq_y_Invariants :
  assumes I_holds : "CleanQ_List_Invariants K rb"  and  Y_owned: "b \<in> lSY rb"
  shows "CleanQ_List_Invariants K (CleanQ_List_enq_y b rb)"  
  unfolding CleanQ_List_enq_y_def
  using I_holds CleanQ_List_enq_y_I3 CleanQ_List_enq_y_I2 CleanQ_List_enq_y_I1 Y_owned
  by(auto simp:CleanQ_List_Invariants_simp)

lemma CleanQ_List_enq_y_weak_Invariants :
  fixes st st' K b
  assumes I: "CleanQ_List_Invariants K st'"
      and rb: "st = CleanQ_List_enq_y b st'"
      and frame: "frame_list_weak ((lTYX st') @ [b],lSX st', lTXY st', (lSY st') - {b}) (lTYX st, lSX st, lTXY st, lSY st)"
      and owns: "b \<in> lSY st'"
    shows "CleanQ_List_Invariants K st"  
  by (metis CleanQ_List_enq_y_Invariants I owns rb)

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
  apply(simp add:CleanQ_List_Invariants_simp)
  by (metis disjoint_iff_not_equal distinct.simps(2) hd_in_set list.collapse)

lemma CleanQ_List_deq_y_result :
  assumes ne: "lTXY rb \<noteq> []"  and  Y_deq: "rb' = CleanQ_List_deq_y rb"
    and I2_holds : "I2_list_img rb" and I3_holds : "I3 rb" and buf: "b = hd (lTXY rb)"
  shows  "b \<in> (lSY rb') \<and> b \<notin> lSX rb' \<and> b \<notin> set(lTXY rb') \<and> b \<notin> set (lTYX rb')"
  using ne Y_deq I2_holds I3_holds buf unfolding CleanQ_List_deq_y_def
  apply(simp add:CleanQ_List_Invariants_simp)
  by (metis disjoint_iff_not_equal distinct.simps(2) hd_in_set list.collapse)


text \<open>
  We can now show that the operations have the same outcome of when lifted to the 
  set model.
\<close>

lemma CleanQ_List_deq_x_equal : 
  assumes ne: "lTYX rb \<noteq> []" and  TYX_owned : "b = hd (lTYX rb)" and  I3_holds : "I3 rb"
  shows "CleanQ_List2Set (CleanQ_List_deq_x rb) = CleanQ_Set_deq_x b (CleanQ_List2Set rb)"
  unfolding CleanQ_List2Set_def CleanQ_Set_deq_x_def CleanQ_List_deq_x_def
  using I3_holds ne TYX_owned by(simp add: list_set_hd_tl_subtract CleanQ_List_Invariants_simp) 
 
lemma CleanQ_List_deq_y_equal : 
  assumes ne: "lTXY rb \<noteq> []" and  TXY_owned : "b = hd (lTXY rb)" and  I3_holds : "I3 rb"
  shows "CleanQ_List2Set (CleanQ_List_deq_y rb) = CleanQ_Set_deq_y b (CleanQ_List2Set rb)"
  unfolding CleanQ_List2Set_def CleanQ_Set_deq_y_def CleanQ_List_deq_y_def
  using assms by(simp add: list_set_hd_tl_subtract CleanQ_List_Invariants_simp)
  



text \<open>
  The two operations \verb+CleanQ_List_deq_x+ and \verb+CleanQ_List_deq_y+ transition
  the model state. Thus we need to prove that invariants \verb+I1_list_img+, \verb+I2_list_img+, and 
  I3 are preserved for both of them.
\<close>

lemma CleanQ_List_deq_x_I1 :
  assumes I1_holds : "I1_list_img rb K"  and   TYX_ne: "(lTYX rb) \<noteq> []"
  shows "I1_list_img (CleanQ_List_deq_x rb) K"
  using TYX_ne I1_holds list_set_hd_tl_union
  unfolding CleanQ_List_deq_x_def by(auto simp:CleanQ_List_Invariants_simp)

lemma CleanQ_List_deq_y_I1 :
  assumes I1_holds : "I1_list_img rb K"  and   TXY_ne: "(lTXY rb) \<noteq> []"
  shows "I1_list_img (CleanQ_List_deq_y rb) K"
  using TXY_ne I1_holds list_set_hd_tl_union
  unfolding CleanQ_List_deq_y_def by(auto simp:CleanQ_List_Invariants_simp)


lemma CleanQ_List_deq_x_I2 :
  assumes I2_holds : "I2_list_img rb"  and   TYX_ne: "(lTYX rb) \<noteq> []" and I3_holds: "I3 rb"
  shows "I2_list_img (CleanQ_List_deq_x rb)"
  using assms  unfolding CleanQ_List_deq_x_def I2_list_img_def apply(simp)
  by (metis (no_types, lifting) I3_def distinct.simps(2) hd_Cons_tl inf_commute 
            insert_disjoint(1) list.simps(15))

lemma CleanQ_List_deq_y_I2 :
  assumes I2_holds : "I2_list_img rb"  and   TXY_ne: "(lTXY rb) \<noteq> []" and I3_holds: "I3 rb"
  shows "I2_list_img (CleanQ_List_deq_y rb)"
  using assms  unfolding CleanQ_List_deq_y_def I2_list_img_def apply(simp)
  by (metis (no_types, lifting) I3_def distinct.simps(2) hd_Cons_tl inf_commute 
            insert_disjoint(1) list.simps(15))
  


lemma CleanQ_List_deq_x_I3 :
  assumes I3_holds : "I3 rb"
  shows "I3 (CleanQ_List_deq_x rb)"
  using assms distinct_tl unfolding CleanQ_List_deq_x_def  I3_def by auto

lemma CleanQ_List_deq_y_I3 :
  assumes I3_holds : "I3 rb"
  shows "I3 (CleanQ_List_deq_y rb)"
  using assms distinct_tl unfolding CleanQ_List_deq_y_def  I3_def by auto


text \<open>The weak frame condition for an dequeue  preserves invariant 3.\<close>
lemma CleanQ_List_deq_x_weak_I3:
  fixes st st' K x
  assumes I: "CleanQ_List_Invariants K st'"
      and deq: "st = CleanQ_List_deq_x st'"
      and frame: "frame_list_weak (lTXY st', lSY st', lTYX st', lSX st' \<union> {x}) (lTXY st, lSY st, lTYX st, lSX st)"
      and hd: "lTYX st \<noteq> [] \<and> x = hd (lTYX st)"
    shows "I3 st"
proof(unfold I3_def, intro conjI)
  from frame obtain \<delta>aB \<delta>Bc where
    fA: "lTXY st' = \<delta>aB @ lTXY st" and
    fB: "lSY st' \<union> set \<delta>aB = set \<delta>Bc \<union> lSY st" and
    fC: "lTYX st' @ \<delta>Bc  = lTYX st" and
    dBC: "lSY st \<inter> set \<delta>Bc = {}" and
    dsBC: "distinct \<delta>Bc" and
    fD: "lSX st' \<union> {x} = lSX st"
    by auto

  from I have "distinct (lTXY st')" by(auto simp:CleanQ_List_Invariants_simp)
  with fA show "distinct (lTXY st)" by(auto)
  from fA have "set (\<delta>aB @ lTXY st) = set (lTXY st')" by(simp)
  hence "set \<delta>aB \<subseteq> set (lTXY st')" by(auto)
  with fB have "set \<delta>Bc \<subseteq> set (lTXY st') \<union> (lSY st')" by(auto)
  with I have "set (lTYX st') \<inter> set \<delta>Bc = {}" by(auto simp:CleanQ_List_Invariants_simp)
  moreover from I have "distinct (lTYX st')" by(auto simp:CleanQ_List_Invariants_simp)
  ultimately show "distinct (lTYX st)"
    using dsBC fC CleanQ_List_deq_x_I3 I deq  by (auto simp:CleanQ_List_Invariants_simp)
qed


text \<open>The weak frame condition for an dequeue  preserves invariant 3.\<close>
lemma CleanQ_List_deq_y_weak_I3:
  fixes st st' K x
  assumes I: "CleanQ_List_Invariants K st'"
      and deq: "st = CleanQ_List_deq_y st'"
      and frame: "frame_list_weak (lTYX st', lSX st', lTXY st', lSY st' \<union> {x}) (lTYX st, lSX st, lTXY st, lSY st)"
      and hd: "lTXY st \<noteq> [] \<and> x = hd (lTXY st)"
    shows "I3 st"
proof(unfold I3_def, intro conjI)
  from frame obtain \<delta>aB \<delta>Bc where
    fA: "lTYX st' = \<delta>aB @ lTYX st" and
    fB: "lSX st' \<union> set \<delta>aB = set \<delta>Bc \<union> lSX st" and
    fC: "lTXY st' @ \<delta>Bc  = lTXY st" and
    dBC: "lSX st \<inter> set \<delta>Bc = {}" and
    dsBC: "distinct \<delta>Bc" and
    fD: "lSY st' \<union> {x} = lSY st"
    by auto

  from I have "distinct (lTYX st')"  by (auto simp:CleanQ_List_Invariants_simp)
  with fA show "distinct (lTYX st)" by(auto)
  from fA have "set (\<delta>aB @ lTYX st) = set (lTYX st')" by(simp)
  hence "set \<delta>aB \<subseteq> set (lTYX st')" by(auto)
  with fB have "set \<delta>Bc \<subseteq> set (lTYX st') \<union> (lSX st')" by(auto)
  with I have "set (lTXY st') \<inter> set \<delta>Bc = {}" by (auto simp:CleanQ_List_Invariants_simp)
  moreover from I have "distinct (lTXY st')" by (auto simp:CleanQ_List_Invariants_simp)
  ultimately show "distinct (lTXY st)"
    using dsBC fC CleanQ_List_deq_y_I3 I deq by (auto simp:CleanQ_List_Invariants_simp)
qed

text \<open>
  Both invariants I1, I2, and I3 are preserved by dequeue operations, thus we can combine them 
  to obtain show that the predicate \verb+CleanQ_List_Invariants+ holds
\<close>

lemma CleanQ_List_deq_x_Invariants :
  assumes I_holds : "CleanQ_List_Invariants K rb"  and  TYX_ne: "[] \<noteq> (lTYX rb)"
    shows "CleanQ_List_Invariants K (CleanQ_List_deq_x rb)" 
  using assms CleanQ_List_deq_x_I1 CleanQ_List_deq_x_I2 CleanQ_List_deq_x_I3
  by (metis CleanQ_List_Invariants_simp)

lemma CleanQ_List_deq_y_Invariants :
  assumes I_holds : "CleanQ_List_Invariants K rb"  and  TYX_ne: "[] \<noteq> (lTXY rb)"
    shows "CleanQ_List_Invariants K (CleanQ_List_deq_y rb)" 
   using assms CleanQ_List_deq_y_I1 CleanQ_List_deq_y_I2 CleanQ_List_deq_y_I3
   by (metis CleanQ_List_Invariants_simp)



(* ==================================================================================== *)
subsection \<open>Multi-Step State Transition Operations\<close>
(* ==================================================================================== *)


text \<open>
  We now define the \verb+enqueue+ and \verb+dequeue+ operations for multipl step 
  state advancements in one instance. 
\<close>

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  We first define the \verb+enqueue_n+ operation, for both sides. This will remove a list
  of buffers from the owning set, and add it to the transfer set
\<close>

definition CleanQ_List_enq_n_x :: "'a list \<Rightarrow> 'a CleanQ_List_State \<Rightarrow> 'a CleanQ_List_State"
  where "CleanQ_List_enq_n_x B rb = rb \<lparr> lSX := (lSX rb) - set B, lTXY := lTXY rb @ B \<rparr>"

definition CleanQ_List_enq_n_y :: "'a list \<Rightarrow> 'a CleanQ_List_State \<Rightarrow> 'a CleanQ_List_State"
  where "CleanQ_List_enq_n_y B rb = rb \<lparr> lSY := (lSY rb) - set B, lTYX := lTYX rb @ B \<rparr>"


text \<open>
 This can be defined inductively as:
\<close>

lemma CleanQ_List_enq_n_x_ind:
  "CleanQ_List_enq_n_x (b # B) rb = CleanQ_List_enq_n_x B (CleanQ_List_enq_x b rb)"
  unfolding CleanQ_List_enq_n_x_def CleanQ_List_enq_x_def
  by (simp, meson Diff_insert2)
  

text \<open>
  The multi-step  enqueue operations move buffers around different sets and lists.
   We define a few helper lemmas, which allow us to talk about where the buffer ends up.
\<close>

lemma CleanQ_List_enq_n_x_result :
  assumes X_owned: "\<forall>b \<in> set B. b \<in> lSX rb"  and  X_enq: "rb' = CleanQ_List_enq_n_x B rb"
    and I2_holds : "I2_list_img rb"
  shows  "\<forall>b \<in> set B. b \<in> set (lTXY rb') \<and> b \<notin> lSX rb' \<and> b \<notin> lSY rb' \<and> b \<notin> set (lTYX rb')"
  using X_owned X_enq I2_holds unfolding CleanQ_List_enq_n_x_def 
  by(auto simp:CleanQ_List_Invariants_simp)

lemma CleanQ_List_enq_n_y_result :
  assumes X_owned: "\<forall>b \<in> set B. b \<in> lSY rb"  and  X_enq: "rb' = CleanQ_List_enq_n_y B rb"
    and I2_holds : "I2_list_img rb"
  shows  "\<forall>b \<in> set B. b \<in> set (lTYX rb') \<and> b \<notin> lSX rb' \<and> b \<notin> lSY rb' \<and> b \<notin> set (lTXY rb')"
  using X_owned X_enq I2_holds unfolding CleanQ_List_enq_n_y_def 
  by(auto simp:CleanQ_List_Invariants_simp)


text \<open>
  We can now show that the outcome of the list \verb+enqeue_n+ operation is the same
  as the corresponding set operation.
\<close>

lemma CleanQ_List_enq_n_x_equal :
  "CleanQ_List2Set (CleanQ_List_enq_n_x B rb) = CleanQ_Set_enq_n_x (set B) (CleanQ_List2Set rb)"
  unfolding CleanQ_List2Set_def CleanQ_Set_enq_n_x_def CleanQ_List_enq_n_x_def 
  by(auto)

lemma CleanQ_List_enq_n_yx_equal :
  "CleanQ_List2Set (CleanQ_List_enq_n_y B rb) = CleanQ_Set_enq_n_y (set B) (CleanQ_List2Set rb)"
  unfolding CleanQ_List2Set_def CleanQ_Set_enq_n_y_def CleanQ_List_enq_n_y_def 
  by(auto)


text \<open>
  We now show that the \verb+enqueue_n+ operation satisfy the list invariant, we show each
  invariant I1-I3 individually.
\<close>

lemma CleanQ_List_enq_n_x_I1 :
  assumes I1_holds: "I1_list_img rb K"  and  X_owned: "\<forall> b \<in> set B. b \<in> lSX rb"
    shows "I1_list_img (CleanQ_List_enq_n_x B rb) K"
  unfolding CleanQ_List_enq_n_x_def using I1_holds X_owned by(auto simp:CleanQ_List_Invariants_simp)

lemma CleanQ_List_enq_n_y_I1 :
  assumes I1_holds: "I1_list_img rb K"  and  Y_owned: "\<forall> b \<in> set B. b \<in> lSY rb"
    shows "I1_list_img (CleanQ_List_enq_n_y B rb) K"
  unfolding CleanQ_List_enq_n_y_def using I1_holds Y_owned  by(auto simp:CleanQ_List_Invariants_simp)

lemma CleanQ_List_enq_n_x_I2 :
  assumes  I2_holds: "I2_list_img rb"   and  X_owned: "\<forall>b \<in> set B. b \<in> lSX rb" 
      and  dist: "distinct B"
    shows "I2_list_img (CleanQ_List_enq_n_x B rb)"
  unfolding CleanQ_List_enq_n_x_def using I2_holds X_owned dist by(auto simp:CleanQ_List_Invariants_simp) 

lemma CleanQ_List_enq_n_y_I2 :
  assumes  I2_holds: "I2_list_img rb"   and  X_owned: "\<forall>b \<in> set B. b \<in> lSY rb" 
      and  dist: "distinct B"
    shows "I2_list_img (CleanQ_List_enq_n_y B rb)"
  unfolding CleanQ_List_enq_n_y_def using I2_holds X_owned dist by(auto simp:CleanQ_List_Invariants_simp)

lemma CleanQ_List_enq_n_x_I3 :
  assumes  I2_holds: "I2_list_img rb" and I3_holds: "I3 rb" 
      and  X_owned: "\<forall> b \<in> set B. b \<in> lSX rb" and  dist: "distinct B"
    shows "I3 (CleanQ_List_enq_n_x B rb)"
  unfolding CleanQ_List_enq_n_x_def  using  I2_holds I3_holds X_owned dist  by(auto simp:CleanQ_List_Invariants_simp)

lemma CleanQ_List_enq_n_y_I3 :
  assumes  I2_holds: "I2_list_img rb" and I3_holds: "I3 rb" 
      and  Y_owned: "\<forall> b \<in> set B. b \<in> lSY rb" and  dist: "distinct B"
    shows "I3 (CleanQ_List_enq_n_y B rb)"
  unfolding CleanQ_List_enq_n_y_def  using  I2_holds I3_holds Y_owned dist  by(auto simp:CleanQ_List_Invariants_simp)


text \<open>
  We can now combine the proofs for invariants I1-I3 and show the complete list invariant.
\<close>

lemma CleanQ_List_enq_n_x_Invariants :
  assumes I_holds : "CleanQ_List_Invariants K rb" 
      and  X_owned: "\<forall> b \<in> set B. b \<in> lSX rb" and  dist: "distinct B"
  shows "CleanQ_List_Invariants K (CleanQ_List_enq_n_x B rb)"  
  unfolding CleanQ_List_enq_n_x_def 
  using I_holds CleanQ_List_enq_n_x_I3 CleanQ_List_enq_n_x_I2 CleanQ_List_enq_n_x_I1
        X_owned  dist  by(auto simp:CleanQ_List_Invariants_simp)

lemma CleanQ_List_enq_n_y_Invariants :
  assumes I_holds : "CleanQ_List_Invariants K rb" 
      and  Y_owned: "\<forall> b \<in> set B. b \<in> lSY rb" and  dist: "distinct B"
  shows "CleanQ_List_Invariants K (CleanQ_List_enq_n_y B rb)"  
  unfolding CleanQ_List_enq_n_y_def 
  using I_holds CleanQ_List_enq_n_y_I3 CleanQ_List_enq_n_y_I2 CleanQ_List_enq_n_y_I1
        Y_owned  dist  by(auto simp:CleanQ_List_Invariants_simp)


text \<open>
  Finally, we can also show that the set invariants are preserved.
\<close>

lemma CleanQ_List_enq_n_x_Set_Invariants :
  assumes I_holds : "CleanQ_List_Invariants K rb"  
      and  X_owned: "\<forall> b \<in> set B. b \<in> lSX rb" and  dist: "distinct B"
      and RB_upd: "rb' = CleanQ_List_enq_n_x B rb"
    shows "CleanQ_Set_Invariants K (CleanQ_List2Set rb')"  
  using assms CleanQ_List_Invariants_Set_Invariants CleanQ_List_enq_n_x_Invariants 
  by(metis)

lemma CleanQ_List_enq_n_y_Set_Invariants :
  assumes I_holds : "CleanQ_List_Invariants K rb"  
      and  X_owned: "\<forall> b \<in> set B. b \<in> lSY rb" and  dist: "distinct B"
      and RB_upd: "rb' = CleanQ_List_enq_n_y B rb"
    shows "CleanQ_Set_Invariants K (CleanQ_List2Set rb')"  
  using assms CleanQ_List_Invariants_Set_Invariants CleanQ_List_enq_n_y_Invariants 
  by(metis)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  The multi-step \verb+dequeue_n+ operation is similar to the single step operation, 
  with the exception that it takes the first $n$ elements from the transfer list, instead
  of just the head.
\<close>

definition CleanQ_List_deq_n_x :: "nat \<Rightarrow> 'a CleanQ_List_State  \<Rightarrow> 'a CleanQ_List_State"
  where "CleanQ_List_deq_n_x n rb = rb \<lparr> lSX := (lSX rb) \<union> set (take n (lTYX rb)), 
                                     lTYX := drop n (lTYX rb) \<rparr>" 

definition CleanQ_List_deq_n_y :: "nat \<Rightarrow> 'a CleanQ_List_State  \<Rightarrow> 'a CleanQ_List_State"
  where "CleanQ_List_deq_n_y n rb = rb \<lparr> lSY := (lSY rb) \<union> set (take n (lTXY rb)), 
                                     lTXY := drop n (lTXY rb) \<rparr>" 

text \<open>
  We can now talk about the effects of the \verb+dequeue_n+ operation with respect to 
  the ownership sets. 
\<close>

lemma CleanQ_List_deq_n_x_equal : 
  assumes TYX_owned : "B = take n (lTYX rb)" and I3_holds : "I3 rb"
  shows "CleanQ_List2Set (CleanQ_List_deq_n_x n rb) = CleanQ_Set_deq_n_x (set B) (CleanQ_List2Set rb)"
  unfolding CleanQ_List2Set_def CleanQ_Set_deq_n_x_def CleanQ_List_deq_n_x_def
  using assms apply(auto)
  apply (simp add: in_set_dropD)
  apply (metis IntI empty_iff order_refl set_take_disj_set_drop_if_distinct I3_def)
  using set_append by fastforce

lemma CleanQ_List_deq_n_y_equal : 
  assumes  TYX_owned : "B = take n (lTXY rb)"  and  I3_holds : "I3 rb" 
  shows "CleanQ_List2Set (CleanQ_List_deq_n_y n rb) = CleanQ_Set_deq_n_y (set B) (CleanQ_List2Set rb)"
  unfolding CleanQ_List2Set_def CleanQ_Set_deq_n_y_def CleanQ_List_deq_n_y_def
  using assms apply(auto)
  apply (simp add: in_set_dropD)
  apply (metis IntI empty_iff order_refl set_take_disj_set_drop_if_distinct I3_def)
  using set_append by fastforce


text \<open>
  The \verb+dequeue_n+ operation preserves the invariant I1-I3
\<close>

lemma CleanQ_List_deq_n_x_I1 :
  assumes I1_holds : "I1_list_img rb K"
  shows "I1_list_img (CleanQ_List_deq_n_x n rb) K"
  unfolding CleanQ_List_deq_n_x_def using I1_holds
  apply(auto simp: I1_list_img_def, simp add: in_set_takeD)  
  apply (meson in_set_dropD)
  by (metis UnE append_take_drop_id set_append)
  
lemma CleanQ_List_deq_n_y_I1 :
  assumes I1_holds : "I1_list_img rb K"
  shows "I1_list_img (CleanQ_List_deq_n_y n rb) K"
  unfolding CleanQ_List_deq_n_y_def using I1_holds
  apply(auto simp: I1_list_img_def, simp add: in_set_takeD)  
  apply (meson in_set_dropD)
  by (metis UnE append_take_drop_id set_append)

lemma CleanQ_List_deq_n_x_I2 :
  assumes I2_holds : "I2_list_img rb"  and  I3_holds: "I3 rb"
  shows "I2_list_img (CleanQ_List_deq_n_x n rb)"
  unfolding CleanQ_List_deq_n_x_def  using I2_holds I3_holds list_distinct_drop_take_inter
  apply(auto simp:I2_list_img_def I3_def list_distinct_drop_take_element)
  using in_set_takeD in_set_dropD by fastforce+
  
  

lemma CleanQ_List_deq_n_y_I2 :
  assumes I2_holds : "I2_list_img rb"  and  I3_holds: "I3 rb"
  shows "I2_list_img (CleanQ_List_deq_n_y n rb)"
unfolding CleanQ_List_deq_n_y_def  using I2_holds I3_holds list_distinct_drop_take_inter
  apply(auto simp:I2_list_img_def I3_def list_distinct_drop_take_element)
  using in_set_takeD in_set_dropD by fastforce+


lemma CleanQ_List_deq_n_x_I3 :
  assumes I3_holds : "I3 rb"
  shows "I3 (CleanQ_List_deq_n_x n rb)"
    unfolding CleanQ_List_deq_n_x_def using I3_holds distinct_tl by (auto simp:I3_def)

lemma CleanQ_List_deq_n_y_I3 :
  assumes I3_holds : "I3 rb"
  shows "I3 (CleanQ_List_deq_n_y n rb)"
    unfolding CleanQ_List_deq_n_y_def using I3_holds distinct_tl by (auto simp:I3_def)


lemma CleanQ_List_deq_n_x_Invariants :
assumes I_holds : "CleanQ_List_Invariants K rb" 
  shows "CleanQ_List_Invariants K (CleanQ_List_deq_n_x n rb)" 
  using assms CleanQ_List_deq_n_x_I1 CleanQ_List_deq_n_x_I2 CleanQ_List_deq_n_x_I3
  using CleanQ_List_Invariants_simp by blast

lemma CleanQ_List_deq_n_y_Invariants :
assumes I_holds : "CleanQ_List_Invariants K rb" 
  shows "CleanQ_List_Invariants K (CleanQ_List_deq_n_y n rb)" 
  using assms CleanQ_List_deq_n_y_I1 CleanQ_List_deq_n_y_I2 CleanQ_List_deq_n_y_I3
  using CleanQ_List_Invariants_simp by blast


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
  where "CleanQ_List_deq_x_pre K buf = Semantic.Normal ` {rb.  CleanQ_List_Invariants K rb \<and>
                                                          (lTYX rb) \<noteq> [] \<and> buf = hd (lTYX rb) }"

definition CleanQ_List_deq_y_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_List_State, 'a CleanQ_List_State) Semantic.xstate set"        
  where "CleanQ_List_deq_y_pre K buf = Semantic.Normal ` {rb. CleanQ_List_Invariants K rb \<and>
                                                          (lTXY rb) \<noteq> [] \<and> buf = hd (lTXY rb) }"


end



