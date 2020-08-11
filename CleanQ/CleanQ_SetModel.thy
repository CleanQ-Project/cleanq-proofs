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



section \<open>Abstract CleanQ Set Model\<close>

text \<open>
  We define the CleanQ set model in the the following Isabelle theory: 
\<close>

theory CleanQ_SetModel
(*<*)
imports 
  Main
  "../Simpl/Simpl" 
  "../Complx/OG_Hoare"
begin
(*>*)


text \<open>
  We now define the model state, its invariants and state transitions. 
\<close>

(* ==================================================================================== *)
subsection \<open>CleanQ Set Model State\<close>
(* ==================================================================================== *)

text \<open>
  We model a system with a single point-to-point queue between two agents $X$ and $Y$.
  The state of the abstract CleanQ Set model is captured in the Isabelle record
  \verb+CleanQ_Set_State+. It consists of four sets, each of which capturing the ownership 
  of buffer elements in the system. The sets can be divided into two groups: First, 
  buffer elements that are owned by either $X$ or $Y$, and secondly, buffer elements that
  are in transfer between $X$ and $Y$ or between $Y$ and $X$:

  \<^item> SX: this is the set of buffers owned by X.
  \<^item> SY: this is the set of buffers owned by Y.
  \<^item> TXY: this is the set of buffers in transfer from X to Y.
  \<^item> TYX: this is the set of buffers in transfer from Y to X.
\<close>

record 'a CleanQ_Set_State =
  SX  :: "'a set"
  SY  :: "'a set"
  TXY :: "'a set"
  TYX :: "'a set"

text \<open>
  Note, we do not specify the representation of the buffer elements. This can be a single,
  fixed-sized page frame, a variable-sized base-limit segment, or a set of memory 
  locations. 
\<close>

(*<*)
(* Define some global variables to make Simpl/Complex proofs work *)
record 'g CleanQ_Set_State_vars = 
  SetRB_'  :: "nat CleanQ_Set_State"
(*>*)
  


(* ==================================================================================== *)
subsection \<open>CleanQ Set Model Invariants\<close>
(* ==================================================================================== *)


text \<open>
  In the CleanQ model, every buffer element has its well-defined owner. In other words,
  buffer elements are not lost or magically created, and at any point in time, a buffer
  element is owned by precisely one set. We now state the invariants of the abstract
  CleanQ Set Model.
\<close>

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I1: Constant Union\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  The union of all sets is constant. This ensures that buffer elements are not lost, or
  created during the ownership transfer. The constant $K$ is a set of buffer elements.
  Recall, the actual representation of buffer elements is undefined.
\<close>

definition I1 :: "'a CleanQ_Set_State \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1 rb K \<longleftrightarrow> ((SX rb) \<union> (SY rb) \<union> (TXY rb) \<union> (TYX rb)) = K"


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I2: Pairwise Empty\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  A buffer element cannot be in more than one set at any instance of time, otherwise there
  would be multiple owners for the same buffer element. We express this invariant as ``All
  pairwise intersections of the sets in the model state are empty''. Thus, a buffer element
  cannot be in more than one set. We express this by explicitly listing all intersections
  for the state with two agents.
\<close>

definition I2 :: "'a CleanQ_Set_State \<Rightarrow> bool"
  where "I2 rb \<longleftrightarrow> SX rb \<inter> SY rb = {} \<and> SX rb \<inter> TXY rb = {} \<and> SX rb \<inter> TYX rb = {} \<and>
                   SY rb \<inter> TXY rb = {} \<and> SY rb \<inter> TYX rb = {} \<and> TXY rb \<inter> TYX rb = {}"


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>CleanQ Set Invariants\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We combine all invariants for the abstract CleanQ set model and define the unified
  predicate \verb+CleanQ_Set_Invariants+.
\<close>

definition CleanQ_Set_Invariants :: "'a set \<Rightarrow> 'a CleanQ_Set_State \<Rightarrow> bool"
  where "CleanQ_Set_Invariants K rb \<longleftrightarrow> I1 rb K \<and> I2 rb"


lemmas CleanQ_Set_Invariants_simp = CleanQ_Set_Invariants_def I1_def I2_def
  


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
  The enqueue operation initiates a transfer of ownership from $X \rightarrow Y$
  (\verb+CleanQ_Set_enq_x+), or the other direction from $Y \rightarrow X$ 
  (\verb+CleanQ_Set_enq_y+). This corresponds to removing the element from set $SX$ and 
  inserting it into set $TXY$, or removing it from the set $XY$ and inserting it to 
  $TYX$ respectively. In both cases, we update the CleanQ sate by updating the sets
  accordingly.
\<close>

definition CleanQ_Set_enq_x :: "'a \<Rightarrow> 'a CleanQ_Set_State \<Rightarrow> 'a CleanQ_Set_State"
  where "CleanQ_Set_enq_x b rb = rb \<lparr> SX := (SX rb) - {b}, TXY := (TXY rb) \<union> {b} \<rparr>"

definition CleanQ_Set_enq_y :: "'a \<Rightarrow> 'a CleanQ_Set_State \<Rightarrow> 'a CleanQ_Set_State"
  where "CleanQ_Set_enq_y b rb = rb \<lparr> SY := (SY rb) - {b}, TYX := (TYX rb) \<union> {b} \<rparr>"


text \<open>
  These definitions are the same as producing a new record:
\<close>

lemma CleanQ_Set_enq_x_upd :
  "CleanQ_Set_enq_x b rb = \<lparr> SX = (SX rb) - {b}, SY = (SY rb), 
                             TXY = (TXY rb) \<union> {b}, TYX = (TYX rb) \<rparr>"
  by(simp add:CleanQ_Set_enq_x_def)

lemma CleanQ_Set_enq_y_upd :
  "CleanQ_Set_enq_y b rb = \<lparr> SX = (SX rb), SY = (SY rb) - {b}, 
                             TXY = (TXY rb), TYX = (TYX rb) \<union> {b} \<rparr>"
  by(simp add:CleanQ_Set_enq_y_def)


text \<open>
  The two operations \verb+CleanQ_Set_enq_x+ and \verb+CleanQ_Set_enq_y+ transition
  the model state. Thus we need to prove that invariants I1 and I2 are preserved for
  both of them.
\<close>

lemma CleanQ_Set_enq_x_I1 :
assumes I1_holds: "I1 rb K"  and  X_owned: "b \<in> SX rb" 
  shows "I1 (CleanQ_Set_enq_x b rb) K"
  using I1_holds X_owned unfolding CleanQ_Set_enq_x_def I1_def by auto

lemma CleanQ_Set_enq_y_I1 :
assumes I1_holds: "I1 rb K"  and  X_owned: "b \<in> SY rb"
  shows "I1 (CleanQ_Set_enq_y b rb) K"
  using I1_holds X_owned unfolding CleanQ_Set_enq_y_def I1_def by auto

lemma CleanQ_Set_enq_x_I2 :
assumes I2_holds: "I2 rb"  and  X_owned: "b \<in> SX rb"
  shows "I2 (CleanQ_Set_enq_x b rb)"
  using I2_holds X_owned unfolding CleanQ_Set_enq_x_def I2_def  by auto

lemma CleanQ_Set_enq_y_I2 :
assumes  I2_holds: "I2 rb"  and  X_owned: "b \<in> SY rb"
  shows "I2 (CleanQ_Set_enq_y b rb)"
  using I2_holds X_owned unfolding CleanQ_Set_enq_y_def I2_def by auto


text \<open>
  Both invariants I1 and I2 are preserved by \verb+enqueue+ operations, thus we can 
  combine them to obtain show that the combined predicate \verb+CleanQ_Set_Invariants+ 
  always holds.
\<close>

lemma CleanQ_Set_enq_x_Invariants :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "b \<in> SX rb"
  shows "CleanQ_Set_Invariants K (CleanQ_Set_enq_x b rb)"  
  using assms CleanQ_Set_Invariants_def CleanQ_Set_enq_x_I1 CleanQ_Set_enq_x_I2 by metis

lemma CleanQ_Set_enq_y_Invariants :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "b \<in> SY rb"
  shows "CleanQ_Set_Invariants K (CleanQ_Set_enq_y b rb)"  
  using assms CleanQ_Set_Invariants_def CleanQ_Set_enq_y_I1 CleanQ_Set_enq_y_I2 by metis


text \<open>
  We can show that the buffers are ending up in the right set. Buffer B will end up in 
  the transfer set, this is trivially true by definition.
\<close>

lemma CleanQ_Set_enq_x_dst :
  "b \<in> TXY (CleanQ_Set_enq_x b rb)"
  by (simp add: CleanQ_Set_enq_x_upd)

lemma CleanQ_Set_enq_y_dst :
  "b \<in> TYX (CleanQ_Set_enq_y b rb)"
  by (simp add: CleanQ_Set_enq_y_upd)


text \<open>
  Next, we can show that the buffers are not in the other sets
\<close>

lemma CleanQ_Set_enq_x_ndst1 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "b \<in> SX rb"
  shows "b \<notin> SY (CleanQ_Set_enq_x b rb)"
  using I_holds X_owned 
  unfolding CleanQ_Set_Invariants_simp CleanQ_Set_enq_x_def by(auto)

lemma CleanQ_Set_enq_x_ndst2 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "b \<in> SX rb"
  shows "b \<notin> SX (CleanQ_Set_enq_x b rb)"
  using I_holds X_owned 
  unfolding CleanQ_Set_Invariants_simp CleanQ_Set_enq_x_def by(auto)

lemma CleanQ_Set_enq_x_ndst3 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "b \<in> SX rb"
  shows "b \<notin> TYX (CleanQ_Set_enq_x b rb)"
  using I_holds X_owned 
  unfolding CleanQ_Set_Invariants_simp CleanQ_Set_enq_x_def by(auto)

lemma CleanQ_Set_enq_y_ndst1 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "b \<in> SY rb"
  shows "b \<notin> SX (CleanQ_Set_enq_y b rb)"
  using I_holds Y_owned 
  unfolding CleanQ_Set_Invariants_simp CleanQ_Set_enq_y_def by(auto)

lemma CleanQ_Set_enq_y_ndst2 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "b \<in> SY rb"
  shows "b \<notin> SY (CleanQ_Set_enq_y b rb)"
  using I_holds Y_owned 
  unfolding CleanQ_Set_Invariants_simp CleanQ_Set_enq_y_def by(auto)

lemma CleanQ_Set_enq_y_ndst3 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "b \<in> SY rb"
  shows "b \<notin> TXY (CleanQ_Set_enq_y b rb)"
  using I_holds Y_owned 
  unfolding CleanQ_Set_Invariants_simp CleanQ_Set_enq_y_def by(auto)


text \<open>
  Finally, we can combine the lemmas to obtain a single lemma for \verb+enqueue+
  operation where the buffers end up.  
\<close>

lemma CleanQ_Set_enq_x_result :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "b \<in> SX rb"
    and CQ: "rb' = CleanQ_Set_enq_x b rb"
  shows "b \<in> TXY rb' \<and>  b \<notin> SX rb' \<and> b \<notin> SY rb' \<and> b \<notin> TYX rb'"
  using assms
  by (simp add: CleanQ_Set_enq_x_dst CleanQ_Set_enq_x_ndst1 CleanQ_Set_enq_x_ndst2 
                CleanQ_Set_enq_x_ndst3)

lemma CleanQ_Set_enq_y_result :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "b \<in> SY rb"
    and CQ: "rb' = CleanQ_Set_enq_y b rb"
  shows "b \<in> TYX rb' \<and>  b \<notin> SX rb' \<and> b \<notin> SY rb' \<and> b \<notin> TXY rb'"
  using assms
  by (simp add: CleanQ_Set_enq_y_dst CleanQ_Set_enq_y_ndst1 CleanQ_Set_enq_y_ndst2 
                CleanQ_Set_enq_y_ndst3)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  The dequeue operation completes a transfer of ownership from $Y \rightarrow X$
  (\verb+CleanQ_Set_deq_x+), or the other direction from $X \rightarrow X$ 
  (\verb+CleanQ_Set_deq_y+). This corresponds to removing the element from set $TXY$ and 
  inserting it into set $SY$, or removing it from the set $TYX$ and inserting it to 
  $SX$ respectively. In both cases, we update the CleanQ sate by updating the sets
  accordingly.
\<close>

definition CleanQ_Set_deq_x :: "'a \<Rightarrow> 'a CleanQ_Set_State \<Rightarrow> 'a CleanQ_Set_State"
  where "CleanQ_Set_deq_x b rb = \<lparr> SX = (SX rb) \<union> {b}, SY = (SY rb), TXY = (TXY rb),  
                                   TYX = (TYX rb) - {b} \<rparr>"

definition CleanQ_Set_deq_y :: "'a \<Rightarrow> 'a CleanQ_Set_State \<Rightarrow> 'a CleanQ_Set_State"
  where "CleanQ_Set_deq_y b rb = \<lparr> SX = (SX rb), SY = (SY rb) \<union> {b}, 
                                   TXY = (TXY rb) - {b}, TYX = (TYX rb) \<rparr>"


text \<open>
  These definitions are the same as producing a new record:
\<close>

lemma CleanQ_Set_deq_x_upd :
  "CleanQ_Set_deq_x b rb = \<lparr> SX = (SX rb) \<union> {b}, SY = (SY rb), 
                             TXY = (TXY rb), TYX = (TYX rb) - {b} \<rparr>"
  by(simp add:CleanQ_Set_deq_x_def)

lemma CleanQ_Set_deq_y_upd :
  "CleanQ_Set_deq_y b rb = \<lparr> SX = (SX rb), SY = (SY rb) \<union> {b},
                             TXY = (TXY rb) - {b}, TYX = (TYX rb) \<rparr>"
  by(simp add:CleanQ_Set_deq_y_def)


text \<open>
  The two operations \verb+CleanQ_Set_deq_x+ and \verb+CleanQ_Set_deq_y+ transition
  the model state. Thus we need to prove that invariants I1 and I2 are preserved for
  both of them.
\<close>

lemma CleanQ_Set_deq_x_I1 :
assumes I1_holds : "I1 rb K"  and  TYX_owned: "b \<in> TYX rb"
  shows "I1 (CleanQ_Set_deq_x b rb) K"
  using I1_holds TYX_owned unfolding CleanQ_Set_deq_x_def I1_def  by auto

lemma CleanQ_Set_deq_y_I1 :
assumes I1_holds : "I1 rb K"  and  TXY_owned: "b \<in> TXY rb"
  shows "I1 (CleanQ_Set_deq_y b rb) K"
  using I1_holds TXY_owned unfolding CleanQ_Set_deq_y_def I1_def  by auto

lemma CleanQ_Set_deq_x_I2 :
assumes  I2_holds : "I2 rb"  and  TYX_owned: "b \<in> TYX rb"
  shows "I2 (CleanQ_Set_deq_x b rb)"
  using I2_holds TYX_owned  unfolding CleanQ_Set_deq_x_def I2_def by auto

lemma CleanQ_Set_deq_y_I2 :
assumes  I2_holds : "I2 rb"  and  TXY_owned: "b \<in> TXY rb"
  shows "I2 (CleanQ_Set_deq_y b rb)"
  using I2_holds TXY_owned  unfolding CleanQ_Set_deq_y_def I2_def by auto


text \<open>
  Both invariants I1 and I2 are preserved by dequeue operations, thus we can combine them 
  to obtain show that the predicate \verb+CleanQ_Set_Invariants+ holds
\<close>

lemma CleanQ_Set_deq_x_Invariants :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  TYX_owned: "b \<in> TYX rb"
  shows "CleanQ_Set_Invariants K (CleanQ_Set_deq_x b rb)" 
  using assms unfolding CleanQ_Set_Invariants_def I1_def I2_def CleanQ_Set_deq_x_def 
  by auto
   

lemma CleanQ_Set_deq_y_Invariants :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  TXY_owned: "b \<in> TXY rb"
  shows "CleanQ_Set_Invariants K (CleanQ_Set_deq_y b rb)" 
  using assms unfolding CleanQ_Set_Invariants_def I1_def I2_def CleanQ_Set_deq_y_def 
  by auto


text \<open>
  We can show that the buffers are ending up in the right set. The dequeued buffer goes
  into the SX or SY sets respectively. This is by definition, and thus trivial.
\<close>

lemma CleanQ_Set_deq_x_dst :
  "b \<in> SX (CleanQ_Set_deq_x b rb)"
  by (simp add: CleanQ_Set_deq_x_upd)


lemma CleanQ_Set_deq_y_dst :
  "b \<in> SY (CleanQ_Set_deq_y b rb)"
  by (simp add: CleanQ_Set_deq_y_upd)


text \<open>
  Next, we can show that the buffer not in any of the other sets. 
\<close>

lemma CleanQ_Set_deq_x_ndst1 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "b \<in> TYX rb"
  shows "b \<notin> SY (CleanQ_Set_deq_x b rb)"
  using assms unfolding CleanQ_Set_deq_x_def CleanQ_Set_Invariants_simp by(auto)

lemma CleanQ_Set_deq_x_ndst2 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "b \<in> TYX rb"
  shows "b \<notin> TXY (CleanQ_Set_deq_x b rb)"
  using assms unfolding CleanQ_Set_deq_x_def CleanQ_Set_Invariants_simp by(auto)

lemma CleanQ_Set_deq_x_ndst3 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "b \<in> TYX rb"
  shows "b \<notin> TYX (CleanQ_Set_deq_x b rb)"
  using assms unfolding CleanQ_Set_deq_x_def CleanQ_Set_Invariants_simp by(auto)

lemma CleanQ_Set_deq_y_ndst1 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "b \<in> TXY rb"
  shows "b \<notin> SX (CleanQ_Set_deq_y b rb)"
  using assms unfolding CleanQ_Set_deq_y_def CleanQ_Set_Invariants_simp by(auto)

lemma CleanQ_Set_deq_y_ndst2 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "b \<in> TXY rb"
  shows "b \<notin> TYX (CleanQ_Set_deq_y b rb)"
  using assms unfolding CleanQ_Set_deq_y_def CleanQ_Set_Invariants_simp by(auto)

lemma CleanQ_Set_deq_y_ndst3 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "b \<in> TXY rb"
  shows "b \<notin> TXY (CleanQ_Set_deq_y b rb)"
  using assms unfolding CleanQ_Set_deq_y_def CleanQ_Set_Invariants_simp by(auto)


text \<open>
  Finally, we combine the lemmas above to obtain a single lemma for the \verb+dequeue+
  operation. 
\<close>

lemma CleanQ_Set_deq_x_result :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  YX_owned: "b \<in> TYX rb"
    and CQ: "rb' = CleanQ_Set_deq_x b rb"
  shows "b \<in> SX rb' \<and>  b \<notin> SY rb' \<and> b \<notin> TXY rb' \<and> b \<notin> TYX rb'"
  using assms
  by (simp add: CleanQ_Set_deq_x_dst CleanQ_Set_deq_x_ndst1 CleanQ_Set_deq_x_ndst2 
                CleanQ_Set_deq_x_ndst3)

lemma CleanQ_Set_deq_y_result :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  YX_owned: "b \<in> TXY rb"
    and CQ: "rb' = CleanQ_Set_deq_y b rb"
  shows "b \<in> SY rb' \<and>  b \<notin> SX rb' \<and> b \<notin> TXY rb' \<and> b \<notin> TYX rb'"
  using assms
  by (simp add: CleanQ_Set_deq_y_dst CleanQ_Set_deq_y_ndst1 CleanQ_Set_deq_y_ndst2 
                CleanQ_Set_deq_y_ndst3)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Lemmas Summaries\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We define a few lemmas and lemma groups which simplify the proofs
\<close>

lemmas CleanQ_Set_ops = CleanQ_Set_deq_x_def CleanQ_Set_deq_y_def 
                        CleanQ_Set_enq_x_def CleanQ_Set_enq_y_def


(* ==================================================================================== *)
subsection \<open>Multistep State Transition Operations\<close>
(* ==================================================================================== *)

text \<open>
  We now define the semantics of enqueuing and dequing multiple buffers. This is useful
  when talking about concurrency: The other side may enqueue and/or dequeue multiple
  buffers at once, as observed by the one side. We therefore define the \verb+enqueue+
  and \verb+dequeue+ operation to operation on a set of buffers.
\<close>


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue-N Operation\<close>
(* ------------------------------------------------------------------------------------ *)


definition CleanQ_Set_enq_n_x :: "'a set \<Rightarrow> 'a CleanQ_Set_State \<Rightarrow> 'a CleanQ_Set_State"
  where "CleanQ_Set_enq_n_x B rb = rb \<lparr> SX := (SX rb) - B, TXY := (TXY rb) \<union> B \<rparr>"

definition CleanQ_Set_enq_n_y :: "'a set \<Rightarrow> 'a CleanQ_Set_State \<Rightarrow> 'a CleanQ_Set_State"
  where "CleanQ_Set_enq_n_y B rb = rb \<lparr> SY := (SY rb) - B, TYX := (TYX rb) \<union> B \<rparr>"


text \<open>
  We can inductively describe the effects on the enqueue N operation, by taking the 
\<close>

lemma CleanQ_Set_enq_n_x_ind:
  "CleanQ_Set_enq_n_x ({b} \<union> B) rb = CleanQ_Set_enq_x b (CleanQ_Set_enq_n_x B rb)"
  unfolding CleanQ_Set_enq_n_x_def CleanQ_Set_enq_x_def
  by(simp, meson Diff_insert)

lemma CleanQ_Set_enq_n_x_ind_list:
  "CleanQ_Set_enq_n_x (set (b # B)) rb = CleanQ_Set_enq_x b (CleanQ_Set_enq_n_x (set B) rb)"
  unfolding CleanQ_Set_enq_n_x_def CleanQ_Set_enq_x_def
  by(simp, meson Diff_insert)

lemma CleanQ_Set_enq_n_y_ind:
  "CleanQ_Set_enq_n_y ({b} \<union> B) rb = CleanQ_Set_enq_y b (CleanQ_Set_enq_n_y B rb)"
  unfolding CleanQ_Set_enq_n_y_def CleanQ_Set_enq_y_def
  by(simp, meson Diff_insert)

lemma CleanQ_Set_enq_n_y_ind_list:
  "CleanQ_Set_enq_n_y (set (b # B)) rb = CleanQ_Set_enq_y b (CleanQ_Set_enq_n_y (set B) rb)"
  unfolding CleanQ_Set_enq_n_y_def CleanQ_Set_enq_y_def
  by(simp, meson Diff_insert)


text \<open>
  The inductive definition can be commuted:
\<close>

lemma CleanQ_Set_enq_n_x_commute:
  "CleanQ_Set_enq_x b (CleanQ_Set_enq_n_x B rb) = CleanQ_Set_enq_n_x B (CleanQ_Set_enq_x b rb)"
  unfolding CleanQ_Set_enq_n_x_def CleanQ_Set_enq_x_def
  by (simp, metis Diff_insert Diff_insert2)

lemma CleanQ_Set_enq_n_y_commute:
  "CleanQ_Set_enq_y b (CleanQ_Set_enq_n_y B rb) = CleanQ_Set_enq_n_y B (CleanQ_Set_enq_y b rb)"
  unfolding CleanQ_Set_enq_n_y_def CleanQ_Set_enq_y_def
  by (simp, metis Diff_insert Diff_insert2)


text \<open>
  Like the single step enqueue operation, we can show that doing this multi-step, still
  preserves invariant I1 and I2..
\<close>

lemma CleanQ_Set_enq_n_x_I1 :
assumes I1_holds: "I1 rb K"  and  X_owned: "\<forall>b \<in> B. b \<in> SX rb" 
  shows "I1 (CleanQ_Set_enq_n_x B rb) K"
  using I1_holds X_owned unfolding CleanQ_Set_enq_n_x_def I1_def by auto

lemma CleanQ_Set_enq_n_y_I1 :
assumes I1_holds: "I1 rb K"  and  Y_owned: "\<forall>b \<in> B. b \<in> SY rb" 
  shows "I1 (CleanQ_Set_enq_n_y B rb) K"
  using I1_holds Y_owned unfolding CleanQ_Set_enq_n_y_def I1_def by auto

lemma CleanQ_Set_enq_n_x_I2 :
assumes I2_holds: "I2 rb"  and  X_owned: "\<forall>b \<in> B. b \<in> SX rb" 
  shows "I2 (CleanQ_Set_enq_n_x B rb)"
  using I2_holds X_owned unfolding CleanQ_Set_enq_n_x_def I2_def by auto

lemma CleanQ_Set_enq_n_y_I2 :
assumes I2_holds: "I2 rb"  and  Y_owned: "\<forall>b \<in> B. b \<in> SY rb" 
  shows "I2 (CleanQ_Set_enq_n_y B rb)"
  using I2_holds Y_owned unfolding CleanQ_Set_enq_n_y_def I2_def by auto


text \<open>
  Likewise, we can show that the \verb+CleanQ_Set_Invariants" are preserved by combining
  the lemmas above:
\<close>

lemma CleanQ_Set_enq_n_x_Invariants :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "\<forall>b \<in> B. b \<in> SX rb" 
  shows "CleanQ_Set_Invariants K (CleanQ_Set_enq_n_x B rb)"  
  using assms CleanQ_Set_enq_n_x_I1 CleanQ_Set_enq_n_x_I2 CleanQ_Set_Invariants_simp
  by blast

lemma CleanQ_Set_enq_n_y_Invariants :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "\<forall>b \<in> B. b \<in> SY rb" 
  shows "CleanQ_Set_Invariants K (CleanQ_Set_enq_n_y B rb)"  
  using assms CleanQ_Set_enq_n_y_I1 CleanQ_Set_enq_n_y_I2 CleanQ_Set_Invariants_simp 
  by blast


text \<open>
  We can now show that all buffers in the set $B$ are ending up in the transfer sets. 
  Not this is trivially true, as enqueue inserts those buffers into the transfer set. 
\<close>

lemma CleanQ_Set_enq_n_x_dst :
  "\<forall>b \<in> B. b \<in> TXY (CleanQ_Set_enq_n_x B rb)"
  by (simp add: CleanQ_Set_enq_n_x_def)

lemma CleanQ_Set_enq_n_y_dst :
  "\<forall> b \<in> B. b \<in> TYX (CleanQ_Set_enq_n_y B rb)"
  by (simp add: CleanQ_Set_enq_n_y_def)

text \<open>
  And further, all those buffers are not part of any other set. 
\<close>

lemma CleanQ_Set_enq_n_x_ndst1 :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "\<forall>b \<in> B. b \<in> SX rb" 
  shows "\<forall>b \<in> B. b \<notin> SY (CleanQ_Set_enq_n_x B rb)"
  using assms unfolding CleanQ_Set_Invariants_simp CleanQ_Set_enq_n_x_def by(auto)

lemma CleanQ_Set_enq_n_x_ndst2 :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "\<forall>b \<in> B. b \<in> SX rb" 
  shows "\<forall>b \<in> B. b \<notin> SX (CleanQ_Set_enq_n_x B rb)"
  using assms unfolding CleanQ_Set_Invariants_simp CleanQ_Set_enq_n_x_def by(auto)

lemma CleanQ_Set_enq_n_x_ndst3 :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "\<forall>b \<in> B. b \<in> SX rb" 
  shows "\<forall>b \<in> B. b \<notin> TYX (CleanQ_Set_enq_n_x B rb)"
  using assms unfolding CleanQ_Set_Invariants_simp CleanQ_Set_enq_n_x_def by(auto)

lemma CleanQ_Set_enq_n_y_ndst1 :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "\<forall>b \<in> B. b \<in> SY rb" 
  shows "\<forall>b \<in> B. b \<notin> SY (CleanQ_Set_enq_n_y B rb)"
  using assms unfolding CleanQ_Set_Invariants_simp CleanQ_Set_enq_n_y_def by(auto)

lemma CleanQ_Set_enq_n_y_ndst2 :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "\<forall>b \<in> B. b \<in> SY rb" 
  shows "\<forall>b \<in> B. b \<notin> SX (CleanQ_Set_enq_n_y B rb)"
  using assms unfolding CleanQ_Set_Invariants_simp CleanQ_Set_enq_n_y_def by(auto)

lemma CleanQ_Set_enq_n_y_ndst3 :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "\<forall>b \<in> B. b \<in> SY rb" 
  shows "\<forall>b \<in> B. b \<notin> TXY (CleanQ_Set_enq_n_y B rb)"
  using assms unfolding CleanQ_Set_Invariants_simp CleanQ_Set_enq_n_y_def by(auto)


text \<open>
  We can now combine the lemmas above to obtain the result of the multi-step 
  \verb+ enqueue+  operation.
\<close>

lemma CleanQ_Set_enq_n_x_result :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "\<forall>b \<in> B. b \<in> SX rb" 
    and CQ: "rb' = CleanQ_Set_enq_n_x B rb"
  shows "\<forall>b \<in> B. b \<in> TXY rb' \<and>  b \<notin> SX rb' \<and> b \<notin> SY rb' \<and> b \<notin> TYX rb'"
  using assms
  by (simp add: CleanQ_Set_enq_n_x_dst CleanQ_Set_enq_n_x_ndst1 CleanQ_Set_enq_n_x_ndst2 
                CleanQ_Set_enq_n_x_ndst3)


lemma CleanQ_Set_enq_n_y_result :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "\<forall>b \<in> B. b \<in> SY rb" 
    and CQ: "rb' = CleanQ_Set_enq_n_y B rb"
  shows "\<forall>b \<in> B. b \<in> TYX rb' \<and>  b \<notin> SX rb' \<and> b \<notin> SY rb' \<and> b \<notin> TXY rb'"
  using assms
  by (simp add: CleanQ_Set_enq_n_y_dst CleanQ_Set_enq_n_y_ndst1 CleanQ_Set_enq_n_y_ndst2 
                CleanQ_Set_enq_n_y_ndst3)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue-N Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  We now define the the effects of performing a \verb+dequeue+ of  multiple buffers at 
  once from the transfer set. 
\<close>

definition CleanQ_Set_deq_n_x :: "'a set \<Rightarrow> 'a CleanQ_Set_State \<Rightarrow> 'a CleanQ_Set_State"
  where "CleanQ_Set_deq_n_x B rb = \<lparr> SX = (SX rb) \<union> B, SY = (SY rb), TXY = (TXY rb),  
                                   TYX = (TYX rb) - B \<rparr>"

definition CleanQ_Set_deq_n_y :: "'a set \<Rightarrow> 'a CleanQ_Set_State \<Rightarrow> 'a CleanQ_Set_State"
  where "CleanQ_Set_deq_n_y B rb = \<lparr> SX = (SX rb), SY = (SY rb) \<union> B, 
                                   TXY = (TXY rb) - B, TYX = (TYX rb) \<rparr>"


text \<open>
  We can define this in an inductive way:
\<close>

lemma CleanQ_Set_deq_n_x_ind:
  "CleanQ_Set_deq_n_x ({b} \<union> B) rb = CleanQ_Set_deq_x b (CleanQ_Set_deq_n_x B rb)"
  unfolding CleanQ_Set_deq_n_x_def CleanQ_Set_deq_x_def  by auto

lemma CleanQ_Set_deq_n_x_ind_list:
  "CleanQ_Set_deq_n_x (set (b # B)) rb = CleanQ_Set_deq_x b (CleanQ_Set_deq_n_x (set B) rb)"
  unfolding CleanQ_Set_deq_n_x_def CleanQ_Set_deq_x_def  by auto

lemma CleanQ_Set_deq_n_y_ind:
  "CleanQ_Set_deq_n_y ({b} \<union> B) rb = CleanQ_Set_deq_y b (CleanQ_Set_deq_n_y B rb)"
  unfolding CleanQ_Set_deq_n_y_def CleanQ_Set_deq_y_def  by auto

lemma CleanQ_Set_deq_n_y_ind_list:
  "CleanQ_Set_deq_n_y (set (b # B)) rb = CleanQ_Set_deq_y b (CleanQ_Set_deq_n_y (set B) rb)"
  unfolding CleanQ_Set_deq_n_y_def CleanQ_Set_deq_y_def  by auto


text \<open>
  The multi-step \verb+dequeue_n+ operation perserves the invariant I1 and I2.
\<close>

lemma CleanQ_Set_deq_n_x_I1 :
assumes I1_holds : "I1 rb K"  and  TYX_owned: "\<forall>b \<in> B. b \<in> TYX rb"
  shows "I1 (CleanQ_Set_deq_n_x B rb) K"
  using assms unfolding CleanQ_Set_deq_n_x_def I1_def by(auto)

lemma CleanQ_Set_deq_n_y_I1 :
assumes I1_holds : "I1 rb K"  and  TXY_owned: "\<forall>b \<in> B. b \<in> TXY rb"
  shows "I1 (CleanQ_Set_deq_n_y B rb) K"
  using assms unfolding CleanQ_Set_deq_n_y_def I1_def by(auto)

lemma CleanQ_Set_deq_n_x_I2 :
assumes I2_holds : "I2 rb"  and  TYX_owned: "\<forall>b \<in> B. b \<in> TYX rb"
  shows "I2 (CleanQ_Set_deq_n_x B rb)"
  using assms unfolding CleanQ_Set_deq_n_x_def I2_def by(auto)

lemma CleanQ_Set_deq_n_y_I2 :
assumes I2_holds : "I2 rb"  and  TYX_owned: "\<forall>b \<in> B. b \<in> TXY rb"
  shows "I2 (CleanQ_Set_deq_n_y B rb)"
  using assms unfolding CleanQ_Set_deq_n_y_def I2_def by(auto)


text \<open>
  And we can combine the lemmas above to get show that the set invariant is preserved
  by the \verb+dequeue_n+ operation:
\<close>

lemma CleanQ_Set_deq_n_x_Invariants :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  TYX_owned: "\<forall>b \<in> B. b \<in> TYX rb"
  shows "CleanQ_Set_Invariants K (CleanQ_Set_deq_n_x B rb)" 
  using assms CleanQ_Set_deq_n_x_I1 CleanQ_Set_deq_n_x_I2 I_holds 
  unfolding CleanQ_Set_Invariants_def by(auto)


lemma CleanQ_Set_deq_n_y_Invariants :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  TXY_owned: "\<forall>b \<in> B. b \<in> TXY rb"
  shows "CleanQ_Set_Invariants K (CleanQ_Set_deq_n_y B rb)" 
  using assms CleanQ_Set_deq_n_y_I1 CleanQ_Set_deq_n_y_I2 I_holds 
  unfolding CleanQ_Set_Invariants_def by(auto)


text \<open>
  We can now talk about where the buffers end up when performing \verb+dequeue_n+ 
  This is by definition trivial.
\<close>

lemma CleanQ_Set_deq_n_x_dst :
  "\<forall> b \<in> B. b \<in> SX (CleanQ_Set_deq_n_x B rb)"
  unfolding CleanQ_Set_deq_n_x_def by(auto)

lemma CleanQ_Set_deq_n_y_dst :
  "\<forall> b \<in> B. b \<in> SY (CleanQ_Set_deq_n_y B rb)"
  unfolding CleanQ_Set_deq_n_y_def by(auto)

text \<open>
  And moreover show that the buffers do not end up in any other sets. 
\<close>

lemma CleanQ_Set_deq_n_x_ndst1 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "\<forall>b \<in> B. b \<in> TYX rb"
  shows "\<forall> b \<in> B. b \<notin> SY (CleanQ_Set_deq_n_x B rb)"
  using assms unfolding CleanQ_Set_deq_n_x_def CleanQ_Set_Invariants_simp by(auto)

lemma CleanQ_Set_deq_n_x_ndst2 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "\<forall>b \<in> B. b \<in> TYX rb"
  shows "\<forall> b \<in> B. b \<notin> TXY (CleanQ_Set_deq_n_x B rb)"
  using assms unfolding CleanQ_Set_deq_n_x_def CleanQ_Set_Invariants_simp by(auto)

lemma CleanQ_Set_deq_n_x_ndst3 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "\<forall>b \<in> B. b \<in> TYX rb"
  shows "\<forall> b \<in> B. b \<notin> TYX (CleanQ_Set_deq_n_x B rb)"
  using assms unfolding CleanQ_Set_deq_n_x_def CleanQ_Set_Invariants_simp by(auto)

lemma CleanQ_Set_deq_n_y_ndst1 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "\<forall>b \<in> B. b \<in> TXY rb"
  shows "\<forall> b \<in> B. b \<notin> SX (CleanQ_Set_deq_n_y B rb)"
  using assms unfolding CleanQ_Set_deq_n_y_def CleanQ_Set_Invariants_simp by(auto)

lemma CleanQ_Set_deq_n_y_ndst2 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "\<forall>b \<in> B. b \<in> TXY rb"
  shows "\<forall> b \<in> B. b \<notin> TXY (CleanQ_Set_deq_n_y B rb)"
  using assms unfolding CleanQ_Set_deq_n_y_def CleanQ_Set_Invariants_simp by(auto)

lemma CleanQ_Set_deq_n_y_ndst3 :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "\<forall>b \<in> B. b \<in> TXY rb"
  shows "\<forall> b \<in> B. b \<notin> TYX (CleanQ_Set_deq_n_y B rb)"
  using assms unfolding CleanQ_Set_deq_n_y_def CleanQ_Set_Invariants_simp by(auto)

text \<open>
  Finally, combining the lemmas above to obtain the result lemma of the operation.
\<close>

lemma CleanQ_Set_deq_n_x_result :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  YX_owned: "\<forall>b \<in> B. b \<in> TYX rb"
    and CQ: "rb' = CleanQ_Set_deq_n_x B rb"
    shows "\<forall>b \<in> B. b \<in> SX rb' \<and>  b \<notin> SY rb' \<and> b \<notin> TXY rb' \<and> b \<notin> TYX rb'"
  using assms
  by (simp add: CleanQ_Set_deq_n_x_dst CleanQ_Set_deq_n_x_ndst1 CleanQ_Set_deq_n_x_ndst2 
                CleanQ_Set_deq_n_x_ndst3)

lemma CleanQ_Set_deq_n_y_result :
assumes I_holds : "CleanQ_Set_Invariants K rb"  and  XY_owned: "\<forall>b \<in> B. b \<in> TXY rb"
    and CQ: "rb' = CleanQ_Set_deq_n_y B rb"
  shows "\<forall>b \<in> B. b \<in> SY rb' \<and>  b \<notin> SX rb' \<and> b \<notin> TXY rb' \<and> b \<notin> TYX rb'"
  using assms
  by (simp add: CleanQ_Set_deq_n_y_dst CleanQ_Set_deq_n_y_ndst1 CleanQ_Set_deq_n_y_ndst2 
                CleanQ_Set_deq_n_y_ndst3)



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Lemmas Summaries\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We define a few lemmas and lemma groups which simplify the proofs
\<close>

lemmas CleanQ_Set_ops_n = CleanQ_Set_deq_n_x_def CleanQ_Set_deq_n_y_def 
                          CleanQ_Set_enq_n_x_def CleanQ_Set_enq_n_y_def


(* ==================================================================================== *)
subsection \<open>Integration in SIMPL\<close>
(* ==================================================================================== *)

text \<open>
  We now integrate the the CleanQ Set Model into SIMPL. For each of the two operations,
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

lemma CleanQ_Set_enq_x_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<in> SX \<acute>SetRB \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_enq_x b \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  by(vcg, simp only: CleanQ_Set_enq_x_Invariants)

lemma CleanQ_Set_enq_y_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<in> SY \<acute>SetRB \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_enq_y b \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  by(vcg, simp only: CleanQ_Set_enq_y_Invariants)

text \<open>
  The same applies for the multi-step \verb+eneuque_n+ operation.
\<close>

lemma CleanQ_Set_enq_n_x_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> (\<forall>b \<in> B. b \<in> (SX \<acute>SetRB)) \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_enq_n_x B \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  apply(vcg) using CleanQ_Set_enq_n_x_Invariants by blast

lemma CleanQ_Set_enq_n_y_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> (\<forall>b \<in> B. b \<in> (SY \<acute>SetRB)) \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_enq_n_y B \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  apply(vcg) using CleanQ_Set_enq_n_y_Invariants by blast



text \<open>
  The enqueue operation  happens in two steps. The buffer element is removed
  from one set and added to a new set. We can express this as two sequential operations
  in the next lemma, where we show that the invariant is still preserved and that 
  the outcome is the same, as with the definition above.
\<close>

lemma CleanQ_Set_enq_x_two_step:
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<in> SX \<acute>SetRB \<rbrace>
        \<acute>SetRB :== \<acute>SetRB \<lparr> SX := (SX \<acute>SetRB) - {b} \<rparr> ;;
        \<acute>SetRB :== \<acute>SetRB \<lparr> TXY := (TXY \<acute>SetRB) \<union> {b} \<rparr>  
      \<lbrace> \<acute>SetRB = CleanQ_Set_enq_x b rb' \<and> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  by(vcg, auto simp:CleanQ_Set_Invariants_simp CleanQ_Set_enq_x_def)
  

lemma CleanQ_Set_enq_y_two_step:
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<in> SY \<acute>SetRB \<rbrace>
        \<acute>SetRB :== \<acute>SetRB \<lparr> SY := (SY \<acute>SetRB) - {b} \<rparr> ;;
        \<acute>SetRB :== \<acute>SetRB \<lparr> TYX := (TYX \<acute>SetRB) \<union> {b} \<rparr>  
      \<lbrace> \<acute>SetRB = CleanQ_Set_enq_y b rb' \<and> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  by(vcg, auto simp:CleanQ_Set_Invariants_simp CleanQ_Set_enq_y_def)
  


text \<open>
  Next we can define this conditionally, where we only execute the enqueue operation, 
  when we are owning the buffer. 
\<close>

lemma CleanQ_Set_enq_x_conditional :
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace> 
         IF b \<in> SX \<acute>SetRB THEN 
          \<acute>SetRB :== (CleanQ_Set_enq_x b \<acute>SetRB) 
         FI 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<notin> (SX \<acute>SetRB) \<rbrace>" 
  by(vcg, auto simp:CleanQ_Set_enq_x_Invariants CleanQ_Set_enq_x_def 
                    CleanQ_Set_Invariants_simp)
  

lemma CleanQ_Set_enq_y_conditional :
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace> 
         IF b \<in> SY \<acute>SetRB THEN 
          \<acute>SetRB :== (CleanQ_Set_enq_y b \<acute>SetRB) 
         FI 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<and>  b \<notin> (SY \<acute>SetRB) \<rbrace>" 
  by(vcg, auto simp:CleanQ_Set_enq_y_Invariants CleanQ_Set_enq_y_def 
                    CleanQ_Set_Invariants_simp)



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  We first show, that we can define a Hoare triple for the dequeue operations from both
  agents X and Y, and that in both cases the invariant is preserved.
\<close>

lemma CleanQ_Set_deq_x_preserves_invariants: 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<in> TYX \<acute>SetRB \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_deq_x b \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  by(vcg, simp only: CleanQ_Set_deq_x_Invariants)

lemma CleanQ_Set_deq_y_preserves_invariants: 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<in> TXY \<acute>SetRB \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_deq_y b \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  by(vcg, simp only: CleanQ_Set_deq_y_Invariants)


text \<open>
  The same applies for the multi-step \verb+eneuque_n+ operation.
\<close>

lemma CleanQ_Set_deq_n_x_preserves_invariants: 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> (\<forall> b \<in> B. b \<in> TYX \<acute>SetRB) \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_deq_n_x B \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  apply(vcg) using CleanQ_Set_deq_n_x_Invariants by blast

lemma CleanQ_Set_deq_n_y_preserves_invariants: 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> (\<forall> b \<in> B. b \<in> TXY \<acute>SetRB) \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_deq_n_y B \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  apply(vcg) using CleanQ_Set_deq_n_y_Invariants by blast


text \<open>
  The dequeue operation effectively happens in two steps. The buffer element is removed
  from one set and added to a new set. We can express this as two sequential operations
  in the next lemma, where we show that the invariant is still preserved and that 
  the outcome is the same, as with the definition above.
\<close>

lemma CleanQ_Set_deq_x_two_step:
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<in> TYX \<acute>SetRB \<rbrace>
        \<acute>SetRB :== \<acute>SetRB \<lparr> TYX := (TYX \<acute>SetRB) - {b} \<rparr> ;;
        \<acute>SetRB :== \<acute>SetRB \<lparr> SX := (SX \<acute>SetRB) \<union> {b} \<rparr>  
      \<lbrace> \<acute>SetRB = CleanQ_Set_deq_x b rb' \<and> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  by(vcg, simp add: CleanQ_Set_deq_x_def CleanQ_Set_Invariants_simp, auto)

lemma CleanQ_Set_deq_y_two_step:
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<in> TXY \<acute>SetRB \<rbrace>
        \<acute>SetRB :== \<acute>SetRB \<lparr> TXY := (TXY \<acute>SetRB) - {b} \<rparr> ;;
        \<acute>SetRB :== \<acute>SetRB \<lparr> SY := (SY \<acute>SetRB) \<union> {b} \<rparr>  
      \<lbrace> \<acute>SetRB = CleanQ_Set_deq_y b rb' \<and> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  by(vcg, simp add: CleanQ_Set_deq_y_def CleanQ_Set_Invariants_simp, auto)


text \<open>
  Next we can define this conditionally, where we only execute the enqueue operation, 
  when we are owning the buffer
\<close>

lemma CleanQ_Set_deq_x_conditional:
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace> 
         IF b \<in> TYX \<acute>SetRB THEN 
          \<acute>SetRB :== (CleanQ_Set_deq_x b \<acute>SetRB) 
         FI 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>" 
  by (vcg, meson CleanQ_Set_deq_x_Invariants)

lemma CleanQ_Set_deq_y_conditional:
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace> 
         IF b \<in> TXY \<acute>SetRB THEN 
          \<acute>SetRB :== (CleanQ_Set_deq_y b \<acute>SetRB) 
         FI 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>" 
  by (vcg, meson CleanQ_Set_deq_y_Invariants)




(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Combining Enqueue and Dequeue\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We can now combine the enqeueue and dequeue operations and pass a buffer around the 
  queue and back to the originator. We prove this by showing the state is the same.
\<close>

lemma CleanQ_Set_ops_combine : 
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<and> rb = \<acute>SetRB \<and> b \<in> SX \<acute>SetRB \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_enq_x b \<acute>SetRB) ;;
        \<acute>SetRB :== (CleanQ_Set_deq_y b \<acute>SetRB) ;;
        \<acute>SetRB :== (CleanQ_Set_enq_y b \<acute>SetRB) ;;
        \<acute>SetRB :== (CleanQ_Set_deq_x b \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<and> rb = \<acute>SetRB \<and> b \<in> SX \<acute>SetRB \<rbrace>" 
  apply(vcg, auto simp:CleanQ_Set_ops CleanQ_Set_Invariants_simp)
  using insert_absorb by fastforce
  


  
(* ==================================================================================== *)
subsection \<open>Strong and Weak Frame Conditions\<close>
(* ==================================================================================== *)

text \<open>
  We now define the strong and weak frame conditions for the CleanQ Set model. Those are
  used in the concurrency proofs. They define the set of operations the other side can
  do to the state of the queue system. 
\<close>


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Strong Frame Condition\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  The strong frame condition as we currently have it can be defined as shown below. The 
  essence of it is that no set changes which is not specifically defined to change.
\<close>

type_synonym 'a tuple = "'a set \<times> 'a set \<times> 'a set \<times> 'a set"

fun CleanQ_Set_Frame_Strong :: "'a tuple \<Rightarrow>'a tuple \<Rightarrow> bool"
  where "CleanQ_Set_Frame_Strong (sx',txy',sy',tyx') (sx,txy,sy,tyx) \<longleftrightarrow> 
                                          sx' = sx \<and> txy' = txy \<and> sy' = sy \<and> tyx' = tyx"

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Weak Frame Condition\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  For the concurrent case, we can not assume that the sets we do not explicitly modify by 
  an operation do not change and for this we have to weaken the frame condition that 
  e.g. when enqueueing from X the sets TXY, SY and TYX might change through actions of Y.
\<close>
definition  CleanQ_Set_Frame_Weak_x :: 
    "'a CleanQ_Set_State \<Rightarrow> 'a CleanQ_Set_State \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
    where "CleanQ_Set_Frame_Weak_x st' st dtxy dsy  \<longleftrightarrow> 
            SX st = SX st' \<and> SY st \<union> dsy = SY st'\<union> dtxy \<and>
            TXY st \<union> dtxy  = TXY st' \<and> TYX st = TYX st' \<union> dsy \<and>
            dsy \<inter> (SY st) = {} \<and> dtxy \<inter> TXY st = {} \<and> dsy \<inter> TXY st = {}"

definition  CleanQ_Set_Frame_Weak_y :: 
    "'a CleanQ_Set_State \<Rightarrow> 'a CleanQ_Set_State \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
    where "CleanQ_Set_Frame_Weak_y st' st dtyx dsx  \<longleftrightarrow> 
            SY st = SY st' \<and> SX st \<union> dsx = SX st'\<union> dtyx \<and>
            TYX st \<union> dtyx  = TYX st' \<and> TXY st = TXY st' \<union> dsx \<and>
            dsx \<inter> (SX st) = {} \<and> dtyx \<inter> TYX st = {} \<and> dsx \<inter> TYX st = {}  "


text \<open>
  We can now show, that enqueue  and dequeue operations fulfil the weak frame condition.
\<close>

lemma CleanQ_Set_Frame_Weak_x_enq:
  assumes I: "CleanQ_Set_Invariants K st'"  and  owns: "b \<in> SY st'"
    shows "CleanQ_Set_Frame_Weak_x st' (CleanQ_Set_enq_y b st') {} {b}"
  using assms unfolding CleanQ_Set_Frame_Weak_x_def CleanQ_Set_enq_y_def 
  by(auto simp:CleanQ_Set_Invariants_simp)

lemma CleanQ_Set_Frame_Weak_x_deq:
  assumes I: "CleanQ_Set_Invariants K st'"  and  owns: "b \<in> TXY st'"
    shows "CleanQ_Set_Frame_Weak_x st' (CleanQ_Set_deq_y b st') {b} {}"
  using assms unfolding CleanQ_Set_Frame_Weak_x_def CleanQ_Set_deq_y_def  by(auto)

lemma CleanQ_Set_Frame_Weak_y_enq:
  assumes I: "CleanQ_Set_Invariants K st'"  and  owns: "b \<in> SX st'"
    shows "CleanQ_Set_Frame_Weak_y st' (CleanQ_Set_enq_x b st') {} {b}"
  using assms unfolding CleanQ_Set_Frame_Weak_y_def CleanQ_Set_enq_x_def 
  by(auto simp:CleanQ_Set_Invariants_simp)

lemma CleanQ_Set_Frame_Weak_y_deq:
  assumes I: "CleanQ_Set_Invariants K st'"  and  owns: "b \<in> TYX st'"
    shows "CleanQ_Set_Frame_Weak_y st' (CleanQ_Set_deq_x b st') {b} {}"
  using assms unfolding CleanQ_Set_Frame_Weak_y_def CleanQ_Set_deq_x_def  by(auto)

text \<open>
  The weak frame conditions imply where the sets must come from. Note 
\<close>

lemma  CleanQ_Set_Frame_Weak_y_owns1:
  "CleanQ_Set_Frame_Weak_y st' st {} B \<Longrightarrow> B \<subseteq> SX st'"
  unfolding CleanQ_Set_Frame_Weak_y_def by(auto)

lemma  CleanQ_Set_Frame_Weak_y_owns2:
  "CleanQ_Set_Frame_Weak_y st' st A {} \<Longrightarrow> A \<subseteq> TYX st'"
  unfolding CleanQ_Set_Frame_Weak_y_def by(auto)

lemma  CleanQ_Set_Frame_Weak_y_owns3:
  "CleanQ_Set_Frame_Weak_y st' st A B \<Longrightarrow> A \<subseteq> TYX st' \<and> B \<subseteq> (SX st' \<union> A)"
  unfolding CleanQ_Set_Frame_Weak_y_def by(auto)

lemma  CleanQ_Set_Frame_Weak_x_owns1:
  "CleanQ_Set_Frame_Weak_x st' st {} B \<Longrightarrow> B \<subseteq> SY st'"
  unfolding CleanQ_Set_Frame_Weak_x_def by(auto)

lemma  CleanQ_Set_Frame_Weak_x_owns2:
  "CleanQ_Set_Frame_Weak_x st' st A {} \<Longrightarrow> A \<subseteq> TXY st'"
  unfolding CleanQ_Set_Frame_Weak_x_def by(auto)

lemma  CleanQ_Set_Frame_Weak_x_owns3:
  "CleanQ_Set_Frame_Weak_x st' st A B \<Longrightarrow> A \<subseteq> TXY st' \<and> B \<subseteq> (SY st' \<union> A)"
  unfolding CleanQ_Set_Frame_Weak_x_def by(auto)

text \<open>
  The weak frame condition for an \verb+enqueue+ or \verb+dequeue+ preserves I1. 
\<close>

lemma CleanQ_Set_enq_x_I1_weak:
assumes I: "CleanQ_Set_Invariants K st'" 
   and frame: "CleanQ_Set_Frame_Weak_y st' st {} {b}"
 shows "I1 st K"
  using assms unfolding I1_def CleanQ_Set_Frame_Weak_y_def CleanQ_Set_Invariants_def
  by(auto simp:CleanQ_Set_Invariants_simp)
  
lemma CleanQ_Set_enq_y_I1_weak:
assumes I: "CleanQ_Set_Invariants K st'" 
   and frame: "CleanQ_Set_Frame_Weak_x st' st {} {b}"
 shows "I1 st K"
  using assms unfolding I1_def CleanQ_Set_Frame_Weak_x_def CleanQ_Set_Invariants_def
  by(auto simp:CleanQ_Set_Invariants_simp)

lemma CleanQ_Set_deq_x_I1_weak:
assumes I: "CleanQ_Set_Invariants K st'" 
   and frame: "CleanQ_Set_Frame_Weak_y st' st {b} {}"
 shows "I1 st K"
  using assms unfolding I1_def CleanQ_Set_Frame_Weak_y_def CleanQ_Set_Invariants_def
  by(auto simp:CleanQ_Set_Invariants_simp)

lemma CleanQ_Set_deq_y_I1_weak:
assumes I: "CleanQ_Set_Invariants K st'"
   and frame: "CleanQ_Set_Frame_Weak_x st' st {b} {}"
 shows "I1 st K"
  using assms unfolding I1_def CleanQ_Set_Frame_Weak_x_def CleanQ_Set_Invariants_def
  by(auto simp:CleanQ_Set_Invariants_simp)

text \<open>
  The weak frame condition for an \verb+enqueue+ or \verb+dequeue+ preserves I2. 
\<close>

lemma CleanQ_Set_enq_x_I2_weak:
assumes I: "CleanQ_Set_Invariants K st'" 
   and frame: "CleanQ_Set_Frame_Weak_y st' st {} {b}"
 shows "I2 st"
  using assms unfolding I2_def CleanQ_Set_Frame_Weak_y_def CleanQ_Set_Invariants_def
  by(auto)  

lemma CleanQ_Set_deq_x_I2_weak:
assumes I: "CleanQ_Set_Invariants K st'" 
   and frame: "CleanQ_Set_Frame_Weak_y st' st {b} {}" 
 shows "I2 st"
  using assms unfolding I2_def CleanQ_Set_Frame_Weak_y_def CleanQ_Set_Invariants_def
  by(auto)  

lemma CleanQ_Set_enq_y_I2_weak:
assumes I: "CleanQ_Set_Invariants K st'" 
   and frame: "CleanQ_Set_Frame_Weak_x st' st {} {b}"
 shows "I2 st"
  using assms unfolding I2_def CleanQ_Set_Frame_Weak_x_def CleanQ_Set_Invariants_def
  by(auto)  

lemma CleanQ_Set_deq_y_I2_weak:
assumes I: "CleanQ_Set_Invariants K st'" 
   and frame: "CleanQ_Set_Frame_Weak_x st' st {b} {}" 
 shows "I2 st"
  using assms unfolding I2_def CleanQ_Set_Frame_Weak_x_def CleanQ_Set_Invariants_def
  by(auto)  



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Generic Frame Conditions\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  Generically, the frame condition is the equivalence of sets, that are not being talked
  about.
\<close>

fun frame_strong ::
  "'a \<times> 'b \<times> 'c \<times> 'd \<Rightarrow>'a \<times> 'b \<times> 'c \<times> 'd \<Rightarrow> bool"
  where "frame_strong (A',B',C',D') (A,B,C,D) \<longleftrightarrow> A' = A \<and> B' = B \<and> C' = C \<and> D' = D"


text \<open>@{term D} is in its initial state, but elements may move from @{term A} to @{term B}
  and from @{term B} to @{term C}.\<close>

fun frame_weak ::
  "'a set \<times> 'a set \<times> 'a set \<times> 'a set \<Rightarrow> 'a set \<times> 'a set \<times> 'a set \<times> 'a set \<Rightarrow> bool"
  where "frame_weak (A',B',C',D') (A,B,C,D) \<longleftrightarrow>  D' = D \<and> (\<exists>\<Delta>AB \<Delta>BC.
    A \<union> \<Delta>AB = A'\<and>        
    B \<union> \<Delta>BC = B' \<union> \<Delta>AB \<and>    
    C = C' \<union> \<Delta>BC \<and>    
    A \<inter> \<Delta>AB = {} \<and>          
    A \<inter> \<Delta>BC = {} \<and>
    B \<inter> \<Delta>BC = {} )"


text \<open>
  We can show equivalent to the frame conditions above
\<close>
lemma CleanQ_Set_frame_weak_equiv_x:
  "frame_weak (TXY st', SY st', TYX st', SX st' ) (TXY st, SY st, TYX st, SX st)
                              \<longleftrightarrow> (\<exists>\<Delta>AB \<Delta>BC. CleanQ_Set_Frame_Weak_x st' st \<Delta>AB \<Delta>BC)"
  unfolding frame_weak.simps CleanQ_Set_Frame_Weak_x_def 
  by (metis Int_commute)
  

lemma CleanQ_Set_frame_weak_equiv_y:
  "frame_weak (TYX st', SX st', TXY st', SY st' ) (TYX st, SX st, TXY st, SY st) 
                             \<longleftrightarrow> (\<exists>\<Delta>AB \<Delta>BC. CleanQ_Set_Frame_Weak_y st' st \<Delta>AB \<Delta>BC)"
  unfolding frame_weak.simps CleanQ_Set_Frame_Weak_y_def
  by (metis Int_commute)

text \<open>
  As a first step we have to show that the strong frame condition implies the weak one.
\<close>

lemma frame_s_w:
  "frame_strong (A',B',C',D') (A,B,C,D) \<Longrightarrow> frame_weak (A',B',C',D') (A,B,C,D)"
  unfolding frame_strong.simps frame_weak.simps by(blast)


text \<open>The weak frame condition for an enqueue from @{term D} into @{term A} preserves
  invariant 1.\<close>

lemma CleanQ_Set_enq_x_I1_weak2:
  fixes st st' K b
  assumes I: "CleanQ_Set_Invariants K st'"
      and frame: "frame_weak (TXY st' \<union> {b},SY st', TYX st', SX st' - {b})
                             (TXY st, SY st, TYX st, SX st)"
      and owns: "b \<in> SX st'"
    shows "I1 st K"
  using assms subst unfolding frame_weak.simps I1_def
  by (smt CleanQ_Set_Invariants_def I1_def Un_insert_right insert_Diff 
          sup_aci(3) sup_assoc sup_bot.comm_neutral)

lemma CleanQ_Set_enq_y_I1_weak2:
  fixes st st' K b
  assumes I: "CleanQ_Set_Invariants K st'"
      and frame: "frame_weak (TYX st' \<union> {b},SX st', TXY st', SY st' - {b})
                             (TYX st, SX st, TXY st, SY st)"
      and owns: "b \<in> SY st'"
    shows "I1 st K"
  using assms subst unfolding frame_weak.simps I1_def
  by (smt CleanQ_Set_Invariants_def I1_def Un_insert_right insert_Diff sup_aci(3)
          sup_assoc sup_bot.comm_neutral)

lemma CleanQ_Set_enq_x_I2_weak2:
  fixes st st' K b
  assumes I: "CleanQ_Set_Invariants K st'"
      and frame: "frame_weak (TXY st' \<union> {b},SY st', TYX st', SX st' - {b} )
                             (TXY st, SY st, TYX st, SX st)"
      and owns: "b \<in> SX st'"
    shows "I2 st"
proof(unfold I2_def, intro conjI)
  from frame obtain \<Delta>AB \<Delta>BC where
    fA: "(TXY st' \<union> {b}) = \<Delta>AB \<union> TXY st" and
    fB: "SY st' \<union> \<Delta>AB = \<Delta>BC \<union> SY st" and
    fC: "TYX st' \<union> \<Delta>BC = TYX st" and
    fD: "SX st' - {b} = SX st" and
    dAB: "TXY st \<inter> \<Delta>AB = {}" and
    dAC: "TXY st \<inter> \<Delta>BC = {}" and
    dBC: "SY st \<inter> \<Delta>BC = {}"
    by (metis (no_types, lifting) frame_weak.simps sup.commute)

  from fA have ss_\<Delta>AB: "\<Delta>AB \<subseteq> TXY st' \<union> {b}" by(auto)
  with fB have ss_\<Delta>BC: "\<Delta>BC \<subseteq> TXY st' \<union> SY st' \<union> {b}" by(auto)

  from fA have ss_A: "TXY st \<subseteq> TXY st' \<union> {b}" by(auto)
  from fB ss_\<Delta>AB have ss_B: "SY st \<subseteq> TXY st' \<union> SY st' \<union> {b}" by(auto)
  from fC ss_\<Delta>BC have ss_C: "TYX st \<subseteq> TXY st' \<union> SY st' \<union> TYX st' \<union> {b}" by(auto)

  from I ss_A show "SX st \<inter> TXY st = {}" 
    by(unfold fD[symmetric], auto simp:CleanQ_Set_Invariants_simp)
  from I ss_B show "SX st \<inter> SY st = {}" 
    by(unfold fD[symmetric], auto simp:CleanQ_Set_Invariants_simp)
  from I ss_C show "SX st \<inter> TYX st = {}" 
    by(unfold fD[symmetric], auto simp:CleanQ_Set_Invariants_simp)

  from fC have "SY st \<inter> TYX st = SY st \<inter> (TYX st' \<union> \<Delta>BC)" by(simp)
  also have "... = (SY st \<inter> TYX st') \<union> (SY st \<inter> \<Delta>BC)" by(auto)
  also {
    from ss_B have "SY st \<inter> TYX st' \<subseteq> (TXY st' \<union> SY st' \<union> {b}) \<inter> TYX st'" by(auto)
    also from I owns have "... = {}" by(auto simp:CleanQ_Set_Invariants_simp)
    finally have "(SY st \<inter> TYX st') \<union> (SY st \<inter> \<Delta>BC) = SY st \<inter> \<Delta>BC" by(simp)
  }
  txt \<open>@{term "SY st \<inter> \<Delta>BC = {}"} is essential\<close>
  finally have "SY st \<inter> TYX st = SY st \<inter> \<Delta>BC" .
  with dBC show "SY st \<inter> TYX st = {}" by(simp)

  from fC have "TXY st \<inter> TYX st = TXY st \<inter> (TYX st' \<union> \<Delta>BC)" by(simp)
  also have "... = (TXY st \<inter> TYX st') \<union> (TXY st \<inter> \<Delta>BC)" by(auto)
  also {
    from ss_A have "TXY st \<inter> TYX st' \<subseteq> (TXY st' \<union> {b}) \<inter> TYX st'" by(auto)
    also from I owns have "... = {}" by(auto simp:CleanQ_Set_Invariants_simp)
    finally have "(TXY st \<inter> TYX st') \<union> (TXY st \<inter> \<Delta>BC) = TXY st \<inter> \<Delta>BC" by(simp)
  }
  txt \<open>@{term "TXY st \<inter> \<Delta>BC = {}"} is essential\<close>
  finally have "TXY st \<inter> TYX st = TXY st \<inter> \<Delta>BC" .
  with dAC show "TXY st \<inter> TYX st = {}" by(simp add:CleanQ_Set_Invariants_simp)

  from fB have "TXY st \<inter> (\<Delta>BC \<union> SY st) = TXY st \<inter> (SY st' \<union> \<Delta>AB)" by(simp)
  also have "... = (TXY st \<inter> SY st') \<union> (TXY st \<inter> \<Delta>AB)" by(auto)
  also {
    from ss_A have "TXY st \<inter> SY st' \<subseteq> (TXY st' \<union> {b}) \<inter> SY st'" by(auto)
    also from I owns have "... = {}" by(auto simp:CleanQ_Set_Invariants_simp)
    finally have "(TXY st \<inter> SY st') \<union> (TXY st \<inter> \<Delta>AB) = TXY st \<inter> \<Delta>AB" by(simp)
  }
  txt \<open>@{term "TXY st \<inter> \<Delta>AB = {}"} is essential, given @{term "TXY st \<inter> \<Delta>BC = {}"}.\<close>
  finally have "TXY st \<inter> (\<Delta>BC \<union> SY st) = TXY st \<inter> \<Delta>AB" .
  with dAB show "SY st \<inter> TXY st = {}" by auto
qed

lemma CleanQ_Set_enq_y_I2_weak2:
  fixes st st' K b
  assumes I: "CleanQ_Set_Invariants K st'"
      and frame: "frame_weak (TYX st' \<union> {b},SX st', TXY st', SY st' - {b}) 
                             (TYX st, SX st, TXY st, SY st)"
      and owns: "b \<in> SY st'"
    shows "I2 st"
proof(unfold I2_def, intro conjI)
  from frame obtain \<Delta>AB \<Delta>BC where
    fA: "(TYX st' \<union> {b}) = \<Delta>AB \<union> TYX st" and
    fB: "SX st' \<union> \<Delta>AB = \<Delta>BC \<union> SX st" and
    fC: "TXY st' \<union> \<Delta>BC = TXY st" and
    fD: "SY st' - {b} = SY st" and
    dAB: "TYX st \<inter> \<Delta>AB = {}" and
    dAC: "TYX st \<inter> \<Delta>BC = {}" and
    dBC: "SX st \<inter> \<Delta>BC = {}"
    by (metis (no_types, lifting) frame_weak.simps sup.commute)

  from fA have ss_\<Delta>AB: "\<Delta>AB \<subseteq> TYX st' \<union> {b}" by(auto)
  with fB have ss_\<Delta>BC: "\<Delta>BC \<subseteq> TYX st' \<union> SX st' \<union> {b}" by(auto)

  from fA have ss_A: "TYX st \<subseteq> TYX st' \<union> {b}" by(auto)
  from fB ss_\<Delta>AB have ss_B: "SX st \<subseteq> TYX st' \<union> SX st' \<union> {b}" by(auto)
  from fC ss_\<Delta>BC have ss_C: "TXY st \<subseteq> TYX st' \<union> SX st' \<union> TXY st' \<union> {b}" by(auto)

  from I ss_A show "SY st \<inter> TYX st = {}" 
    by(unfold fD[symmetric], auto simp:CleanQ_Set_Invariants_simp)
  from I ss_B show "SX st \<inter> SY st = {}" 
    by(unfold fD[symmetric], auto simp:CleanQ_Set_Invariants_simp)
  from I ss_C show "SY st \<inter> TXY st = {}" 
    by(unfold fD[symmetric], auto simp:CleanQ_Set_Invariants_simp)

  from fC have "SX st \<inter> TXY st = SX st \<inter> (TXY st' \<union> \<Delta>BC)" by(simp)
  also have "... = (SX st \<inter> TXY st') \<union> (SX st \<inter> \<Delta>BC)" by(auto)
  also {
    from ss_B have "SX st \<inter> TXY st' \<subseteq> (TYX st' \<union> SX st' \<union> {b}) \<inter> TXY st'" by(auto)
    also from I owns have "... = {}" by(auto simp:CleanQ_Set_Invariants_simp)
    finally have "(SX st \<inter> TXY st') \<union> (SX st \<inter> \<Delta>BC) = SX st \<inter> \<Delta>BC" by(simp)
  }
  txt \<open>@{term "SX st \<inter> \<Delta>BC = {}"} is essential\<close>
  finally have "SX st \<inter> TXY st = SX st \<inter> \<Delta>BC" .
  with dBC show "SX st \<inter> TXY st = {}" by(simp)

  from fC have "TYX st \<inter> TXY st = TYX st \<inter> (TXY st' \<union> \<Delta>BC)" by(simp)
  also have "... = (TYX st \<inter> TXY st') \<union> (TYX st \<inter> \<Delta>BC)" by(auto)
  also {
    from ss_A have "TYX st \<inter> TXY st' \<subseteq> (TYX st' \<union> {b}) \<inter> TXY st'" by(auto)
    also from I owns have "... = {}" by(auto simp:CleanQ_Set_Invariants_simp)
    finally have "(TYX st \<inter> TXY st') \<union> (TYX st \<inter> \<Delta>BC) = TYX st \<inter> \<Delta>BC" by(simp)
  }
  txt \<open>@{term "TYX st \<inter> \<Delta>BC = {}"} is essential\<close>
  finally have "TYX st \<inter> TXY st = TYX st \<inter> \<Delta>BC" .
  with dAC show "TXY st \<inter> TYX st = {}" by(blast)

  from fB have "TYX st \<inter> (\<Delta>BC \<union> SX st) = TYX st \<inter> (SX st' \<union> \<Delta>AB)" by(simp)
  also have "... = (TYX st \<inter> SX st') \<union> (TYX st \<inter> \<Delta>AB)" by(auto)
  also {
    from ss_A have "TYX st \<inter> SX st' \<subseteq> (TYX st' \<union> {b}) \<inter> SX st'" by(auto)
    also from I owns have "... = {}" by(auto simp:CleanQ_Set_Invariants_simp)
    finally have "(TYX st \<inter> SX st') \<union> (TYX st \<inter> \<Delta>AB) = TYX st \<inter> \<Delta>AB" by(simp)
  }
  txt \<open>@{term "TYX st \<inter> \<Delta>AB = {}"} is essential, given @{term "TYX st \<inter> \<Delta>BC = {}"}.\<close>
  finally have "TYX st \<inter> (\<Delta>BC \<union> SX st) = TYX st \<inter> \<Delta>AB" .
  with dAB show "SX st \<inter> TYX st = {}" by auto
qed



text \<open>
  Similar to enqueue we also have to show the same for dequeue and the weak frame condition
\<close>


lemma CleanQ_Set_deq_x_weak_I1:
  fixes st st' K b
  assumes I: "CleanQ_Set_Invariants K st'"
      and frame: "frame_weak (TXY st',SY st', TYX st' - {b}, SX st' \<union> {b}) 
                             (TXY st, SY st, TYX st, SX st)"
      and owns: "b \<in> TYX st'"
    shows "I1 st K"
  using assms subst unfolding frame_weak.simps I1_def
    by (smt CleanQ_Set_Invariants_def I1_def Un_insert_right insert_Diff 
          sup_aci(3) sup_assoc sup_bot.comm_neutral)

lemma CleanQ_Set_deq_y_weak_I1:
  fixes st st' K b
  assumes I: "CleanQ_Set_Invariants K st'"
      and frame: "frame_weak (TYX st',SX st', TXY st' - {b}, SY st' \<union> {b}) 
                             (TYX st, SX st, TXY st, SY st)"
      and owns: "b \<in> TXY st'"
    shows "I1 st K"
  using assms subst unfolding frame_weak.simps I1_def
  by (smt CleanQ_Set_Invariants_def I1_def Un_insert_right insert_Diff 
          sup_aci(3) sup_assoc sup_bot.comm_neutral)

lemma CleanQ_Set_deq_x_weak_I2:
  fixes st st' K b
  assumes I: "CleanQ_Set_Invariants K st'"
      and frame: "frame_weak (TXY st',SY st', TYX st' - {b},  SX st' \<union> {b}) 
                             (TXY st, SY st, TYX st, SX st)"
      and owns: "b \<in> TYX st'"
    shows "I2 st"
proof(unfold I2_def, intro conjI)
  from frame obtain \<Delta>AB \<Delta>BC where
    fA: "TXY st' = \<Delta>AB \<union> TXY st" and
    fB: "SY st' \<union> \<Delta>AB = \<Delta>BC \<union> SY st" and
    fC: "(TYX st' - {b}) \<union> \<Delta>BC = TYX st" and
    fD: "SX st' \<union> {b} = SX st" and
    dAB: "TXY st \<inter> \<Delta>AB = {}" and
    dAC: "TXY st \<inter> \<Delta>BC = {}" and
    dBC: "SY st \<inter> \<Delta>BC = {}"
    by (metis (no_types, lifting) frame_weak.simps sup.commute)

  from fA have ss_\<Delta>AB: "\<Delta>AB \<subseteq> TXY st'" by(auto)
  with fB have ss_\<Delta>BC: "\<Delta>BC \<subseteq> TXY st' \<union> SY st'" by(auto)

  from fA have ss_A: "TXY st \<subseteq> TXY st'" by(auto)
  from fB ss_\<Delta>AB have ss_B: "SY st \<subseteq> TXY st' \<union> SY st'" by(auto)
  from fC ss_\<Delta>BC have ss_C: "TYX st \<subseteq> TXY st' \<union> SY st' \<union> (TYX st' - {b})" by(auto)

  from I owns ss_A show "SX st \<inter> TXY st = {}" 
    by(unfold fD[symmetric],  auto simp:CleanQ_Set_Invariants_simp)
  from I owns ss_B show "SX st \<inter> SY st = {}"
    by(unfold fD[symmetric],  auto simp:CleanQ_Set_Invariants_simp)
  from I owns ss_C show "SX st \<inter> TYX st = {}"
    by(unfold fD[symmetric],  auto simp:CleanQ_Set_Invariants_simp)

  from fC have "SY st \<inter> TYX st = SY st \<inter> ((TYX st' - {b}) \<union> \<Delta>BC)" by(simp)
  also have "... = (SY st \<inter> (TYX st' - {b})) \<union> (SY st \<inter> \<Delta>BC)" by(auto)
  also {
    from ss_B have "SY st \<inter> (TYX st' - {b}) \<subseteq> (TXY st' \<union> SY st') \<inter> TYX st'" by(auto)
    also from I have "... = {}" by( auto simp:CleanQ_Set_Invariants_simp)
    finally have "(SY st \<inter> (TYX st' - {b})) \<union> (SY st \<inter> \<Delta>BC) = SY st \<inter> \<Delta>BC" by(simp)
  }
  txt \<open>@{term "SY st \<inter> \<Delta>BC = {}"} is essential\<close>
  finally have "SY st \<inter> TYX st = SY st \<inter> \<Delta>BC" .
  with dBC show "SY st \<inter> TYX st = {}" by simp

  from fC have "TXY st \<inter> TYX st = TXY st \<inter> ((TYX st' - {b}) \<union> \<Delta>BC)" by simp
  also have "... = (TXY st \<inter> (TYX st' - {b})) \<union> (TXY st \<inter> \<Delta>BC)" by blast
  also {
    from ss_A have "TXY st \<inter> (TYX st' - {b}) \<subseteq> (TXY st' \<union> {b}) \<inter> (TYX st' - {b})" by(auto)
    also from I have "... = {}" by( auto simp:CleanQ_Set_Invariants_simp)
    finally have "(TXY st \<inter> (TYX st' - {b})) \<union> (TXY st \<inter> \<Delta>BC) = TXY st \<inter> \<Delta>BC" by(simp)
  }
  txt \<open>@{term "TXY st \<inter> \<Delta>BC = {}"} is essential\<close>
  finally have "TXY st \<inter> TYX st = TXY st \<inter> \<Delta>BC" .
  with dAC show "TXY st \<inter> TYX st = {}" by(simp)

  from fB have "TXY st \<inter> (\<Delta>BC \<union> SY st) = TXY st \<inter> (SY st' \<union> \<Delta>AB)" by(simp)
  also have "... = (TXY st \<inter> SY st') \<union> (TXY st \<inter> \<Delta>AB)" by(auto)
  also {
    from ss_A have "TXY st \<inter> SY st' \<subseteq> (TXY st' \<union> {b}) \<inter> SY st'" by(auto)
    also from I owns have "... = {}" by( auto simp:CleanQ_Set_Invariants_simp)
    finally have "(TXY st \<inter> SY st') \<union> (TXY st \<inter> \<Delta>AB) = TXY st \<inter> \<Delta>AB" by(simp)
  }
  txt \<open>@{term "TXY st \<inter> \<Delta>AB = {}"} is essential, given @{term "TXY st \<inter> \<Delta>BC = {}"}.\<close>
  finally have "TXY st \<inter> (\<Delta>BC \<union> SY st) = TXY st \<inter> \<Delta>AB" .
  with dAB show " SY st \<inter> TXY st = {}" by(auto)
qed


lemma CleanQ_Set_deq_y_weak_I2:
  fixes st st' K b
  assumes I: "CleanQ_Set_Invariants K st'"
      and frame: "frame_weak (TYX st',SX st', TXY st' - {b}, SY st' \<union> {b}) 
                             (TYX st, SX st, TXY st, SY st)"
      and owns: "b \<in> TXY st'"
    shows "I2 st"
proof(unfold I2_def, intro conjI)
  from frame obtain \<Delta>AB \<Delta>BC where
    fA: "TYX st' = \<Delta>AB \<union> TYX st" and
    fB: "SX st' \<union> \<Delta>AB = \<Delta>BC \<union> SX st" and
    fC: "(TXY st' - {b}) \<union> \<Delta>BC = TXY st" and
    fD: "SY st' \<union> {b} = SY st" and
    dAB: "TYX st \<inter> \<Delta>AB = {}" and
    dAC: "TYX st \<inter> \<Delta>BC = {}" and
    dBC: "SX st \<inter> \<Delta>BC = {}"
    by (metis (no_types, lifting) frame_weak.simps sup.commute)

  from fA have ss_\<Delta>AB: "\<Delta>AB \<subseteq> TYX st'" by(auto)
  with fB have ss_\<Delta>BC: "\<Delta>BC \<subseteq> TYX st' \<union> SX st'" by(auto)

  from fA have ss_A: "TYX st \<subseteq> TYX st'" by(auto)
  from fB ss_\<Delta>AB have ss_B: "SX st \<subseteq> TYX st' \<union> SX st'" by(auto)
  from fC ss_\<Delta>BC have ss_C: "TXY st \<subseteq> TYX st' \<union> SX st' \<union> (TXY st' - {b})" by(auto)

  from I owns ss_A show "SY st \<inter> TYX st = {}" 
    by(unfold fD[symmetric], auto simp:CleanQ_Set_Invariants_simp)
  from I owns ss_B show "SX st \<inter> SY st = {}" 
    by(unfold fD[symmetric], auto simp:CleanQ_Set_Invariants_simp)
  from I owns ss_C show "SY st \<inter> TXY st = {}" 
    by(unfold fD[symmetric], auto simp:CleanQ_Set_Invariants_simp)

  from fC have "SX st \<inter> TXY st = SX st \<inter> ((TXY st' - {b}) \<union> \<Delta>BC)" by(simp)
  also have "... = (SX st \<inter> (TXY st' - {b})) \<union> (SX st \<inter> \<Delta>BC)" by(auto)
  also {
    from ss_B have "SX st \<inter> (TXY st' - {b}) \<subseteq> (TYX st' \<union> SX st') \<inter> TXY st'" by(auto)
    also from I have "... = {}" by(auto simp:CleanQ_Set_Invariants_simp)
    finally have "(SX st \<inter> (TXY st' - {b})) \<union> (SX st \<inter> \<Delta>BC) = SX st \<inter> \<Delta>BC" by(simp)
  }
  txt \<open>@{term "SX st \<inter> \<Delta>BC = {}"} is essential\<close>
  finally have "SX st \<inter> TXY st = SX st \<inter> \<Delta>BC" .
  with dBC show "SX st \<inter> TXY st = {}" by simp

  from fC have "TYX st \<inter> TXY st = TYX st \<inter> ((TXY st' - {b}) \<union> \<Delta>BC)" by simp
  also have "... = (TYX st \<inter> (TXY st' - {b})) \<union> (TYX st \<inter> \<Delta>BC)" by blast
  also {
    from ss_A have "TYX st \<inter> (TXY st' - {b}) \<subseteq> (TYX st' \<union> {b}) \<inter> (TXY st' - {b})" by(auto)
    also from I have "... = {}" by(auto simp:CleanQ_Set_Invariants_simp)
    finally have "(TYX st \<inter> (TXY st' - {b})) \<union> (TYX st \<inter> \<Delta>BC) = TYX st \<inter> \<Delta>BC" by(simp)
  }
  txt \<open>@{term "TYX st \<inter> \<Delta>BC = {}"} is essential\<close>
  finally have "TYX st \<inter> TXY st = TYX st \<inter> \<Delta>BC" .
  with dAC show "TXY st \<inter> TYX st = {}" by auto

  from fB have "TYX st \<inter> (\<Delta>BC \<union> SX st) = TYX st \<inter> (SX st' \<union> \<Delta>AB)" by(simp)
  also have "... = (TYX st \<inter> SX st') \<union> (TYX st \<inter> \<Delta>AB)" by(auto)
  also {
    from ss_A have "TYX st \<inter> SX st' \<subseteq> (TYX st' \<union> {b}) \<inter> SX st'" by(auto)
    also from I owns have "... = {}" by(auto simp:CleanQ_Set_Invariants_simp)
    finally have "(TYX st \<inter> SX st') \<union> (TYX st \<inter> \<Delta>AB) = TYX st \<inter> \<Delta>AB" by(simp)
  }
  txt \<open>@{term "TYX st \<inter> \<Delta>AB = {}"} is essential, given @{term "TYX st \<inter> \<Delta>BC = {}"}.\<close>
  finally have "TYX st \<inter> (\<Delta>BC \<union> SX st) = TYX st \<inter> \<Delta>AB" .
  with dAB show " SX st \<inter> TYX st = {}" by(auto)
qed



(* ==================================================================================== *)
subsection \<open>Integration in COMPLEX\<close>
(* ==================================================================================== *)

text \<open>
  Next, we can formulate the \verb+enqueue+ and \verb+dequeue+ operations in COMPLEX.
\<close>

(* 

  have two threads. 
    X: call enqx | deqx
    Y: call enqy | deqy


lemma
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/\<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>\<^esub>
    COBEGIN 
         \<lbrace>  b \<in> SX \<acute>SetRB \<rbrace> \<acute>SetRB := (CleanQ_Set_enq_x b \<acute>SetRB) \<lbrace>True\<rbrace>, \<lbrace>True\<rbrace>
       \<parallel> \<lbrace>  b2 \<in> SY \<acute>SetRB \<rbrace> \<acute>SetRB := (CleanQ_Set_enq_y b2 \<acute>SetRB) \<lbrace>True\<rbrace>, \<lbrace>True\<rbrace>
    COEND \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>,\<lbrace> True\<rbrace>"

  
          apply simp_all apply auto
  done



lemma
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/{True}\<^esub>
    COBEGIN test_guard \<lbrace>True\<rbrace>,\<lbrace>True\<rbrace>
         \<parallel> \<lbrace>True\<rbrace> \<acute>y:=0 \<lbrace>True\<rbrace>, \<lbrace>True\<rbrace>
    COEND \<lbrace>True\<rbrace>,\<lbrace>True\<rbrace>"
  unfolding test_guard_def
  apply oghoare (*11 subgoals*)
           apply simp_all
  done
*)

definition CleanQ_Set_Hoare ::  "('s, 'p, 'f) com"
  where "CleanQ_Set_Hoare = Parallel []"



(* ==================================================================================== *)
subsection \<open>Pre- and post- conditions\<close>
(* ==================================================================================== *)

definition CleanQ_Set_deq_x_pre :: 
  "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_deq_x_pre K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> TYX rb }"

definition CleanQ_Set_deq_x_post :: 
  "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_deq_x_post K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> SX rb }"

definition CleanQ_Set_deq_y_pre :: 
  "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_deq_y_pre K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> TXY rb }"

definition CleanQ_Set_deq_y_post :: 
  "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_deq_y_post K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> SY rb }"


definition CleanQ_Set_enq_x_pre :: 
  "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_enq_x_pre K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> SX rb }"

definition CleanQ_Set_enq_x_post :: 
  "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_enq_x_post K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> TXY rb }"

definition CleanQ_Set_enq_y_pre :: 
  "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_enq_y_pre K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> SY rb }"

definition CleanQ_Set_enq_y_post :: 
  "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_enq_y_post K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> TYX rb }"


(*<*)
end
(*>*)