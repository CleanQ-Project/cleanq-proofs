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
begin
(*>*)

text \<open>
  We now define the model state, its invariants and state transitions. Followed by proofs 
  using Owicki-Gries (OG)
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
  RB_'  :: "nat CleanQ_Set_State"
  B_'   ::  nat
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

fun I1 :: "'a CleanQ_Set_State \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1 rb K \<longleftrightarrow> ((SX rb) \<union> (SY rb) \<union> (TXY rb) \<union> (TYX rb)) = K"


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I2: No Double Presence\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  A buffer element cannot be in more than one set at any instance of time, otherwise there
  would be multiple owners for the same buffer element. We express this invariant as ``All
  pairwise intersections of the sets in the model state are empty''. Thus, a buffer element
  cannot be in more than one set. We express this by explicitly listing all intersections
  for the state with two agents.
\<close>

fun I2 :: "'a CleanQ_Set_State \<Rightarrow> bool"
  where "I2 rb \<longleftrightarrow> SX rb \<inter> SY rb = {} \<and> SX rb \<inter> TXY rb = {} \<and> SX rb \<inter> TYX rb = {} \<and>
                   SY rb \<inter> TXY rb = {} \<and> SY rb \<inter> TYX rb = {} \<and> TXY rb \<inter> TYX rb = {}"


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>CleanQ Set Invariants\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We combine all invariants for the abstract CleanQ set model and define the unified
  predicate \verb+CleanQ_Set_Invariants+.
\<close>

fun CleanQ_Set_Invariants :: "'a set \<Rightarrow> 'a CleanQ_Set_State \<Rightarrow> bool"
  where "CleanQ_Set_Invariants K rb \<longleftrightarrow> I1 rb K \<and> I2 rb"


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
  assumes I1_holds: "I1 rb K"  and  I2_holds: "I2 rb"  and  X_owned: "b \<in> SX rb"
    shows "I1 (CleanQ_Set_enq_x b rb) K"
  unfolding CleanQ_Set_enq_x_def 
  using I1_holds X_owned by auto

lemma CleanQ_Set_enq_y_I1 :
  assumes I1_holds: "I1 rb K"  and  I2_holds: "I2 rb"  and  X_owned: "b \<in> SY rb"
    shows "I1 (CleanQ_Set_enq_y b rb) K"
  unfolding CleanQ_Set_enq_y_def 
  using I1_holds X_owned by auto

lemma CleanQ_Set_enq_x_I2 :
  assumes I1_holds: "I1 rb K"  and  I2_holds: "I2 rb"  and  X_owned: "b \<in> SX rb"
    shows "I2 (CleanQ_Set_enq_x b rb)"
  unfolding CleanQ_Set_enq_x_def
  using I2_holds X_owned by auto

lemma CleanQ_Set_enq_y_I2 :
  assumes I1_holds: "I1 rb K"  and  I2_holds: "I2 rb"  and  X_owned: "b \<in> SY rb"
    shows "I2 (CleanQ_Set_enq_y b rb)"
  unfolding CleanQ_Set_enq_y_def
  using I2_holds X_owned by auto


text \<open>
  Both invariants I1 and I2 are preserved by enq operations, thus we can combine them to
  obtain show that the combined predicate \verb+CleanQ_Set_Invariants+ always holds.
\<close>

lemma CleanQ_Set_enq_x_Invariants :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "b \<in> SX rb"
    shows "CleanQ_Set_Invariants K (CleanQ_Set_enq_x b rb)"  
  by (meson I_holds CleanQ_Set_Invariants.simps CleanQ_Set_enq_x_I1 
            CleanQ_Set_enq_x_I2 X_owned)

lemma CleanQ_Set_enq_y_Invariants :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "b \<in> SY rb"
    shows "CleanQ_Set_Invariants K (CleanQ_Set_enq_y b rb)"  
  by (meson I_holds CleanQ_Set_Invariants.simps CleanQ_Set_enq_y_I1 
            CleanQ_Set_enq_y_I2 X_owned)


text \<open>
  We can show that the buffers are ending up in the right set
\<close>

lemma CleanQ_Set_enq_x_dst :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "b \<in> SX rb"
    shows "b \<in> TXY (CleanQ_Set_enq_x b rb)"
  by (simp add: CleanQ_Set_enq_x_upd)

lemma CleanQ_Set_enq_y_dst :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "b \<in> SY rb"
    shows "b \<in> TYX (CleanQ_Set_enq_y b rb)"
  by (simp add: CleanQ_Set_enq_y_upd)


text \<open>
  Lastly, we can show that the buffers are not in the other set
\<close>

lemma CleanQ_Set_enq_x_ndst :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "b \<in> SX rb"
    shows "b \<notin> SY (CleanQ_Set_enq_x b rb)"
  by (metis CleanQ_Set_Invariants.elims(2) CleanQ_Set_enq_x_I2 CleanQ_Set_enq_x_dst 
            I2.elims(2) I_holds Set.set_insert X_owned insert_disjoint(1))

lemma CleanQ_Set_enq_y_ndst :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "b \<in> SY rb"
    shows "b \<notin> SX (CleanQ_Set_enq_y b rb)"
  by (metis CleanQ_Set_Invariants.elims(2) CleanQ_Set_enq_y_I2 CleanQ_Set_enq_y_dst 
            I2.elims(2) I_holds Set.set_insert Y_owned insert_disjoint(1))


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
  assumes I1_holds : "I1 rb K"  and  I2_holds : "I2 rb"  and  TYX_owned: "b \<in> TYX rb"
    shows "I1 (CleanQ_Set_deq_x b rb) K"
  unfolding CleanQ_Set_deq_x_def
  using I1_holds TYX_owned by auto

lemma CleanQ_Set_deq_y_I1 :
  assumes I1_holds : "I1 rb K"  and  I2_holds : "I2 rb"  and  TXY_owned: "b \<in> TXY rb"
    shows "I1 (CleanQ_Set_deq_y b rb) K"
  unfolding CleanQ_Set_deq_y_def
  using I1_holds TXY_owned by auto

lemma CleanQ_Set_deq_x_I2 :
  assumes I1_holds : "I1 rb K"  and  I2_holds : "I2 rb"  and  TYX_owned: "b \<in> TYX rb"
    shows "I2 (CleanQ_Set_deq_x b rb)"
  unfolding CleanQ_Set_deq_x_def
  using I2_holds TYX_owned by auto

lemma CleanQ_Set_deq_y_I2 :
  assumes I1_holds : "I1 rb K"  and  I2_holds : "I2 rb"  and  TXY_owned: "b \<in> TXY rb"
    shows "I2 (CleanQ_Set_deq_y b rb)"
  unfolding CleanQ_Set_deq_y_def
  using I2_holds TXY_owned by auto


text \<open>
  Both invariants I1 and I2 are preserved by dequeue operations, thus we can combine them 
  to obtain show that the predicate \verb+CleanQ_Set_Invariants+ holds
\<close>

lemma CleanQ_Set_deq_x_Invariants :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  TYX_owned: "b \<in> TYX rb"
    shows "CleanQ_Set_Invariants K (CleanQ_Set_deq_x b rb)" 
  by (meson CleanQ_Set_Invariants.simps CleanQ_Set_deq_x_I1 CleanQ_Set_deq_x_I2 I_holds 
            TYX_owned)

lemma CleanQ_Set_deq_y_Invariants :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  TXY_owned: "b \<in> TXY rb"
    shows "CleanQ_Set_Invariants K (CleanQ_Set_deq_y b rb)" 
  by (meson CleanQ_Set_Invariants.simps CleanQ_Set_deq_y_I1 CleanQ_Set_deq_y_I2 I_holds
            TXY_owned)


text \<open>
  We can show that the buffers are ending up in the right set
\<close>

lemma CleanQ_Set_deq_x_dst :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "b \<in> TYX rb"
    shows "b \<in> SX (CleanQ_Set_deq_x b rb)"
  by (simp add: CleanQ_Set_deq_x_upd)

lemma CleanQ_Set_deq_y_dst :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "b \<in> TXY rb"
    shows "b \<in> SY (CleanQ_Set_deq_y b rb)"
  by (simp add: CleanQ_Set_deq_y_upd)


text \<open>
  Lastly, we can show that the buffers are not in the other set
\<close>

lemma CleanQ_Set_deq_x_ndst :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  X_owned: "b \<in> TYX rb"
    shows "b \<notin> SY (CleanQ_Set_deq_x b rb)"
  by (metis CleanQ_Set_Invariants.elims(2) CleanQ_Set_deq_x_I2 CleanQ_Set_deq_x_dst 
            I2.elims(2) I_holds X_owned disjoint_insert(1) mk_disjoint_insert)

lemma CleanQ_Set_deq_y_ndst :
  assumes I_holds : "CleanQ_Set_Invariants K rb"  and  Y_owned: "b \<in> TXY rb"
    shows "b \<notin> SX (CleanQ_Set_deq_y b rb)"
  by (metis CleanQ_Set_Invariants.elims(2) CleanQ_Set_deq_y_I2 CleanQ_Set_deq_y_dst 
      I2.elims(2) I_holds Set.set_insert Y_owned insert_disjoint(1))


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
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RB \<and> CleanQ_Set_Invariants K \<acute>RB \<and> b \<in> SX \<acute>RB \<rbrace> 
        \<acute>RB :== (CleanQ_Set_enq_x b \<acute>RB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>RB \<rbrace>"
  by(vcg, simp only: CleanQ_Set_enq_x_Invariants)

lemma CleanQ_Set_enq_y_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RB \<and> CleanQ_Set_Invariants K \<acute>RB \<and> b \<in> SY \<acute>RB \<rbrace> 
        \<acute>RB :== (CleanQ_Set_enq_y b \<acute>RB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>RB \<rbrace>"
  by(vcg, simp only: CleanQ_Set_enq_y_Invariants)


text \<open>
  The enqueue operation effectively happens in two steps. The buffer element is removed
  from one set and added to a new set. We can express this as two sequential operations
  in the next lemma, where we show that the invariant is still preserved and that 
  the outcome is the same, as with the definition above.
\<close>

lemma CleanQ_Set_enq_x_two_step:
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RB \<and> CleanQ_Set_Invariants K \<acute>RB \<and> b \<in> SX \<acute>RB \<rbrace>
        \<acute>RB :== \<acute>RB \<lparr> SX := (SX \<acute>RB) - {b} \<rparr> ;;
        \<acute>RB :== \<acute>RB \<lparr> TXY := (TXY \<acute>RB) \<union> {b} \<rparr>  
      \<lbrace> \<acute>RB = CleanQ_Set_enq_x b rb' \<and> CleanQ_Set_Invariants K \<acute>RB \<rbrace>"
  by(vcg, simp add: CleanQ_Set_enq_x_def, auto)

lemma CleanQ_Set_enq_y_two_step:
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RB \<and> CleanQ_Set_Invariants K \<acute>RB \<and> b \<in> SY \<acute>RB \<rbrace>
        \<acute>RB :== \<acute>RB \<lparr> SY := (SY \<acute>RB) - {b} \<rparr> ;;
        \<acute>RB :== \<acute>RB \<lparr> TYX := (TYX \<acute>RB) \<union> {b} \<rparr>  
      \<lbrace> \<acute>RB = CleanQ_Set_enq_y b rb' \<and> CleanQ_Set_Invariants K \<acute>RB \<rbrace>"
  by(vcg, simp add: CleanQ_Set_enq_y_def, auto)

text \<open>
  Next we can define this conditionally, where we only execute the enqueue operation, 
  when we are owning the buffer
\<close>

lemma CleanQ_Set_enq_x_conditional :
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_Invariants K \<acute>RB \<rbrace> 
         IF b \<in> SX \<acute>RB THEN 
          \<acute>RB :== (CleanQ_Set_enq_x b \<acute>RB) 
         FI 
      \<lbrace> CleanQ_Set_Invariants K \<acute>RB \<rbrace>" 
  by (vcg, meson CleanQ_Set_enq_x_Invariants)

lemma CleanQ_Set_enq_y_conditional :
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_Invariants K \<acute>RB \<rbrace> 
         IF b \<in> SY \<acute>RB THEN 
          \<acute>RB :== (CleanQ_Set_enq_y b \<acute>RB) 
         FI 
      \<lbrace> CleanQ_Set_Invariants K \<acute>RB \<rbrace>" 
  by (vcg, meson CleanQ_Set_enq_y_Invariants)


(*

can we define a procedure of this, which can be called by a thread?
probably with a guard.

procedures 
  EnqX (S|R) = "IF (SX \<acute>S) \<noteq>  \<emptyset> THEN
                ... pick a b
                 \<acute>RB :== (CleanQ_Set_enq_x b \<acute>RB) 
                FI"

  EnqX (S|R) = "SWITCH (SX \<acute>S)
                    {{b} \<union> _} \<Rightarrow> \<acute>R :== (CleanQ_Set_enq_x b \<acute>S) 
                  | {} \<Rightarrow> \<acute>R = \<acute>S
               END"
*)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  We first show, that we can define a Hoare triple for the dequeue operations from both
  agents X and Y, and that in both cases the invariant is preserved.
\<close>

lemma CleanQ_Set_deq_x_preserves_invariants: 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RB \<and> CleanQ_Set_Invariants K \<acute>RB \<and> b \<in> TYX \<acute>RB \<rbrace> 
        \<acute>RB :== (CleanQ_Set_deq_x b \<acute>RB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>RB \<rbrace>"
  by(vcg, simp only: CleanQ_Set_deq_x_Invariants)

lemma CleanQ_Set_deq_y_preserves_invariants: 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RB \<and> CleanQ_Set_Invariants K \<acute>RB \<and> b \<in> TXY \<acute>RB \<rbrace> 
        \<acute>RB :== (CleanQ_Set_deq_y b \<acute>RB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>RB \<rbrace>"
  by(vcg, simp only: CleanQ_Set_deq_y_Invariants)


text \<open>
  The dequeue operation effectively happens in two steps. The buffer element is removed
  from one set and added to a new set. We can express this as two sequential operations
  in the next lemma, where we show that the invariant is still preserved and that 
  the outcome is the same, as with the definition above.
\<close>

lemma CleanQ_Set_deq_x_two_step:
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RB \<and> CleanQ_Set_Invariants K \<acute>RB \<and> b \<in> TYX \<acute>RB \<rbrace>
        \<acute>RB :== \<acute>RB \<lparr> TYX := (TYX \<acute>RB) - {b} \<rparr> ;;
        \<acute>RB :== \<acute>RB \<lparr> SX := (SX \<acute>RB) \<union> {b} \<rparr>  
      \<lbrace> \<acute>RB = CleanQ_Set_deq_x b rb' \<and> CleanQ_Set_Invariants K \<acute>RB \<rbrace>"
  by(vcg, simp add: CleanQ_Set_deq_x_def, auto)

lemma CleanQ_Set_deq_y_two_step:
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RB \<and> CleanQ_Set_Invariants K \<acute>RB \<and> b \<in> TXY \<acute>RB \<rbrace>
        \<acute>RB :== \<acute>RB \<lparr> TXY := (TXY \<acute>RB) - {b} \<rparr> ;;
        \<acute>RB :== \<acute>RB \<lparr> SY := (SY \<acute>RB) \<union> {b} \<rparr>  
      \<lbrace> \<acute>RB = CleanQ_Set_deq_y b rb' \<and> CleanQ_Set_Invariants K \<acute>RB \<rbrace>"
  by(vcg, simp add: CleanQ_Set_deq_y_def, auto)


text \<open>
  Next we can define this conditionally, where we only execute the enqueue operation, 
  when we are owning the buffer
\<close>

lemma CleanQ_Set_deq_x_conditional:
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_Invariants K \<acute>RB \<rbrace> 
         IF b \<in> TYX \<acute>RB THEN 
          \<acute>RB :== (CleanQ_Set_deq_x b \<acute>RB) 
         FI 
      \<lbrace> CleanQ_Set_Invariants K \<acute>RB \<rbrace>" 
  by (vcg, meson CleanQ_Set_deq_x_Invariants)

lemma CleanQ_Set_deq_y_conditional:
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_Invariants K \<acute>RB \<rbrace> 
         IF b \<in> TXY \<acute>RB THEN 
          \<acute>RB :== (CleanQ_Set_deq_y b \<acute>RB) 
         FI 
      \<lbrace> CleanQ_Set_Invariants K \<acute>RB \<rbrace>" 
  by (vcg, meson CleanQ_Set_deq_y_Invariants)




(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Combining Enqueue and Dequeue\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We can now combine the enqeueue and dequeue operations and pass a buffer around the 
  queue and back to the originator. We prove this by showing the state is the same.
\<close>

lemma CleanQ_Set_ops_combine : 
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_Invariants K \<acute>RB \<and> rb = \<acute>RB \<and> b \<in> SX \<acute>RB \<rbrace> 
        \<acute>RB :== (CleanQ_Set_enq_x b \<acute>RB) ;;
        \<acute>RB :== (CleanQ_Set_deq_y b \<acute>RB) ;;
        \<acute>RB :== (CleanQ_Set_enq_y b \<acute>RB) ;;
        \<acute>RB :== (CleanQ_Set_deq_x b \<acute>RB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>RB \<and> rb = \<acute>RB \<and> b \<in> SX \<acute>RB \<rbrace>" 
proof(vcg)
  have EQ: "\<And> RB. CleanQ_Set_Invariants K RB \<Longrightarrow> b \<in> SX RB \<Longrightarrow> (CleanQ_Set_deq_x b
             (CleanQ_Set_enq_y b
               (CleanQ_Set_deq_y b
                 (CleanQ_Set_enq_x b RB)))) = RB"
    unfolding CleanQ_Set_deq_x_def CleanQ_Set_enq_x_def CleanQ_Set_deq_y_def 
              CleanQ_Set_enq_y_def
    apply(simp) 
    using insert_absorb by fastforce

  from EQ  show "\<And>RB. CleanQ_Set_Invariants K RB \<Longrightarrow>
          b \<in> SX RB \<Longrightarrow>
          CleanQ_Set_Invariants K
           (CleanQ_Set_deq_x b
             (CleanQ_Set_enq_y b
               (CleanQ_Set_deq_y b
                 (CleanQ_Set_enq_x b RB)))) \<and>
          RB =
          CleanQ_Set_deq_x b
           (CleanQ_Set_enq_y b
             (CleanQ_Set_deq_y b (CleanQ_Set_enq_x b RB))) \<and>
          b \<in> SX (CleanQ_Set_deq_x b
                    (CleanQ_Set_enq_y b
                      (CleanQ_Set_deq_y b
                        (CleanQ_Set_enq_x b RB))))"
    by(auto)
qed

  
  



(* ==================================================================================== *)
subsection \<open>Integration in COMPLEX\<close>
(* ==================================================================================== *)


(* 

  have two threads. 
    X: call enqx | deqx
    Y: call enqy | deqy



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



(* ==================================================================================== *)
subsection \<open>STUFF\<close>
(* ==================================================================================== *)

definition CleanQ_Set_deq_x_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_deq_x_pre K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> TXY rb }"

definition CleanQ_Set_deq_x_post :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_deq_x_post K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> SX rb }"


definition CleanQ_Set_State_enqueuex_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_State_enqueuex_pre K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> SX rb }"

definition CleanQ_Set_State_enqueuex_post :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_State_enqueuex_post K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> TXY rb }"


(*<*)
end
(*>*)