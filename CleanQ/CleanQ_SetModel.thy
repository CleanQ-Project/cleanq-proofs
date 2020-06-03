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
  imports  "../Simpl/Vcg"
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


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I1: Constant Union\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  The union of all sets is constant. This ensures that elements are not lost during 
  the ownership transfer
\<close>

fun I1 :: "'a CleanQ_Set_State \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1 rb K \<longleftrightarrow> ((SX rb) \<union> (SY rb) \<union> (TXY rb) \<union> (TYX rb)) = K"


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I2: No Double Presence\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>All pairwise intersubsections are empty. An element cannot be in one than more sets. 
This is required as the element cannot be owned by more than one agent.\<close>

fun I2 :: "'a CleanQ_Set_State \<Rightarrow> bool"
  where "I2 rb \<longleftrightarrow> SX rb \<inter> SY rb = {} \<and> SX rb \<inter> TXY rb = {} \<and> SX rb \<inter> TYX rb = {} \<and> 
                   SY rb \<inter> TXY rb = {} \<and> SY rb \<inter> TYX rb = {} \<and> TXY rb \<inter> TYX rb = {}"


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Invariants\<close>
(* ------------------------------------------------------------------------------------ *)

fun CleanQ_Set_State_Invariants :: "'a set \<Rightarrow> 'a CleanQ_Set_State \<Rightarrow> bool"
  where "CleanQ_Set_State_Invariants K rb \<longleftrightarrow> I1 rb K \<and> I2 rb"


(* ==================================================================================== *)
subsection \<open>State Operations\<close>
(* ==================================================================================== *)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue Operation\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  The enqueue operation initiates a transfer of ownership from X -> Y (enq\_x), or the 
  other way from $Y \rightarrow X$ (enq\_y). This corresponds to removing the element from 
  set SX and inserting it into set TXY, or removing it from the set XY and inserting it to 
  TYX respectively.
\<close>

definition CleanQ_Set_enq_x :: "'a \<Rightarrow> 'a CleanQ_Set_State  \<Rightarrow> 'a CleanQ_Set_State"
  where "CleanQ_Set_enq_x b rb = rb  \<lparr>  SX := (SX rb) - {(b)},  TXY := ((TXY rb) \<union> {(b)}) \<rparr>"

definition CleanQ_Set_enq_y :: "'a \<Rightarrow> 'a CleanQ_Set_State  \<Rightarrow> 'a CleanQ_Set_State"
  where "CleanQ_Set_enq_y b rb = rb  \<lparr>  SY := (SY rb) - {(b)},  TYX := ((TYX rb) \<union> {(b)}) \<rparr>"

(*<*)

lemma CleanQ_Set_enq_x_upd :
  "CleanQ_Set_enq_x b rb =  \<lparr>  SX = (SX rb) - {(b)},  SY = (SY rb), TXY = ((TXY rb) \<union> {(b)}),  
                          TYX = (TYX rb) \<rparr>"
  by(simp add:CleanQ_Set_enq_x_def)

lemma CleanQ_Set_enq_y_upd :
  "CleanQ_Set_enq_y b rb =  \<lparr>  SX = (SX rb),  SY = (SY rb) - {(b)}, TXY = (TXY rb),  
                          TYX = ((TYX rb) \<union> {(b)}) \<rparr>"
  by(simp add:CleanQ_Set_enq_y_def)

(*>*)


text \<open>Next, we show that CleanQ\_Set\_enqueuex preserves the invariant\<close>

lemma CleanQ_Set_enq_x_I1 :
  assumes I1_holds : "I1 rb K"
      and I2_holds : "I2 rb"
      and X_owned: "b \<in> SX rb"
    shows "I1 (CleanQ_Set_enq_x b rb) K"
  unfolding CleanQ_Set_enq_x_def 
  using I1_holds X_owned by auto

lemma CleanQ_Set_enq_x_I2 :
  assumes I1_holds : "I1 rb K"
      and I2_holds : "I2 rb"
      and X_owned: "b \<in> SX rb"
    shows "I2 (CleanQ_Set_enq_x b rb)"
  unfolding CleanQ_Set_enq_x_def
  using I2_holds X_owned by auto

lemma CleanQ_Set_enq_x_Invariants :
  assumes I_holds : "CleanQ_Set_State_Invariants K rb"
      and X_owned: "b \<in> SX rb"
    shows "CleanQ_Set_State_Invariants K (CleanQ_Set_enq_x b rb)"  
  by (meson I_holds CleanQ_Set_State_Invariants.simps CleanQ_Set_enq_x_I1 CleanQ_Set_enq_x_I2 X_owned)





lemma CleanQ_Set_State_Enq_Preserves_Invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RB \<and> CleanQ_Set_State_Invariants K \<acute>RB \<and>  b \<in> SX \<acute>RB   \<rbrace> 
        \<acute>RB :== (CleanQ_Set_enq_x b \<acute>RB) 
      \<lbrace> CleanQ_Set_State_Invariants K \<acute>RB \<rbrace>"
  apply vcg
  by(simp only: CleanQ_Set_enq_x_Invariants)


lemma CleanQ_Set_State_Enq_two_step:
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RB \<and> CleanQ_Set_State_Invariants K \<acute>RB \<and>  b \<in> SX \<acute>RB   \<rbrace>
            \<acute>RB :== \<acute>RB \<lparr>  SX := (SX  \<acute>RB ) - {(b)}  \<rparr> ;;
            \<acute>RB :==  \<acute>RB \<lparr>  TXY := ((TXY  \<acute>RB ) \<union> {(b)}) \<rparr>  
      \<lbrace> \<acute>RB = CleanQ_Set_enq_x b rb' \<rbrace>"
  apply vcg
  by(simp add:CleanQ_Set_enq_x_def)


lemma "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RB \<and> CleanQ_Set_State_Invariants K \<acute>RB \<and>  b \<in> SX \<acute>RB   \<rbrace>
           \<acute>RB :== \<acute>RB \<lparr>  SX := (SX rb) - {(b)}  \<rparr> ;;
           \<acute>RB :==  \<acute>RB \<lparr>  TXY := ((TXY rb) \<union> {(b)}) \<rparr>  
            \<lbrace> CleanQ_Set_State_Invariants K \<acute>RB \<and> \<acute>RB = CleanQ_Set_enq_x b rb' \<rbrace>"
  using  CleanQ_Set_State_Enq_two_step CleanQ_Set_State_Enq_Preserves_Invariants
  oops
  

lemma "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_State_Invariants K \<acute>RB  \<rbrace> 
          IF b \<in> SX \<acute>RB THEN \<acute>RB :== (CleanQ_Set_enq_x b \<acute>RB) FI \<lbrace> CleanQ_Set_State_Invariants K \<acute>RB \<rbrace>"
  apply vcg 
  by (meson CleanQ_Set_enq_x_Invariants)



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  The dequeue operation completes a transfer of ownership from $Y \rightarrow  X$. This 
  corresponds to removing the element from set TYX and inserting it into set SX.
\<close>

definition CleanQ_Set_deq_x :: "'a \<Rightarrow> 'a CleanQ_Set_State  \<Rightarrow> 'a CleanQ_Set_State"
  where "CleanQ_Set_deq_x b rb =  \<lparr>  SX = (SX rb) \<union> {(b)},  SY = (SY rb), TXY = (TXY rb),  
                                   TYX = (TYX rb) - {b} \<rparr>"


text \<open>Next, we show that CleanQ\_Set\_deuquex preserves the invariant\<close>

lemma CleanQ_Set_deq_x_I1 :
  assumes I1_holds : "I1 rb K"
      and I2_holds : "I2 rb"
      and TXY_owned: "b \<in> TXY rb"
    shows "I1 (CleanQ_Set_deq_x b rb) K"
  unfolding CleanQ_Set_deq_x_def
  using I1_holds TXY_owned by auto

lemma CleanQ_Set_deq_x_I2 :
  assumes I1_holds : "I1 rb K"
      and I2_holds : "I2 rb"
      and TYX_owned: "b \<in> TYX rb"
    shows "I2 (CleanQ_Set_deq_x b rb)"
  unfolding CleanQ_Set_deq_x_def
  using I2_holds TYX_owned by auto

lemma CleanQ_Set_deq_x_Invariants :
 assumes I_holds : "CleanQ_Set_State_Invariants K rb"
      and TYX_owned: "b \<in> TYX rb"
    shows "CleanQ_Set_State_Invariants K (CleanQ_Set_deq_x b rb)" 
proof -
  have "I1 \<lparr>SX = SX rb \<union> {b}, SY = SY rb, TXY = TXY rb, TYX = TYX rb - {b}\<rparr> K"
    using I_holds TYX_owned by auto
  then show ?thesis
    by (metis I_holds CleanQ_Set_State_Invariants.simps CleanQ_Set_deq_x_I2 CleanQ_Set_deq_x_def TYX_owned)
qed




lemma "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_State_Invariants K \<acute>RB \<and>  b \<in> TYX \<acute>RB   \<rbrace> \<acute>RB :== (CleanQ_Set_deq_x b \<acute>RB) \<lbrace> CleanQ_Set_State_Invariants K \<acute>RB \<rbrace>"
  apply vcg
  by(simp only: CleanQ_Set_deq_x_Invariants)
  

lemma "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_State_Invariants K \<acute>RB  \<rbrace> 
          IF b \<in> TYX \<acute>RB THEN \<acute>RB :== (CleanQ_Set_deq_x b \<acute>RB) FI \<lbrace> CleanQ_Set_State_Invariants K \<acute>RB \<rbrace>"
  apply vcg 
  by (meson CleanQ_Set_deq_x_Invariants)


(* ==================================================================================== *)
subsection \<open>Basic Integration\<close>
(* ==================================================================================== *)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue Operation\<close>
(* ------------------------------------------------------------------------------------ *)

definition CleanQ_Set_State_enqueuex_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_State_enqueuex_pre K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> SX rb }"

definition CleanQ_Set_State_enqueuex_post :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_State_enqueuex_post K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> TXY rb }"



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


definition CleanQ_Set_deq_x_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_deq_x_pre K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> TXY rb }"

definition CleanQ_Set_deq_x_post :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_deq_x_post K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> SX rb }"




end