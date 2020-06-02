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



section "CleanQ Abstract Set Model"

text \<open>
  We define
\<close>

theory CleanQ_SetModel
(*<*)
  imports  "../Simpl/Vcg"
(*>*)
begin



(* ==================================================================================== *)
subsection \<open>State Definition\<close>
(* ==================================================================================== *)


subsubsection \<open>Abstract Queue Definition\<close>

text \<open>The "SetRB" defines the base state with four sets:
  * SX: this is the set of buffers owned by X.
  * SY: this is the set of buffers owned by Y.
  * TXY: this is the set of buffers in transfer from X -> Y.
  * TYX: this is the set of buffers in transfer from Y -> X.
  
  * Buffers in TXY and TYX are not owned by either X or Y.\<close>

record 'a SetRB =
  SX  :: "'a set"
  SY  :: "'a set"
  TXY :: "'a set"
  TYX :: "'a set"


record 'g SetRB_vars = 
  RB_'  :: "nat SetRB"
  B_'   ::  nat

  


(* ==================================================================================== *)
subsection \<open>State Invariants\<close>
(* ==================================================================================== *)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I1: Constant Union\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  The union of all sets is constant. This ensures that elements are not lost during 
  the ownership transfer
\<close>

fun I1 :: "'a SetRB \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1 rb K \<longleftrightarrow> ((SX rb) \<union> (SY rb) \<union> (TXY rb) \<union> (TYX rb)) = K"


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I2: No Double Presence\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>All pairwise intersubsections are empty. An element cannot be in one than more sets. 
This is required as the element cannot be owned by more than one agent.\<close>

fun I2 :: "'a SetRB \<Rightarrow> bool"
  where "I2 rb \<longleftrightarrow> SX rb \<inter> SY rb = {} \<and> SX rb \<inter> TXY rb = {} \<and> SX rb \<inter> TYX rb = {} \<and> 
                   SY rb \<inter> TXY rb = {} \<and> SY rb \<inter> TYX rb = {} \<and> TXY rb \<inter> TYX rb = {}"


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>SetRB Invariants\<close>
(* ------------------------------------------------------------------------------------ *)

fun SetRB_Invariants :: "'a set \<Rightarrow> 'a SetRB \<Rightarrow> bool"
  where "SetRB_Invariants K rb \<longleftrightarrow> I1 rb K \<and> I2 rb"


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

definition SetRB_enq_x :: "'a \<Rightarrow> 'a SetRB  \<Rightarrow> 'a SetRB"
  where "SetRB_enq_x b rb = rb  \<lparr>  SX := (SX rb) - {(b)},  TXY := ((TXY rb) \<union> {(b)}) \<rparr>"

definition SetRB_enq_y :: "'a \<Rightarrow> 'a SetRB  \<Rightarrow> 'a SetRB"
  where "SetRB_enq_y b rb = rb  \<lparr>  SY := (SY rb) - {(b)},  TYX := ((TYX rb) \<union> {(b)}) \<rparr>"

(*<*)

lemma SetRB_enq_x_upd :
  "SetRB_enq_x b rb =  \<lparr>  SX = (SX rb) - {(b)},  SY = (SY rb), TXY = ((TXY rb) \<union> {(b)}),  
                          TYX = (TYX rb) \<rparr>"
  by(simp add:SetRB_enq_x_def)

lemma SetRB_enq_y_upd :
  "SetRB_enq_y b rb =  \<lparr>  SX = (SX rb),  SY = (SY rb) - {(b)}, TXY = (TXY rb),  
                          TYX = ((TYX rb) \<union> {(b)}) \<rparr>"
  by(simp add:SetRB_enq_y_def)

(*>*)


text \<open>Next, we show that SetRB\_enqueuex preserves the invariant\<close>

lemma SetRB_enq_x_I1 :
  assumes I1_holds : "I1 rb K"
      and I2_holds : "I2 rb"
      and X_owned: "b \<in> SX rb"
    shows "I1 (SetRB_enq_x b rb) K"
  unfolding SetRB_enq_x_def 
  using I1_holds X_owned by auto

lemma SetRB_enq_x_I2 :
  assumes I1_holds : "I1 rb K"
      and I2_holds : "I2 rb"
      and X_owned: "b \<in> SX rb"
    shows "I2 (SetRB_enq_x b rb)"
  unfolding SetRB_enq_x_def
  using I2_holds X_owned by auto

lemma SetRB_enq_x_Invariants :
  assumes I_holds : "SetRB_Invariants K rb"
      and X_owned: "b \<in> SX rb"
    shows "SetRB_Invariants K (SetRB_enq_x b rb)"  
  by (meson I_holds SetRB_Invariants.simps SetRB_enq_x_I1 SetRB_enq_x_I2 X_owned)





lemma SetRB_Enq_Preserves_Invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RB \<and> SetRB_Invariants K \<acute>RB \<and>  b \<in> SX \<acute>RB   \<rbrace> 
        \<acute>RB :== (SetRB_enq_x b \<acute>RB) 
      \<lbrace> SetRB_Invariants K \<acute>RB \<rbrace>"
  apply vcg
  by(simp only: SetRB_enq_x_Invariants)


lemma SetRB_Enq_two_step:
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RB \<and> SetRB_Invariants K \<acute>RB \<and>  b \<in> SX \<acute>RB   \<rbrace>
            \<acute>RB :== \<acute>RB \<lparr>  SX := (SX  \<acute>RB ) - {(b)}  \<rparr> ;;
            \<acute>RB :==  \<acute>RB \<lparr>  TXY := ((TXY  \<acute>RB ) \<union> {(b)}) \<rparr>  
      \<lbrace> \<acute>RB = SetRB_enq_x b rb' \<rbrace>"
  apply vcg
  by(simp add:SetRB_enq_x_def)


lemma "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RB \<and> SetRB_Invariants K \<acute>RB \<and>  b \<in> SX \<acute>RB   \<rbrace>
           \<acute>RB :== \<acute>RB \<lparr>  SX := (SX rb) - {(b)}  \<rparr> ;;
           \<acute>RB :==  \<acute>RB \<lparr>  TXY := ((TXY rb) \<union> {(b)}) \<rparr>  
            \<lbrace> SetRB_Invariants K \<acute>RB \<and> \<acute>RB = SetRB_enq_x b rb' \<rbrace>"
  using  SetRB_Enq_two_step SetRB_Enq_Preserves_Invariants
  oops
  

lemma "\<Gamma>\<turnstile> \<lbrace> SetRB_Invariants K \<acute>RB  \<rbrace> 
          IF b \<in> SX \<acute>RB THEN \<acute>RB :== (SetRB_enq_x b \<acute>RB) FI \<lbrace> SetRB_Invariants K \<acute>RB \<rbrace>"
  apply vcg 
  by (meson SetRB_enq_x_Invariants)



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  The dequeue operation completes a transfer of ownership from $Y \rightarrow  X$. This 
  corresponds to removing the element from set TYX and inserting it into set SX.
\<close>

definition SetRB_dequeuex :: "'a \<Rightarrow> 'a SetRB  \<Rightarrow> 'a SetRB"
  where "SetRB_dequeuex b rb =  \<lparr>  SX = (SX rb) \<union> {(b)},  SY = (SY rb), TXY = (TXY rb),  
                                   TYX = (TYX rb) - {b} \<rparr>"


text \<open>Next, we show that SetRB\_deuquex preserves the invariant\<close>

lemma SetRB_dequeuex_I1 :
  assumes I1_holds : "I1 rb K"
      and I2_holds : "I2 rb"
      and TXY_owned: "b \<in> TXY rb"
    shows "I1 (SetRB_dequeuex b rb) K"
  unfolding SetRB_dequeuex_def
  using I1_holds TXY_owned by auto

lemma SetRB_dequeuex_I2 :
  assumes I1_holds : "I1 rb K"
      and I2_holds : "I2 rb"
      and TYX_owned: "b \<in> TYX rb"
    shows "I2 (SetRB_dequeuex b rb)"
  unfolding SetRB_dequeuex_def
  using I2_holds TYX_owned by auto

lemma SetRB_dequeuex_Invariants :
 assumes I_holds : "SetRB_Invariants K rb"
      and TYX_owned: "b \<in> TYX rb"
    shows "SetRB_Invariants K (SetRB_dequeuex b rb)" 
proof -
  have "I1 \<lparr>SX = SX rb \<union> {b}, SY = SY rb, TXY = TXY rb, TYX = TYX rb - {b}\<rparr> K"
    using I_holds TYX_owned by auto
  then show ?thesis
    by (metis I_holds SetRB_Invariants.simps SetRB_dequeuex_I2 SetRB_dequeuex_def TYX_owned)
qed




lemma "\<Gamma>\<turnstile> \<lbrace> SetRB_Invariants K \<acute>RB \<and>  b \<in> TYX \<acute>RB   \<rbrace> \<acute>RB :== (SetRB_dequeuex b \<acute>RB) \<lbrace> SetRB_Invariants K \<acute>RB \<rbrace>"
  apply vcg
  by(simp only: SetRB_dequeuex_Invariants)
  

lemma "\<Gamma>\<turnstile> \<lbrace> SetRB_Invariants K \<acute>RB  \<rbrace> 
          IF b \<in> TYX \<acute>RB THEN \<acute>RB :== (SetRB_dequeuex b \<acute>RB) FI \<lbrace> SetRB_Invariants K \<acute>RB \<rbrace>"
  apply vcg 
  by (meson SetRB_dequeuex_Invariants)


(* ==================================================================================== *)
subsection \<open>Basic Integration\<close>
(* ==================================================================================== *)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue Operation\<close>
(* ------------------------------------------------------------------------------------ *)

definition SetRB_enqueuex_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a SetRB, 'a SetRB) Semantic.xstate set"
  where "SetRB_enqueuex_pre K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> SX rb }"

definition SetRB_enqueuex_post :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a SetRB, 'a SetRB) Semantic.xstate set"
  where "SetRB_enqueuex_post K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> TXY rb }"



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


definition SetRB_dequeuex_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a SetRB, 'a SetRB) Semantic.xstate set"
  where "SetRB_dequeuex_pre K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> TXY rb }"

definition SetRB_dequeuex_post :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a SetRB, 'a SetRB) Semantic.xstate set"
  where "SetRB_dequeuex_post K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> SX rb }"




end