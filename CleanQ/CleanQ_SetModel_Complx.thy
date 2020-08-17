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



section \<open>Set Model COMPLX proofs\<close>

text \<open>
  Due to problems importing both SIMPL and COMPLX we split the files and have all the proofs
  using COMPLX in this file
\<close>

theory CleanQ_SetModel_Complx
(*<*)
imports 
  Main
  CleanQ_SetModel
  "../Complx/OG_Hoare"
 "../Complx/OG_Syntax"
begin
(*>*)

record CleanQ_Set_st =
  SRB :: "nat CleanQ_Set_State"

(* ==================================================================================== *)
subsection \<open>Integration in COMPLX\<close>
(* ==================================================================================== *)

text \<open>
  We now integrate the the CleanQ Set Model into COMPLX. For each of the two operations,
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
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>
        \<lbrace>CleanQ_Set_Invariants K \<acute>SRB \<and>  b \<in> SX \<acute>SRB\<rbrace> 
          \<acute>SRB := (CleanQ_Set_enq_x b \<acute>SRB) 
        \<lbrace>CleanQ_Set_Invariants K \<acute>SRB\<rbrace>, \<lbrace>True\<rbrace>"
  unfolding CleanQ_Set_Invariants_def
  apply(oghoare)
  by (simp add: CleanQ_Set_enq_x_I1 CleanQ_Set_enq_x_I2 Collect_mono_iff)

lemma CleanQ_Set_enq_y_preserves_invariants : 
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>
        \<lbrace>CleanQ_Set_Invariants K \<acute>SRB \<and> b \<in> SY \<acute>SRB\<rbrace> 
          \<acute>SRB := (CleanQ_Set_enq_y b \<acute>SRB) 
        \<lbrace>CleanQ_Set_Invariants K \<acute>SRB\<rbrace>, \<lbrace>True\<rbrace>"
  unfolding CleanQ_Set_Invariants_def
  apply(oghoare)
  by (simp add: CleanQ_Set_enq_y_I1 CleanQ_Set_enq_y_I2 Collect_mono_iff)



text \<open>
  The same applies for the multi-step \verb+eneuque_n+ operation.
\<close>

lemma CleanQ_Set_enq_n_x_preserves_invariants : 
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>
        \<lbrace>CleanQ_Set_Invariants K \<acute>SRB \<and>  (\<forall>b \<in> B. b \<in> (SX \<acute>SRB)) \<rbrace> 
          \<acute>SRB := (CleanQ_Set_enq_n_x B \<acute>SRB) 
        \<lbrace>CleanQ_Set_Invariants K \<acute>SRB\<rbrace>, \<lbrace>True\<rbrace>"
  unfolding CleanQ_Set_Invariants_def
  apply(oghoare)
  by (simp add: CleanQ_Set_enq_n_x_I1 CleanQ_Set_enq_n_x_I2 Collect_mono)

lemma CleanQ_Set_enq_n_y_preserves_invariants : 
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>
        \<lbrace>CleanQ_Set_Invariants K \<acute>SRB \<and>  (\<forall>b \<in> B. b \<in> (SY \<acute>SRB)) \<rbrace> 
          \<acute>SRB := (CleanQ_Set_enq_n_y B \<acute>SRB) 
        \<lbrace>CleanQ_Set_Invariants K \<acute>SRB\<rbrace>, \<lbrace>True\<rbrace>"
  unfolding CleanQ_Set_Invariants_def
  apply(oghoare)
  by (simp add: CleanQ_Set_enq_n_y_I1 CleanQ_Set_enq_n_y_I2 Collect_mono)

text \<open>
  The enqueue operation  happens in two steps. The buffer element is removed
  from one set and added to a new set. We can express this as two sequential operations
  in the next lemma, where we show that the invariant is still preserved and that 
  the outcome is the same, as with the definition above.
\<close>

lemma CleanQ_Set_enq_x_two_step : 
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>
        \<lbrace>CleanQ_Set_Invariants K \<acute>SRB \<and>  b \<in> SX \<acute>SRB \<rbrace> 
        \<acute>SRB := \<acute>SRB \<lparr> SX := (SX \<acute>SRB) - {b} \<rparr> ;;
        \<lbrace>CleanQ_Set_Invariants (K-{b}) \<acute>SRB  \<rbrace> 
        \<acute>SRB := \<acute>SRB \<lparr> TXY := (TXY \<acute>SRB) \<union> {b} \<rparr>  
        \<lbrace>CleanQ_Set_Invariants K \<acute>SRB\<rbrace>, \<lbrace>True\<rbrace>"
  apply (oghoare, auto)
  oops

(*<*)
end
(*>*)