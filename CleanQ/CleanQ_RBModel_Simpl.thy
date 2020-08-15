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



section \<open>RB Model Simpl proofs\<close>

text \<open>
  Due to problems importing both SIMPL and COMPLX we split the files and have all the proofs
  using SIMPL in this file
\<close>

theory CleanQ_RBModel_Simpl
(*<*) 
  imports Main 
    CleanQ_RB
    CleanQ_RBModel
    "../Simpl/Vcg"
(*>*)  
begin

(* ==================================================================================== *)
subsection \<open>Integration in SIMPL\<close>
(* ==================================================================================== *)

lemma CleanQ_RB_enq_x_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RingRB \<and> CleanQ_RB_Invariants K \<acute>RingRB \<and> b \<in> rSX \<acute>RingRB \<and> 
        CleanQ_RB_enq_x_possible \<acute>RingRB \<rbrace> 
        \<acute>RingRB :== (CleanQ_RB_enq_x b \<acute>RingRB) 
      \<lbrace> CleanQ_RB_Invariants K \<acute>RingRB \<rbrace>" 
  apply(vcg)
  by (meson CleanQ_RB_enq_x_inv_all) 

lemma CleanQ_RB_enq_y_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RingRB \<and> CleanQ_RB_Invariants K \<acute>RingRB \<and> b \<in> rSY \<acute>RingRB \<and> 
        CleanQ_RB_enq_y_possible \<acute>RingRB \<rbrace> 
        \<acute>RingRB :== (CleanQ_RB_enq_y b \<acute>RingRB) 
      \<lbrace> CleanQ_RB_Invariants K \<acute>RingRB \<rbrace>" 
  apply(vcg)
  by (meson CleanQ_RB_enq_y_inv_all) 

lemma CleanQ_RB_deq_x_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RingRB \<and> CleanQ_RB_Invariants K \<acute>RingRB \<and> CleanQ_RB_deq_x_possible \<acute>RingRB \<rbrace> 
        \<acute>RingRB :== (CleanQ_RB_deq_x \<acute>RingRB) 
      \<lbrace> CleanQ_RB_Invariants K \<acute>RingRB \<rbrace>" 
  apply(vcg)
  using CleanQ_RB_deq_x_all_inv by blast
  
lemma CleanQ_RB_deq_y_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RingRB \<and> CleanQ_RB_Invariants K \<acute>RingRB \<and> CleanQ_RB_deq_y_possible \<acute>RingRB \<rbrace> 
        \<acute>RingRB :== (CleanQ_RB_deq_y \<acute>RingRB) 
      \<lbrace> CleanQ_RB_Invariants K \<acute>RingRB \<rbrace>" 
  apply(vcg)
  using CleanQ_RB_deq_y_all_inv by blast

end 