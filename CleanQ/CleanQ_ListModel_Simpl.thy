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

theory CleanQ_ListModel_Simpl
(*<*)
  imports Main "../Simpl/Vcg" CleanQ_ListModel
(*>*)
begin

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

text \<open>
  The same applies for the multi-step \verb+eneuque_n+ operation.
\<close>

lemma CleanQ_List_enq_n_x_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>ListRB \<and> CleanQ_List_Invariants K \<acute>ListRB 
        \<and> (\<forall>b \<in> set B. b \<in> (lSX \<acute>ListRB)) \<and> distinct B \<rbrace> 
        \<acute>ListRB :== (CleanQ_List_enq_n_x B \<acute>ListRB) 
      \<lbrace> CleanQ_List_Invariants K \<acute>ListRB \<rbrace>"
  apply(vcg) using CleanQ_List_enq_n_x_Invariants by blast

lemma CleanQ_List_enq_n_y_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>ListRB \<and> CleanQ_List_Invariants K \<acute>ListRB 
        \<and> (\<forall>b \<in> set B. b \<in> (lSY \<acute>ListRB)) \<and> distinct B \<rbrace> 
        \<acute>ListRB :== (CleanQ_List_enq_n_y B \<acute>ListRB) 
      \<lbrace> CleanQ_List_Invariants K \<acute>ListRB \<rbrace>"
  apply(vcg) using CleanQ_List_enq_n_y_Invariants by blast

end



