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



section \<open>CRB proofs in Complex\<close>


theory CleanQ_CRBModel_Complx
(*<*) 
  imports CleanQ_CRBModel
          "../Complx/OG_Syntax"
          "../Complx/OG_Hoare"
(*>*)  
begin

(* ==================================================================================== *)
subsection \<open>CleanQ Abstract Concurrent Ring Buffer Model State\<close>
(* ==================================================================================== *)

text \<open>
  the model is exactly the same and we reuse the RB Model. 
\<close>

(*<*)
(* Define some global variables to make Simpl/Complex proofs work *)
record CleanQ_CRB_State_vars = 
  CRB  :: "nat CleanQ_RB_State"
  buf :: "nat"
  uni :: "nat set"
(*>*)



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Hoare Triples for the Enqueue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  We now show that the \verb+enqueue+ operation satisfies the pre and post conditions
  for the predicates P, Q and R. 
\<close>


paragraph \<open>Writing the Head Element\<close>

text \<open>
  We show the Hoare triple with \verb+{P) write_head {Q}+.
\<close>

lemma  CleanQ_RB_write_head_x_hoare:
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub> 
   \<lbrace> CleanQ_RB_enq_x_P K \<acute>CRB b \<rbrace> 
    \<acute>CRB := (CleanQ_RB_write_head_x b \<acute>CRB)
   \<lbrace> CleanQ_RB_enq_x_Q K \<acute>CRB b  \<rbrace>, \<lbrace>True\<rbrace>"     
  apply(oghoare)
  by simp
  

lemma  CleanQ_RB_write_head_y_hoare:
 "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub> 
      \<lbrace> CleanQ_RB_enq_y_P K \<acute>CRB b \<rbrace> 
        \<acute>CRB := (CleanQ_RB_write_head_y b \<acute>CRB)
      \<lbrace> CleanQ_RB_enq_y_Q K \<acute> CRB b  \<rbrace>, \<lbrace>True\<rbrace>"                                                 
  apply(oghoare)
  by simp


paragraph \<open>Incrementing the Head Pointer\<close>

text \<open>
  We show the Hoare triple with \verb+{Q) incr_head {R}+.
\<close>

lemma  CleanQ_RB_incr_head_x_hoare:
   "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub> 
    \<lbrace> CleanQ_RB_enq_x_Q K \<acute>CRB b \<rbrace> 
        \<acute>CRB := (CleanQ_RB_incr_head_x b \<acute>CRB)
    \<lbrace> CleanQ_RB_enq_x_R K \<acute>CRB b  \<rbrace>, \<lbrace>True\<rbrace>"
  apply(oghoare)
  using CleanQ_RB_enq_x_inv_all CleanQ_RB_enq_x_result by fastforce

lemma  CleanQ_RB_incr_head_y_hoare:
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>  
    \<lbrace>  CleanQ_RB_enq_y_Q K \<acute>CRB b \<rbrace> 
        \<acute>CRB := (CleanQ_RB_incr_head_y b \<acute>CRB)
    \<lbrace> CleanQ_RB_enq_y_R K \<acute>CRB b  \<rbrace>, \<lbrace>True\<rbrace>"
  apply(oghoare)
  using CleanQ_RB_enq_y_inv_all CleanQ_RB_enq_y_result by fastforce


paragraph \<open>Full Enqueue Operation\<close>

text \<open>
  We show the Hoare triple with \verb+{P) enq {R}+.
\<close>

lemma CleanQ_RB_enq_x_hoare : 
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>  
   \<lbrace> CleanQ_RB_enq_x_P K \<acute>CRB b \<rbrace> 
    \<acute>CRB := (CleanQ_RB_write_head_x b \<acute>CRB) ;;
   \<lbrace> CleanQ_RB_enq_x_Q K \<acute>CRB b \<rbrace>
     \<acute>CRB := (CleanQ_RB_incr_head_x b \<acute>CRB)
   \<lbrace> CleanQ_RB_enq_x_R K \<acute>CRB b \<rbrace>, \<lbrace>True\<rbrace>"
  apply(oghoare)
  using CleanQ_RB_enq_x_inv_all CleanQ_RB_enq_x_result apply fastforce
  by simp
  

lemma CleanQ_RB_enq_y_hoare : 
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>  
  \<lbrace> CleanQ_RB_enq_y_P K \<acute>CRB b \<rbrace> 
    \<acute>CRB := (CleanQ_RB_write_head_y b \<acute>CRB) ;;
  \<lbrace> CleanQ_RB_enq_y_Q K \<acute>CRB b \<rbrace>
    \<acute>CRB := (CleanQ_RB_incr_head_y b \<acute>CRB)
  \<lbrace> CleanQ_RB_enq_y_R K \<acute>CRB b \<rbrace>, \<lbrace>True\<rbrace>"
  apply(oghoare)
  using CleanQ_RB_enq_y_inv_all CleanQ_RB_enq_y_result apply fastforce
  by simp


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Hoare Triples for the Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  We now show that the \verb+dequeue+ operation satisfies the pre and post conditions
  for the predicates P, Q and R. 
\<close>


paragraph \<open>Reading the Tail Element\<close>

text \<open>
  We show the Hoare triple with \verb+{P) read_tail {Q}+.
\<close>

lemma  CleanQ_RB_read_tail_x_hoare:
 "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>  
  \<lbrace> CleanQ_RB_deq_x_P K \<acute>CRB \<rbrace> 
    \<acute>buf := (CleanQ_RB_read_tail_x \<acute>CRB)
  \<lbrace> CleanQ_RB_deq_x_Q K \<acute>CRB \<acute>buf  \<rbrace>, \<lbrace>True\<rbrace>"  
  apply(oghoare)
  by simp 

lemma  CleanQ_RB_read_tail_y_hoare:
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>  
  \<lbrace> CleanQ_RB_deq_y_P K \<acute>CRB \<rbrace> 
    \<acute>buf := (CleanQ_RB_read_tail_y \<acute>CRB)
  \<lbrace> CleanQ_RB_deq_y_Q K \<acute>CRB \<acute>buf  \<rbrace>, \<lbrace>True\<rbrace>"  
  apply(oghoare)  
  by simp

paragraph \<open>Incrementing the Tail Pointer\<close>

text \<open>
  We show the Hoare triple with \verb+{Q) incr_tail {R}+.
\<close>

lemma  CleanQ_RB_incr_tail_x_hoare:
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>  
    \<lbrace>  CleanQ_RB_deq_x_Q K \<acute>CRB b \<rbrace> 
        \<acute>CRB := (CleanQ_RB_incr_tail_x b \<acute>CRB)
    \<lbrace> CleanQ_RB_deq_x_R K \<acute>CRB b\<rbrace>,\<lbrace>True\<rbrace>" 
  apply(oghoare)
  using CleanQ_RB_deq_x_all_inv by fastforce


lemma  CleanQ_RB_incr_tail_y_hoare:
   "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub> 
    \<lbrace>  CleanQ_RB_deq_y_Q K \<acute>CRB b \<rbrace> 
      \<acute>CRB := (CleanQ_RB_incr_tail_y b \<acute>CRB)
    \<lbrace> CleanQ_RB_deq_y_R K \<acute> CRB b  \<rbrace>,\<lbrace>True\<rbrace>" 
  apply(oghoare)
  using CleanQ_RB_deq_y_all_inv by fastforce

 
paragraph \<open>Full Dequeue Operation\<close>

text \<open>
  We show the Hoare triple with \verb+{P) deq {R}+.
\<close>

lemma CleanQ_RB_deq_x_hoare : 
   "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>  
    \<lbrace>  CleanQ_RB_deq_x_P K \<acute>CRB  \<rbrace> 
      \<acute>buf := (CleanQ_RB_read_tail_x \<acute>CRB) ;;
    \<lbrace> CleanQ_RB_deq_x_Q K \<acute>CRB \<acute>buf  \<rbrace>
      \<acute>CRB := (CleanQ_RB_incr_tail_x \<acute>buf \<acute>CRB)
    \<lbrace> CleanQ_RB_deq_x_R K \<acute>CRB \<acute>buf  \<rbrace>, \<lbrace>True\<rbrace>"
  apply(oghoare)
  using CleanQ_RB_deq_x_all_inv apply fastforce
  by simp
  

lemma CleanQ_RB_deq_y_hoare : 
   "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>   
    \<lbrace>  CleanQ_RB_deq_y_P K \<acute>CRB  \<rbrace> 
      \<acute>buf := (CleanQ_RB_read_tail_y \<acute>CRB) ;;
    \<lbrace> CleanQ_RB_deq_y_Q K \<acute>CRB \<acute>buf  \<rbrace>
      \<acute>CRB := (CleanQ_RB_incr_tail_y \<acute>buf \<acute>CRB)
    \<lbrace> CleanQ_RB_deq_y_R K \<acute>CRB \<acute>buf  \<rbrace>, \<lbrace>True\<rbrace>"
  apply(oghoare)
  using CleanQ_RB_deq_y_all_inv apply fastforce
  by simp

type_synonym funcs = "string \<times> nat"
datatype faults = Overflow | InvalidMem

definition 
  CleanQ_CRB_deq_x :: "(CleanQ_CRB_State_vars, funcs, faults) ann_com"
  where "CleanQ_CRB_deq_x \<equiv> 
    \<lbrace> CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB \<rbrace>
      \<acute>buf := (CleanQ_RB_read_tail_x \<acute>CRB) ;;
    \<lbrace> CleanQ_RB_deq_x_Q \<acute>uni \<acute>CRB \<acute>buf \<rbrace>
      \<acute>CRB := (CleanQ_RB_incr_tail_x \<acute>buf \<acute>CRB)"


definition 
  CleanQ_CRB_deq_y :: "(CleanQ_CRB_State_vars, funcs, faults) ann_com"
  where "CleanQ_CRB_deq_y \<equiv> 
    \<lbrace> CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB \<rbrace>
      \<acute>buf := (CleanQ_RB_read_tail_y \<acute>CRB) ;;
    \<lbrace> CleanQ_RB_deq_y_Q \<acute>uni \<acute>CRB \<acute>buf \<rbrace>
      \<acute>CRB := (CleanQ_RB_incr_tail_y \<acute>buf \<acute>CRB)"

definition 
  CleanQ_CRB_enq_x :: "nat \<Rightarrow> (CleanQ_CRB_State_vars, funcs, faults) ann_com"
  where "CleanQ_CRB_enq_x bf \<equiv> 
   \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB bf \<rbrace>
    \<acute>CRB := (CleanQ_RB_write_head_x bf \<acute>CRB) ;;
   \<lbrace> CleanQ_RB_enq_x_Q \<acute>uni \<acute>CRB \<acute>buf \<rbrace>
    \<acute>CRB := (CleanQ_RB_incr_head_x bf \<acute>CRB)"

definition 
  CleanQ_CRB_enq_y :: "nat \<Rightarrow> (CleanQ_CRB_State_vars, funcs, faults) ann_com"
  where "CleanQ_CRB_enq_y bf \<equiv> 
   \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB bf \<rbrace>
    \<acute>CRB := (CleanQ_RB_write_head_y bf \<acute>CRB) ;;
   \<lbrace> CleanQ_RB_enq_y_Q \<acute>uni \<acute>CRB \<acute>buf \<rbrace>
    \<acute>CRB := (CleanQ_RB_incr_head_y bf \<acute>CRB)"
(*
definition 
  CleanQ_CRB_x :: "nat \<Rightarrow> (CleanQ_CRB_State_vars, funcs, faults) ann_com"
  where "CleanQ_CRB_x b \<equiv>
   \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<rbrace>
    (InvalidMem, \<lbrace> b \<in> rSX \<acute>CRB \<rbrace>) \<longmapsto>
   \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<rbrace> 
    \<acute>CRB := CleanQ_CRB_enq_x b 
   \<lbrace> CleanQ_RB_enq_x_R \<acute>uni \<acute>CRB b \<rbrace>"
*)

lemma CleanQ_RB_concurent:
     "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/F\<^esub>   
      COBEGIN
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
           \<acute>buf := CleanQ_RB_read_head_x \<acute>CRB
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>
         \<parallel> 
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
          \<acute>buf := CleanQ_RB_read_head_y \<acute>CRB
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>
      COEND
      \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>"
  apply(oghoare)
  by auto

  
end 