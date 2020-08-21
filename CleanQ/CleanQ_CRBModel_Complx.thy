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
  Previously we only defined that the ring contians "something".
  Now we define the buffer itself as close as possible to the code 
  we want to proof. 
\<close>

record CleanQ_Buffer =
  region :: nat
  offset :: nat
  length :: nat
  valid_offset :: nat
  valid_length :: nat
  flags :: nat

text \<open>
  the model is exactly the same and we reuse the RB Model. 
\<close>

(*<*)
(* Define some global variables to make Simpl/Complex proofs work *)
record CleanQ_CRB_State_vars = 
  CRB  :: "nat CleanQ_RB_State"
  buf_x :: "nat"
  buf_y :: "nat"
  uni :: "nat set"
(*>*)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Redifining writing/reading a buffer\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
   In reality the writes and reads to a buffer (or the buffer struct) are 
   one per field and concurrent actions can happen during each write. In order
   to model this, we redefine writing and reading a buffer to smaller steps 
\<close>

definition CleanQ_RB_read_tail_region_x :: "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> nat" 
  where "CleanQ_RB_read_tail_region_x rb = region (rb_read_tail (rTYX rb))"

definition CleanQ_RB_read_tail_region_y :: "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> nat" 
  where "CleanQ_RB_read_tail_region_y rb = region (rb_read_tail (rTXY rb))"

definition CleanQ_RB_read_tail_offset_x :: "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> nat" 
  where "CleanQ_RB_read_tail_offset_x rb = offset (rb_read_tail (rTYX rb))"

definition CleanQ_RB_read_tail_offset_y :: "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> nat" 
  where "CleanQ_RB_read_tail_offset_y rb = offset (rb_read_tail (rTXY rb))"

definition CleanQ_RB_read_tail_length_x :: "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> nat" 
  where "CleanQ_RB_read_tail_length_x rb = length (rb_read_tail (rTYX rb))"

definition CleanQ_RB_read_tail_length_y :: "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> nat" 
  where "CleanQ_RB_read_tail_length_y rb = length (rb_read_tail (rTXY rb))"

definition CleanQ_RB_read_tail_valid_offset_x :: "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> nat" 
  where "CleanQ_RB_read_tail_valid_offset_x rb = valid_offset (rb_read_tail (rTYX rb))"

definition CleanQ_RB_read_tail_valid_offset_y :: "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> nat" 
  where "CleanQ_RB_read_tail_valid_offset_y rb = valid_offset (rb_read_tail (rTXY rb))"

definition CleanQ_RB_read_tail_valid_length_x :: "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> nat" 
  where "CleanQ_RB_read_tail_valid_length_x rb = valid_length (rb_read_tail (rTYX rb))"

definition CleanQ_RB_read_tail_valid_length_y :: "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> nat" 
  where "CleanQ_RB_read_tail_valid_length_y rb = valid_length (rb_read_tail (rTXY rb))"

definition CleanQ_RB_read_tail_flags_x :: "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> nat" 
  where "CleanQ_RB_read_tail_flags_x rb = flags (rb_read_tail (rTYX rb))"

definition CleanQ_RB_read_tail_flags_y :: "(CleanQ_Buffer CleanQ_RB_State) \<Rightarrow> nat" 
  where "CleanQ_RB_read_tail_flags_y rb = flags (rb_read_tail (rTXY rb))"

text \<open>
  Show equality 
\<close>

lemma CleanQ_RB_read_tail_x_fields_eq :
  shows "CleanQ_RB_read_tail_x rb =  buffer \<lparr> region := CleanQ_RB_read_tail_region_x rb, 
                       offset := CleanQ_RB_read_tail_offset_x rb,
                       length := CleanQ_RB_read_tail_length_x rb,
                       valid_offset := CleanQ_RB_read_tail_valid_offset_x rb,
                       valid_length := CleanQ_RB_read_tail_valid_length_x rb,
                       flags := CleanQ_RB_read_tail_flags_x rb\<rparr>"
  unfolding CleanQ_RB_read_tail_x_def CleanQ_RB_read_tail_region_x_def 
    CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_length_x_def 
    CleanQ_RB_read_tail_valid_length_x_def CleanQ_RB_read_tail_valid_offset_x_def
    CleanQ_RB_read_tail_flags_x_def 
  by simp 

lemma CleanQ_RB_read_tail_y_fields_eq :
  shows "CleanQ_RB_read_tail_y rb =  buffer \<lparr> region := CleanQ_RB_read_tail_region_y rb, 
                       offset := CleanQ_RB_read_tail_offset_y rb,
                       length := CleanQ_RB_read_tail_length_y rb,
                       valid_offset := CleanQ_RB_read_tail_valid_offset_y rb,
                       valid_length := CleanQ_RB_read_tail_valid_length_y rb,
                       flags := CleanQ_RB_read_tail_flags_y rb\<rparr>"
  unfolding CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_region_y_def 
    CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_length_y_def 
    CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_valid_offset_y_def
    CleanQ_RB_read_tail_flags_y_def 
  by simp 

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Defining enqueue and deuque for Complx\<close>
(* ------------------------------------------------------------------------------------ *)


abbreviation "CleanQ_CRB_enq_x b \<equiv> 
            \<lbrace> CleanQ_RB_Invariants \<acute>uni \<acute>CRB  \<rbrace>
            IF CleanQ_RB_enq_x_possible \<acute>CRB \<and> b \<in> rSX \<acute>CRB
            THEN
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_x b \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_Q \<acute>uni \<acute>CRB b \<rbrace>
                \<acute>CRB := (CleanQ_RB_incr_head_x b \<acute>CRB)
            ELSE 
                \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
                SKIP
            FI"

abbreviation "CleanQ_CRB_enq_y b \<equiv> 
            \<lbrace> CleanQ_RB_Invariants \<acute>uni \<acute>CRB  \<rbrace>
            IF CleanQ_RB_enq_y_possible \<acute>CRB \<and> b \<in> rSY \<acute>CRB
            THEN
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_y b \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_Q \<acute>uni \<acute>CRB b \<rbrace>
                \<acute>CRB := (CleanQ_RB_incr_head_y b \<acute>CRB)
            ELSE 
                \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
                SKIP
            FI"

abbreviation "CleanQ_CRB_deq_x \<equiv> 
            \<lbrace> CleanQ_RB_Invariants \<acute>uni \<acute>CRB  \<rbrace>
            IF CleanQ_RB_deq_x_possible \<acute>CRB
            THEN
              \<lbrace> CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<rbrace>
                \<acute>buf_x := (CleanQ_RB_read_tail_x  \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_deq_x_Q \<acute>uni \<acute>CRB \<acute>buf_x \<rbrace>
                \<acute>CRB := (CleanQ_RB_incr_tail_x \<acute>buf_x \<acute>CRB)
            ELSE 
                \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
                SKIP
            FI"


abbreviation "CleanQ_CRB_deq_y \<equiv> 
            \<lbrace> CleanQ_RB_Invariants \<acute>uni \<acute>CRB  \<rbrace>
            IF CleanQ_RB_deq_y_possible \<acute>CRB
            THEN
              \<lbrace> CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_y \<acute>CRB) \<rbrace>
                \<acute>buf_y := (CleanQ_RB_read_tail_y  \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_deq_y_Q \<acute>uni \<acute>CRB \<acute>buf_y \<rbrace>
                \<acute>CRB := (CleanQ_RB_incr_tail_y \<acute>buf_y \<acute>CRB)
            ELSE 
                \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
                SKIP
            FI"

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
  \<lbrace> CleanQ_RB_deq_x_P K \<acute>CRB \<acute>buf_x \<rbrace> 
    \<acute>buf_x := (CleanQ_RB_read_tail_x \<acute>CRB)
  \<lbrace> CleanQ_RB_deq_x_Q K \<acute>CRB \<acute>buf_x  \<rbrace>, \<lbrace>True\<rbrace>"  
  by(oghoare, auto)
  

lemma  CleanQ_RB_read_tail_y_hoare:
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>  
  \<lbrace> CleanQ_RB_deq_y_P K \<acute>CRB \<acute>buf_y \<rbrace> 
    \<acute>buf_y := (CleanQ_RB_read_tail_y \<acute>CRB)
  \<lbrace> CleanQ_RB_deq_y_Q K \<acute>CRB \<acute>buf_y  \<rbrace>, \<lbrace>True\<rbrace>"  
  by(oghoare, auto)  

paragraph \<open>Incrementing the Tail Pointer\<close>

text \<open>
  We show the Hoare triple with \verb+{Q) incr_tail {R}+.
\<close>

lemma  CleanQ_RB_incr_tail_x_hoare:
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>  
    \<lbrace>  CleanQ_RB_deq_x_Q K \<acute>CRB b \<rbrace> 
        \<acute>CRB := (CleanQ_RB_incr_tail_x b \<acute>CRB)
    \<lbrace> CleanQ_RB_deq_x_R K \<acute>CRB b\<rbrace>,\<lbrace>True\<rbrace>" 
  apply(oghoare, auto)
  using CleanQ_RB_deq_x_all_inv by blast
  
  

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
    \<lbrace>  CleanQ_RB_deq_x_P K \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<rbrace> 
      \<acute>buf_x := (CleanQ_RB_read_tail_x \<acute>CRB) ;;
    \<lbrace> CleanQ_RB_deq_x_Q K \<acute>CRB \<acute>buf_x  \<rbrace>
      \<acute>CRB := (CleanQ_RB_incr_tail_x \<acute>buf_x \<acute>CRB)
    \<lbrace> CleanQ_RB_deq_x_R K \<acute>CRB \<acute>buf_x \<rbrace> , \<lbrace>True\<rbrace>"
  apply(oghoare, auto)
  using CleanQ_RB_deq_x_all_inv by blast
  
  
lemma CleanQ_RB_deq_y_hoare : 
   "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>   
    \<lbrace>  CleanQ_RB_deq_y_P K \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<rbrace> 
      \<acute>buf_y := (CleanQ_RB_read_tail_y \<acute>CRB) ;;
    \<lbrace> CleanQ_RB_deq_y_Q K \<acute>CRB \<acute>buf_y  \<rbrace>
      \<acute>CRB := (CleanQ_RB_incr_tail_y \<acute>buf_y \<acute>CRB)
    \<lbrace> CleanQ_RB_deq_y_R K \<acute>CRB \<acute>buf_y \<rbrace>, \<lbrace>True\<rbrace>"
  apply(oghoare, auto)
  using CleanQ_RB_deq_y_all_inv by blast
  
  
type_synonym funcs = "string \<times> nat"

lemma CleanQ_RB_read_concurent:
     "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/F\<^esub>   
      COBEGIN
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
           \<acute>buf_x := CleanQ_RB_read_head_x \<acute>CRB
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>
         \<parallel> 
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
          \<acute>buf_y := CleanQ_RB_read_head_y \<acute>CRB
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>
      COEND
      \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>"
  apply(oghoare)
  by auto

(* let's try this... I think we could start with this and showing this for all
  four combinations. Then continue with splitting up *)

lemma CleanQ_RB_loop_enq_enq:
     "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/{True}\<^esub>   
      COBEGIN
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         WHILE True INV \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         DO \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
           (True,\<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB bx \<rbrace>) \<longmapsto> 
           \<lbrace>  CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB bx \<rbrace>
          \<acute>CRB := CleanQ_RB_enq_x bx \<acute>CRB
         OD
         \<lbrace>  CleanQ_RB_enq_x_R \<acute>uni \<acute>CRB bx \<rbrace>, \<lbrace>True\<rbrace>  
         \<parallel> 
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         WHILE True INV \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         DO
        \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
          (True, \<lbrace>  CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB by \<rbrace>) \<longmapsto> 
            \<lbrace>  CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB by \<rbrace>
            \<acute>CRB := CleanQ_RB_enq_y by \<acute>CRB
         OD
         \<lbrace>  CleanQ_RB_enq_y_R \<acute>uni \<acute>CRB by \<rbrace>, \<lbrace>True\<rbrace>
      COEND
      \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>"
    apply(oghoare, auto)
  apply (simp add: CleanQ_RB_enq_x_inv_all)
  apply (simp add: CleanQ_RB_enq_x_def CleanQ_RB_enq_y_possible_def)
  apply (simp add: CleanQ_RB_enq_y_inv_all)
  apply (simp add: CleanQ_RB_enq_y_enq_x_possible)
  apply (simp add: CleanQ_RB_enq_x_inv_all)
  apply (simp add: CleanQ_RB_enq_y_inv_all)
  apply (simp add: CleanQ_RB_enq_y_inv_all)
  apply (simp add: CleanQ_RB_enq_x_inv_all)
  apply (simp add: CleanQ_RB_enq_y_inv_all)
  by (simp add: CleanQ_RB_enq_x_inv_all)


lemma CleanQ_RB_loop_enq_deq:
     "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/{True}\<^esub>   
      COBEGIN
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         WHILE True INV \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         DO \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
           (True,\<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB bx \<rbrace>) \<longmapsto> 
           \<lbrace>  CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB bx \<rbrace>
          \<acute>CRB := CleanQ_RB_enq_x bx \<acute>CRB
         OD
         \<lbrace>  CleanQ_RB_enq_x_R \<acute>uni \<acute>CRB bx \<rbrace>, \<lbrace>True\<rbrace>  
         \<parallel> 
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         WHILE True INV \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         DO
        \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
          (True, \<lbrace>  CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB by \<rbrace>) \<longmapsto> 
            \<lbrace>  CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB by \<rbrace>
            \<acute>CRB := CleanQ_RB_deq_y \<acute>CRB
         OD
         \<lbrace>  CleanQ_RB_deq_y_R \<acute>uni \<acute>CRB by \<rbrace>, \<lbrace>True\<rbrace>
      COEND
      \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>"
  apply(oghoare, auto)
  apply (simp add: CleanQ_RB_deq_y_all_inv)
  apply (simp_all add: CleanQ_RB_enq_x_deq_y_possible)
  apply (simp_all add: CleanQ_RB_enq_x_inv_all)
  using CleanQ_RB_deq_y_enq_x_possible apply blast
  using CleanQ_RB_deq_y_all_inv apply blast
  using CleanQ_RB_deq_y_all_inv apply blast
  using CleanQ_RB_deq_y_all_inv by blast
  
  
 
lemma CleanQ_RB_loop_deq_enq:
     "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/{True}\<^esub>   
      COBEGIN
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         WHILE True INV \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         DO \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
           (True,\<lbrace> CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB bx \<rbrace>) \<longmapsto> 
           \<lbrace>  CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB bx \<rbrace>
          \<acute>CRB := CleanQ_RB_deq_x \<acute>CRB
         OD
         \<lbrace>  CleanQ_RB_deq_x_R \<acute>uni \<acute>CRB bx \<rbrace>, \<lbrace>True\<rbrace>  
         \<parallel> 
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         WHILE True INV \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         DO
        \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
          (True, \<lbrace>  CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB by \<rbrace>) \<longmapsto> 
            \<lbrace>  CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB by \<rbrace>
            \<acute>CRB := CleanQ_RB_enq_y by \<acute>CRB 
         OD
         \<lbrace>  CleanQ_RB_enq_y_R \<acute>uni \<acute>CRB by \<rbrace>, \<lbrace>True\<rbrace>
      COEND
      \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>" 
  apply(oghoare, auto)
  apply (simp_all add: CleanQ_RB_enq_y_inv_all)
  apply (simp_all add: CleanQ_RB_enq_y_deq_x_possible)
  using CleanQ_RB_deq_x_all_inv apply blast
  using CleanQ_RB_deq_x_enq_y_possible apply blast
  using CleanQ_RB_deq_x_all_inv apply blast
  using CleanQ_RB_deq_x_all_inv apply blast
  using CleanQ_RB_deq_x_all_inv by blast
    

 lemma CleanQ_RB_loop_deq_deq:
     "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/{True}\<^esub>   
      COBEGIN
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         WHILE True INV \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         DO \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
           (True,\<lbrace> CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<rbrace>) \<longmapsto> 
           \<lbrace>  CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB)  \<rbrace>
          \<acute>CRB := CleanQ_RB_deq_x \<acute>CRB
         OD
         \<lbrace>  CleanQ_RB_deq_x_R \<acute>uni \<acute>CRB \<acute>buf_x \<rbrace>, \<lbrace>True\<rbrace>  
         \<parallel> 
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         WHILE True INV \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         DO
        \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
          (True, \<lbrace>  CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<rbrace>) \<longmapsto> 
            \<lbrace>  CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<rbrace>
            \<acute>CRB := CleanQ_RB_deq_y \<acute>CRB 
         OD
         \<lbrace>  CleanQ_RB_deq_y_R \<acute>uni \<acute>CRB \<acute>buf_y \<rbrace>, \<lbrace>True\<rbrace>
      COEND
      \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>" 
   apply(oghoare, auto)
   apply (simp_all add: CleanQ_RB_deq_x_no_change CleanQ_RB_deq_y_possible_def)
   apply (simp_all add: CleanQ_RB_deq_y_deq_x_possible)
   using CleanQ_RB_deq_x_all_inv apply blast
   apply (simp_all add: CleanQ_RB_deq_y_all_inv CleanQ_RB_deq_y_possible_def)
   using CleanQ_RB_deq_x_all_inv apply blast
   using CleanQ_RB_deq_x_all_inv apply blast
   using CleanQ_RB_deq_x_all_inv by blast
  
lemma CleanQ_RB_concurrent_all:
     "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/{True}\<^esub>   
      COBEGIN
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         WHILE True INV \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         DO \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
              (True, \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB bx \<rbrace>) \<longmapsto> ( 
            \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB bx \<rbrace>
              \<acute>CRB := (CleanQ_RB_write_head_x bx \<acute>CRB) ;;
            \<lbrace> CleanQ_RB_enq_x_Q \<acute>uni \<acute>CRB bx \<rbrace>
              \<acute>CRB := (CleanQ_RB_incr_head_x bx \<acute>CRB)) ;;
            \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
              (True,\<lbrace> CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<rbrace>) \<longmapsto> ( 
            \<lbrace> CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<rbrace>
              \<acute>buf_x := (CleanQ_RB_read_tail_x \<acute>CRB) ;;
            \<lbrace> CleanQ_RB_deq_x_Q \<acute>uni \<acute>CRB \<acute>buf_x \<rbrace>
             \<acute>CRB := (CleanQ_RB_incr_tail_x \<acute>buf_x \<acute>CRB))
         OD
         \<lbrace>  CleanQ_RB_deq_x_R \<acute>uni \<acute>CRB \<acute>buf_x \<rbrace>, \<lbrace>True\<rbrace>  
         \<parallel> 
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         WHILE True INV \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         DO \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
              (True, \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB by \<rbrace>) \<longmapsto> ( 
            \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB by \<rbrace>
              \<acute>CRB := (CleanQ_RB_write_head_y by \<acute>CRB) ;;
            \<lbrace> CleanQ_RB_enq_y_Q \<acute>uni \<acute>CRB by \<rbrace>
              \<acute>CRB := (CleanQ_RB_incr_head_y by \<acute>CRB)) ;;
            \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
              (True,\<lbrace> CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_y \<acute>CRB) \<rbrace>) \<longmapsto> ( 
            \<lbrace> CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_y \<acute>CRB) \<rbrace>
              \<acute>buf_y := (CleanQ_RB_read_tail_y \<acute>CRB) ;;
            \<lbrace> CleanQ_RB_deq_y_Q \<acute>uni \<acute>CRB \<acute>buf_y \<rbrace>
             \<acute>CRB := (CleanQ_RB_incr_tail_y \<acute>buf_y \<acute>CRB))
         OD
         \<lbrace>  CleanQ_RB_deq_y_R \<acute>uni \<acute>CRB \<acute>buf_y \<rbrace>, \<lbrace>True\<rbrace>
      COEND
      \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>" 
  apply(oghoare, auto)
  apply (simp_all add: CleanQ_RB_enq_x_inv_all)
  apply (simp_all add: CleanQ_RB_enq_y_inv_all)
  apply (simp_all add: CleanQ_RB_enq_x_def CleanQ_RB_enq_y_possible_def)
  apply (simp_all add: CleanQ_RB_enq_y_enq_x_possible CleanQ_RB_enq_y_possible_def)
  using CleanQ_RB_deq_x_all_inv apply blast
  using CleanQ_RB_deq_y_all_inv apply blast
  using CleanQ_RB_deq_x_all_inv apply blast
  using CleanQ_RB_deq_x_enq_y_possible CleanQ_RB_enq_y_possible_def apply blast
  using CleanQ_RB_deq_y_all_inv apply blast
  using CleanQ_RB_deq_y_enq_x_possible apply blast
  apply (metis CleanQ_RB_enq_x_def CleanQ_RB_enq_x_deq_y_possible)
  apply (simp add: CleanQ_RB_enq_y_deq_x_possible CleanQ_RB_enq_y_possible_def)
  using CleanQ_RB_deq_x_all_inv apply blast
  apply (simp add: CleanQ_RB_deq_x_no_change CleanQ_RB_deq_y_possible_def)
  using CleanQ_RB_deq_y_all_inv apply blast
  using CleanQ_RB_deq_y_deq_x_possible apply blast
  using CleanQ_RB_deq_x_all_inv apply blast
  using CleanQ_RB_deq_x_enq_y_possible CleanQ_RB_enq_y_possible_def apply blast
  using CleanQ_RB_deq_y_all_inv apply blast
  using CleanQ_RB_deq_y_enq_x_possible apply blast
  apply (simp add: CleanQ_RB_Invariants_def CleanQ_RB_deq_y_possible_def CleanQ_RB_enq_x_possible_def I4_rb_valid_def)
  apply (simp add: CleanQ_RB_enq_y_deq_x_possible CleanQ_RB_enq_y_possible_def)
  using CleanQ_RB_deq_x_all_inv apply blast
  apply (simp add: CleanQ_RB_deq_x_no_change CleanQ_RB_deq_y_possible_def)
  using CleanQ_RB_deq_y_all_inv apply blast
  using CleanQ_RB_deq_y_deq_x_possible apply blast
  using CleanQ_RB_deq_x_all_inv apply blast
  using CleanQ_RB_deq_x_enq_y_possible CleanQ_RB_enq_y_possible_def apply blast
  using CleanQ_RB_deq_y_all_inv apply blast
  using CleanQ_RB_deq_y_enq_x_possible apply blast
  using CleanQ_RB_deq_x_all_inv apply blast
  using CleanQ_RB_deq_y_all_inv apply blast
  apply (metis CleanQ_RB_enq_x_def CleanQ_RB_enq_x_deq_y_possible)
  apply (simp add: CleanQ_RB_enq_y_deq_x_possible CleanQ_RB_enq_y_possible_def)
  using CleanQ_RB_deq_x_all_inv apply blast
  apply (simp add: CleanQ_RB_deq_x_no_change CleanQ_RB_deq_y_possible_def)
  using CleanQ_RB_deq_y_all_inv apply blast
  using CleanQ_RB_deq_y_deq_x_possible apply blast
  using CleanQ_RB_deq_y_all_inv apply blast
  using CleanQ_RB_deq_x_all_inv apply blast
  using CleanQ_RB_deq_y_all_inv apply blast
  using CleanQ_RB_deq_x_all_inv by blast


lemma CleanQ_RB_concurrent_if_all:
     "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/{True}\<^esub>   
      COBEGIN
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         WHILE True INV \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         DO  
            CleanQ_CRB_enq_x b;;
            CleanQ_CRB_deq_x
         OD
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>  
         \<parallel> 
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         WHILE True INV \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         DO 
            CleanQ_CRB_enq_y b2;;
            CleanQ_CRB_deq_y
         OD
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>
      COEND
      \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>" 
  apply(oghoare, auto)
  apply (simp_all add: CleanQ_RB_enq_x_inv_all)
  apply (simp_all add: CleanQ_RB_enq_y_inv_all)
  apply (simp_all add: CleanQ_RB_enq_y_enq_x_possible)
  apply (simp_all add: CleanQ_RB_enq_x_deq_y_possible)
  using CleanQ_RB_deq_x_all_inv apply blast
  using CleanQ_RB_deq_y_all_inv apply blast
  apply (simp_all add: CleanQ_RB_enq_y_deq_x_possible)
  apply (simp_all add: CleanQ_RB_deq_x_all_inv CleanQ_RB_deq_x_equiv_incr_tail)
  apply (simp_all add: CleanQ_RB_deq_x_no_change CleanQ_RB_deq_y_possible_def)
  apply (simp_all add: CleanQ_RB_deq_y_all_inv CleanQ_RB_deq_y_equiv_incr_tail CleanQ_RB_deq_y_possible_def)
  apply (simp_all add: CleanQ_RB_enq_x_def CleanQ_RB_enq_y_possible_def)
  using CleanQ_RB_deq_x_enq_y_possible CleanQ_RB_enq_y_possible_def apply blast
  apply (simp_all add: CleanQ_RB_deq_y_enq_x_possible CleanQ_RB_deq_y_possible_def)
  using CleanQ_RB_deq_y_deq_x_possible apply blast
  using CleanQ_RB_deq_x_enq_y_possible CleanQ_RB_enq_y_possible_def apply blast
  using CleanQ_RB_deq_y_deq_x_possible apply blast
  using CleanQ_RB_deq_x_enq_y_possible CleanQ_RB_enq_y_possible_def apply blast
  using CleanQ_RB_deq_y_deq_x_possible by blast


  
  
  
  
  


end 