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



(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CleanQ_SimpleQ
  imports 
    "../autocorres/autocorres/AutoCorres"
    CleanQ_RB
begin

external_file "CleanQ_SimpleQ.c"

install_C_file "CleanQ_SimpleQ.c"

autocorres [

  (* Name compatibility options *)
  lifted_globals_field_prefix="c_glbl_",
  lifted_globals_field_suffix="",
  function_name_prefix="",
  function_name_suffix="_c_fun",


  (* heap abstraction options *)
    
  (* no_heap_abs = FUNC_NAMES, *)
  (* Disable _heap abstraction_ on the given list of functions. *)

  (* force_heap_abs = FUNC_NAMES, *)
  (* Attempt _heap abstraction_  on the given list of functions *)

(*  heap_abs_syntax, *)
  (* Enable experimental heap abstraction syntactic sugar. *)

  (* skip_heap_abs *)
  (* Completely disable _heap abstraction_ *)


  (* word abstraction options *)

  unsigned_word_abs =   rb_can_deq rb_can_enq rb_enq rb_deq,
  (* Use _word abstraction_  on unsigned integers in the given functions. *)

  no_signed_word_abs = rb_can_enq rb_can_deq rb_enq rb_deq, 
  (* Disable signed  _word abstraction_ on the given list of functions. *)

  (* skip_word_abs, *)
  (* Completely disable _word abstraction_. *)


  (* type strengthening options *)
  ts_rules =  pure option nondet, 
  (* Enable _type strengthening_ to the  following types. pure, option, gets nondet *)

  ts_force nondet =  rb_can_deq rb_can_enq  rb_enq rb_deq,
  (* Force the given functions to be type-strengthened to the given type *)


  (* translation scoping options *)
  (* scope = FUNC_NAMES, *)
  (* Only translate the given functions  and their callees, up to depth `scope_depth`. *)

  (* scope_depth = N, *)
  (* Call depth for `scope` *)


  (* less common, debugging options *)

  (*keep_going, *)
  (* Attempt to ignore certain non-critical  errors. *)

  (* trace_heap_lift = FUNC_NAMES`, *)
  (* Trace the _heap abstraction_ process for each of the given functions.  *)

  (* trace_word_abs = FUNC_NAMES`: *) 
  (* As above, but traces _word abstraction_. *)

  (* trace_opt, *)
  (* As above, but traces internal simplification phases (for all functions).*)

  (* no_opt, *)
  (* Disable some optimisation passes that simplify the AutoCorres output. *)

  gen_word_heaps,
  (* Force _heap abstraction_ to create  abstract heaps for standard `word` types *)


  (* seL4 proof options *)

  no_c_termination
  (*  Generate SIMPL wrappers and correspondence proofs *)

  (* c_locale = Name *)
  (*  Run in this locale, rather than the default locale *)

] "CleanQ_SimpleQ.c"
(* skip_word_abs *)



record buffer =
  base :: nat
  length :: nat

context CleanQ_SimpleQ begin

(* Ring Buffer C parser output. *)
thm rb_init_body_def
thm c_fun_rb_can_enq_def
thm c_fun_rb_init_def
thm rb_can_enq_body_def
thm rb_can_enq_c_fun_def
thm rb_can_enq_def


thm rb_enq_body_def
thm rb_can_deq_body_def

thm rb_deq_body_def
thm rb_can_enq_body_def
term rb_C
term buffer_C
term head_C


(* this one should be the pre-condition for the operation *)
definition rb_valid_c :: " lifted_globals \<Rightarrow> rb_C ptr \<Rightarrow> bool"
  where "rb_valid_c s rb \<longleftrightarrow> is_valid_rb_C s rb 
                            \<and> unat (size_C (heap_rb_C s rb)) > 1 
                            \<and> unat (head_C (heap_rb_C s rb)) < unat(size_C (heap_rb_C s rb))
                            \<and> unat (tail_C (heap_rb_C s rb)) < unat(size_C (heap_rb_C s rb))"


definition
  the_rb :: "lifted_globals \<Rightarrow> buffer_C ptr \<Rightarrow> nat \<Rightarrow> buffer"
  where
  "the_rb s b i =  \<lparr> base = unat (offset_C (heap_buffer_C s (b  +\<^sub>p i))),
                     length = unat (length_C (heap_buffer_C s (b  +\<^sub>p i))) \<rparr>"

definition rb_C_to_CleanQ_RB :: "lifted_globals \<Rightarrow> rb_C ptr \<Rightarrow> buffer  CleanQ_RB"
  where "rb_C_to_CleanQ_RB s rb = \<lparr>  ring = \<lambda>i. the_rb s (ring_C (heap_rb_C s rb)) i,
                                     head =  unat (head_C (heap_rb_C s rb)), 
                                     tail =  unat (tail_C (heap_rb_C s rb)),
                                     size =  unat (size_C (heap_rb_C s rb)) \<rparr>"

lemma c_can_deq:
  fixes rb :: "rb_C ptr"
  shows 
  "\<lbrace> \<lambda>s. rb_valid_c s rb  \<rbrace>
   rb_can_deq_c_fun rb
   \<lbrace> \<lambda> r s. r = (if rb_can_deq (rb_C_to_CleanQ_RB s rb) then 1 else 0) \<rbrace>!"
  apply(subst rb_can_deq_c_fun_def)
  apply(wp)
  unfolding rb_can_deq_def rb_empty_def rb_C_to_CleanQ_RB_def rb_valid_c_def
  by(auto)


lemma foo1:
 "unat (C :: 64 word) = ULONG_MAX \<Longrightarrow> (D :: 64 word) < C \<Longrightarrow> unat (D) < ULONG_MAX"
  by(simp add: word_less_nat_alt)

lemma foo2:
 "unat (C :: 64 word) < ULONG_MAX \<Longrightarrow> (D :: 64 word) < C \<Longrightarrow> unat (D) < ULONG_MAX"
  by(simp add: word_less_nat_alt)

lemma foo3: "unat (C :: 64 word) \<le> ULONG_MAX \<Longrightarrow> (D :: 64 word) < C \<Longrightarrow> unat (D) < ULONG_MAX"
  using foo1 foo2 PackedTypes.order_leE 
  by blast

lemma foo4:
  "unat (C :: 64 word) \<le> ULONG_MAX \<Longrightarrow> (D :: 64 word) < C \<Longrightarrow> Suc (unat (D)) \<le> ULONG_MAX"
  using foo3
  by (simp add: less_eq_Suc_le) 
  



lemma c_can_enq:
  fixes rb :: "rb_C ptr"
  shows 
  "\<lbrace> \<lambda>s. rb_valid_c s rb  \<rbrace>
   rb_can_enq_c_fun rb
   \<lbrace> \<lambda> r s. r = (if rb_can_enq (rb_C_to_CleanQ_RB s rb) then 1 else 0) \<rbrace>!"
  apply(subst rb_can_enq_c_fun_def)
  apply(wp) 
  unfolding rb_can_enq_def rb_full_def rb_C_to_CleanQ_RB_def 
  apply(simp add:rb_valid_c_def)
  using foo4 word_less_nat_alt by fastforce


lemma c_rb_enq:
  fixes rb :: "rb_C ptr" and b :: buffer_C
  assumes full: "rb_can_enq_c_fun rb =  return (0)"
  shows 
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and> s0 = s  \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. r \<noteq> 0 \<rbrace>!"
   apply(subst rb_enq_c_fun_def)
  apply(wp)
   apply(auto)
  apply(subst full)
  apply(wp)
  apply(simp)
  done
 

  
lemma c_rb_enq2:
  fixes rb :: "rb_C ptr" and b :: buffer_C and s0 :: lifted_globals
  assumes full: "rb_can_enq_c_fun rb =  return (0)"
  shows "
   \<lbrace> \<lambda>s. rb_valid_c s rb \<and> s0 = s  \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. r \<noteq> 0 \<and> s = s0 \<rbrace>!"
   apply(subst rb_enq_c_fun_def)
   apply(auto)
    apply(wp)
   apply(simp)
   apply(subst full)
   apply(wp)
  by(simp)
  
lemma c_rb_enq3:
  fixes rb :: "rb_C ptr" and b :: buffer_C and s0 :: lifted_globals
  shows "
   \<lbrace> \<lambda>s. rb_valid_c s rb \<and> s0 = s \<and> rb_can_enq_c_fun rb =  return (0)  \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. r \<noteq> 0 \<and> s = s0 \<rbrace>!"
  apply(subst rb_enq_c_fun_def)
  apply(wp)
  apply(auto)
  apply(subst rb_can_enq_c_fun_def)
  apply(wp)
  apply(auto)
  
  by(simp)


lemma "unat (C) \<le> ULONG_MAX \<Longrightarrow> D < C \<Longrightarrow> unat (D) < ULONG_MAX"


  

  




(* SimpleQ C parser output. *)

thm simpleq_enq_body_def
thm simpleq_deq_body_def
thm simpleq_enq_x_body_def
thm simpleq_enq_y_body_def
thm simpleq_deq_x_body_def
thm simpleq_deq_y_body_def

(* SimpleQ Init C parser output. *)
thm init_x_body_def
thm init_y_body_def
thm init_queue_body_def


end
end
