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
  (* heap abstraction options *)
    
  (* no_heap_abs = FUNC_NAMES, *)
  (* Disable _heap abstraction_ on the given list of functions. *)

  (* force_heap_abs = FUNC_NAMES, *)
  (* Attempt _heap abstraction_  on the given list of functions *)

  heap_abs_syntax,
  (* Enable experimental heap abstraction syntactic sugar. *)

  (* skip_heap_abs *)
  (* Completely disable _heap abstraction_ *)


  (* word abstraction options *)

  (* unsigned_word_abs = FUNC_NAMES, *)
  (* Use _word abstraction_  on unsigned integers in the given functions. *)

  (* no_signed_word_abs = FUNC_NAMES, *)
  (* Disable signed  _word abstraction_ on the given list of functions. *)

  (* skip_word_abs, *)
  (* Completely disable _word abstraction_. *)


  (* type strengthening options *)
  (* ts_rules =  pure option nondet, *)
  (* Enable _type strengthening_ to the  following types. pure, option, gets nondet *)

  (* ts_force RULE_NAME = FUNC_NAMES *)
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

  no_c_termination,
  (*  Generate SIMPL wrappers and correspondence proofs *)

  (* c_locale = Name *)
  (*  Run in this locale, rather than the default locale *)


  (* Name compatibility options *)
  lifted_globals_field_prefix="c_glbl_",
  lifted_globals_field_suffix="",
  function_name_prefix="c_fun_",
  function_name_suffix=""
] "CleanQ_SimpleQ.c"
(* skip_word_abs *)


context CleanQ_SimpleQ begin

(* Ring Buffer C parser output. *)
thm rb_init_body_def
thm c_fun_rb_can_enq_def
thm c_fun_rb_init_def
thm rb_can_enq_body_def
thm c_fun_rb_can_enq_def
thm rb_enq_body_def
thm rb_can_deq_body_def

thm rb_deq_body_def
thm rb_can_enq_body_def
term rb_C


definition rb_C_to_CleanQ_RB :: "lifted_globals \<Rightarrow> rb_C ptr \<Rightarrow> nat  CleanQ_RB"
  where "rb_C_to_CleanQ_RB s rb = \<lparr>  ring = \<lambda>x. 1,
                                     head =  Word.unat (head_C (heap_rb_C s rb)), 
                                     tail =  Word.unat (tail_C (heap_rb_C s rb)),
                                     size =  Word.unat (size_C (heap_rb_C s rb)) \<rparr>"

lemma foo:
  "\<lbrace> \<lambda>s. True \<rbrace>
   c_fun_rb_can_deq rb
   \<lbrace> \<lambda> r s. r = 1 \<rbrace>!"
  unfolding rb_can_deq_def apply(vcg)

  unfolding  rb_C_to_CleanQ_RB_def rb_can_deq_def rb_empty_def
  
  
  



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
