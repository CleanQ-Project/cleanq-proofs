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
autocorres [heap_abs_syntax, ts_rules = nondet] "CleanQ_SimpleQ.c"

record foo =   
  head :: nat
  tail :: nat
  size :: nat

context CleanQ_SimpleQ begin

(* Ring Buffer C parser output. *)
thm rb_init_body_def
thm rb_init'_def
thm rb_can_enq_body_def
thm rb_can_enq'_def
thm rb_enq_body_def
thm rb_can_deq_body_def

thm rb_deq_body_def




term rb_C





definition rb_C_to_CleanQ_RB :: "lifted_globals \<Rightarrow> rb_C ptr \<Rightarrow> nat  CleanQ_RB"
  where "rb_C_to_CleanQ_RB s rb = \<lparr>  ring = \<lambda>x. 1,
                                     head =  Word.unat (head_C (heap_rb_C s rb)), 
                                     tail =  Word.unat (tail_C (heap_rb_C s rb)),
                                     size =  Word.unat (size_C (heap_rb_C s rb)) \<rparr>"

lemma foo:
  "\<lbrace> \<lambda>s.  is_valid_rb_C s rb \<rbrace> rb_can_deq' rb \<lbrace> \<lambda> r s. r = (if rb_can_deq (rb_C_to_CleanQ_RB s rb) then 1 else 0) \<rbrace>!"
  unfolding  rb_C_to_CleanQ_RB_def rb_can_deq_def rb_empty_def
  apply(simp)
  unfolding rb_can_deq'_def



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
