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

term ring_C


(* some helper lemmas with the 64-bit words *)

lemma unat_64word_eq_lt_lt:
 "unat (C :: 64 word) = ULONG_MAX \<Longrightarrow> (D :: 64 word) < C \<Longrightarrow> unat (D) < ULONG_MAX"
  by(simp add: word_less_nat_alt)

lemma unat_64word_lt_lt_lt:
 "unat (C :: 64 word) < ULONG_MAX \<Longrightarrow> (D :: 64 word) < C \<Longrightarrow> unat (D) < ULONG_MAX"
  by(simp add: word_less_nat_alt)

lemma unat_64word_leq_lt_lt: 
  "unat (C :: 64 word) \<le> ULONG_MAX \<Longrightarrow> (D :: 64 word) < C \<Longrightarrow> unat (D) < ULONG_MAX"
  using unat_64word_eq_lt_lt unat_64word_lt_lt_lt PackedTypes.order_leE 
  by blast

lemma unat_64word_lt_succ_leq:
  "unat (C :: 64 word) \<le> ULONG_MAX \<Longrightarrow> (D :: 64 word) < C \<Longrightarrow> Suc (unat (D)) \<le> ULONG_MAX"
  using unat_64word_leq_lt_lt  by (simp add: less_eq_Suc_le) 




(* this one should be the pre-condition for the operation *)
definition rb_valid_c :: " lifted_globals \<Rightarrow> rb_C ptr \<Rightarrow> bool"
  where "rb_valid_c s rb \<longleftrightarrow> is_valid_rb_C s rb 
                            \<and> unat (size_C (heap_rb_C s rb)) > 1 
                            \<and> unat (head_C (heap_rb_C s rb)) < unat(size_C (heap_rb_C s rb))
                            \<and> unat (tail_C (heap_rb_C s rb)) < unat(size_C (heap_rb_C s rb)) 
                            \<and> (\<forall>i <  unat (size_C (heap_rb_C s rb)). is_valid_buffer_C s (ring_C (heap_rb_C s rb) +\<^sub>p i))"


definition
  the_rb :: "lifted_globals \<Rightarrow> buffer_C ptr \<Rightarrow> nat \<Rightarrow> buffer"
  where
  "the_rb s b i =  \<lparr> base = unat (offset_C (heap_buffer_C s (b  +\<^sub>p i))),
                     length = unat (length_C (heap_buffer_C s (b  +\<^sub>p i))) \<rparr>"

definition rb_C_to_CleanQ_RB :: "lifted_globals \<Rightarrow> rb_C ptr \<Rightarrow> buffer_C  CleanQ_RB"
  where "rb_C_to_CleanQ_RB s rb = \<lparr>  ring = \<lambda>i. heap_buffer_C s ((ring_C (heap_rb_C s rb))  +\<^sub>p i),
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
  using unat_64word_lt_succ_leq word_less_nat_alt by fastforce


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
   apply(simp add:rb_enq_c_fun_def)
   apply(wp, simp add:full)+
   done

  




lemma c_rb_enq4:
  fixes rb :: "rb_C ptr" and b :: buffer_C and s0 :: lifted_globals
  assumes space: "rb_can_enq_c_fun rb =  return (1)" and prev: "rb0 = rb_C_to_CleanQ_RB s rb"
  shows "
   \<lbrace> \<lambda>s. rb_valid_c s rb \<and> s0 = s  \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. r =0 \<and> s \<noteq> s0 \<and> rb_C_to_CleanQ_RB s rb = rb_enq b rb0  \<rbrace>!"
  apply(simp add:rb_enq_c_fun_def)
  apply(wp)
  apply(simp add:space)
   apply(wp_once)
  apply(auto)
      prefer 5 apply(simp add:rb_valid_c_def)
  prefer 4 apply(simp add:rb_valid_c_def)
  apply (metis int_unat)
    prefer 3 apply(simp add:rb_valid_c_def)
   prefer 2 apply(simp add:rb_enq_def rb_C_to_CleanQ_RB_def prev) 
  apply(simp add:rb_incr_head_def rb_write_def) apply(auto)
  
  sorry




(* ==================================================================================== *)
subsection \<open>Enqueue Operation\<close>
(* ==================================================================================== *)

text \<open>
  For the enqueue operation, we can show that the operation preserves the size of the
  ring buffer, and the tail pointer.
\<close>

lemma c_rb_enq_preserves_size :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and> s0 = s \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. size_C (heap_rb_C s rb) = size_C (heap_rb_C s0 rb)  \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_can_enq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_valid_c_def) 
  apply (metis int_unat)
  apply (simp add: unat_64word_leq_lt_lt Suc_leI word_less_nat_alt)
  done

lemma c_rb_enq_preserves_size2 :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and> size_C (heap_rb_C s rb) = k \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. size_C (heap_rb_C s rb) = k  \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_can_enq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_valid_c_def) 
  apply (metis int_unat)
  apply (simp add: unat_64word_leq_lt_lt Suc_leI word_less_nat_alt)
  done


lemma c_rb_enq_preserves_tail :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and> s0 = s \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. tail_C (heap_rb_C s rb) = tail_C (heap_rb_C s0 rb)  \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_can_enq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_valid_c_def) 
  apply (metis int_unat)
  apply (simp add: unat_64word_leq_lt_lt Suc_leI word_less_nat_alt)
  done

lemma c_rb_enq_preserves_tail2 :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and>  tail_C (heap_rb_C s rb) = k \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s.  tail_C (heap_rb_C s rb) = k  \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_can_enq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_valid_c_def) 
  apply (metis int_unat)
  apply (simp add: unat_64word_leq_lt_lt Suc_leI word_less_nat_alt)
  done


text \<open>
  If the queue is full, and the enqueue operation cannot put another buffer into
  the ring, then the ring buffer remains in the same state. .
\<close>


lemma c_rb_enq_preserves_head :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and> s0 = s \<and> rb_can_enq_c_fun rb = return (0)  \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. head_C (heap_rb_C s rb) = head_C (heap_rb_C s0 rb)  \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
   apply(wp_once)+
   apply(smt hoare_assume_preNF validNF_chain validNF_return)
   done

lemma c_rb_enq_preserves_head2 :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and> head_C (heap_rb_C s rb) = k \<and> rb_can_enq_c_fun rb = return (0) \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. head_C (heap_rb_C s rb) = k \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
   apply(wp_once)+
   apply(smt hoare_assume_preNF validNF_chain validNF_return)
   done

lemma c_rb_enq_preserves_ring :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and> s0 = s \<and> rb_can_enq_c_fun rb = return (0)  \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. ring_C (heap_rb_C s rb) = ring_C (heap_rb_C s0 rb)  \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
   apply(wp_once)+
   apply(smt hoare_assume_preNF validNF_chain validNF_return)
   done


lemma c_rb_enq_preserves_ring2 :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and> ring_C (heap_rb_C s rb) = k \<and> rb_can_enq_c_fun rb = return (0) \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. ring_C (heap_rb_C s rb) = k  \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
   apply(wp_once)+
   apply(smt hoare_assume_preNF validNF_chain validNF_return)
   done

text \<open>
  In fact, if the ring buffer is full, then the state is not altered at all.
\<close>

lemma c_rb_enq_full_preserves_state:
  fixes rb :: "rb_C ptr" and b :: buffer_C
  shows "
   \<lbrace> \<lambda>s. rb_valid_c s rb \<and> s0 = s \<and> rb_can_enq_c_fun rb =  return (0)  \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. r \<noteq> 0 \<and> s = s0 \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
  apply(wp_once)+
  apply(simp)
  apply (smt hoare_assume_preNF validNF_chain validNF_return)
  done



(* ==================================================================================== *)
subsection \<open>Dequeue Operation\<close>
(* ==================================================================================== *)

text \<open>
  For the dequeue operation, we can show that the operation preserves the size of the
  ring buffer, and the head pointer.
\<close>

lemma c_rb_deq_preserves_size :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and> s0 = s \<and>  is_valid_buffer_C s b \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. size_C (heap_rb_C s rb) = size_C (heap_rb_C s0 rb) \<rbrace>!"
   apply(simp add:rb_deq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_can_deq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_valid_c_def) 
  apply (metis int_unat)
  done


lemma c_rb_deq_preserves_size2 :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and> size_C (heap_rb_C s rb) = k  \<and>  is_valid_buffer_C s b \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. size_C (heap_rb_C s rb) = k  \<rbrace>!"
   apply(simp add:rb_deq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_can_deq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_valid_c_def)  
  apply (metis int_unat)
  done


lemma c_rb_deq_preserves_head :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and> s0 = s  \<and>  is_valid_buffer_C s b \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. head_C (heap_rb_C s rb) = head_C (heap_rb_C s0 rb)  \<rbrace>!"
   apply(simp add:rb_deq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_can_deq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_valid_c_def) 
  apply (metis int_unat)
  done

lemma c_rb_deq_preserves_head2 :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and>  head_C (heap_rb_C s rb) = k  \<and> is_valid_buffer_C s b \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s.  head_C (heap_rb_C s rb) = k  \<rbrace>!"
   apply(simp add:rb_deq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_can_deq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_valid_c_def)  
  apply (metis int_unat)
  done


text \<open>
  If the queue is empty, and the dequeue operation cannot pull another buffer from
  the ring, then the ring buffer remains in the same state. .
\<close>


lemma c_rb_deq_preserves_tail :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and> s0 = s \<and> rb_can_deq_c_fun rb = return (0)  \<and> is_valid_buffer_C s b \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. tail_C (heap_rb_C s rb) = tail_C (heap_rb_C s0 rb)  \<rbrace>!"
   apply(simp add:rb_deq_c_fun_def)
   apply(wp_once)+
   apply(smt hoare_assume_preNF validNF_chain validNF_return)
   done

lemma c_rb_deq_preserves_tail2 :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and> tail_C (heap_rb_C s rb) = k \<and> rb_can_deq_c_fun rb = return (0)  \<and> is_valid_buffer_C s b \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. tail_C (heap_rb_C s rb) = k \<rbrace>!"
   apply(simp add:rb_deq_c_fun_def)
   apply(wp_once)+
   apply(smt hoare_assume_preNF validNF_chain validNF_return)
   done

lemma c_rb_deq_preserves_ring :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and> s0 = s \<and> rb_can_deq_c_fun rb = return (0) \<and> is_valid_buffer_C s b \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. ring_C (heap_rb_C s rb) = ring_C (heap_rb_C s0 rb)  \<rbrace>!"
   apply(simp add:rb_deq_c_fun_def)
   apply(wp_once)+
   apply(smt hoare_assume_preNF validNF_chain validNF_return)
   done

lemma c_rb_deq_preserves_ring2 :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. rb_valid_c s rb \<and> ring_C (heap_rb_C s rb) = k \<and> rb_can_deq_c_fun rb = return (0)  \<and> is_valid_buffer_C s b \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. ring_C (heap_rb_C s rb) = k  \<rbrace>!"
   apply(simp add:rb_deq_c_fun_def)
   apply(wp_once)+
   apply(smt hoare_assume_preNF validNF_chain validNF_return)
   done

text \<open>
  In fact, if the ring buffer is empty, then the state is not altered at all.
\<close>

lemma c_rb_deq_full_preserves_state:
  fixes rb :: "rb_C ptr" and b :: buffer_C
  shows "
   \<lbrace> \<lambda>s. rb_valid_c s rb \<and> s0 = s \<and> rb_can_enq_c_fun rb =  return (0)  \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. r \<noteq> 0 \<and> s = s0 \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
  apply(wp_once)+
  apply(simp)
  apply (smt hoare_assume_preNF validNF_chain validNF_return)
  done



(* ####################################################### *)


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
