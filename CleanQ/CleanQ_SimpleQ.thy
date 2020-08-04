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
    "AutoCorres.AutoCorres"
    CleanQ_RB
begin

(* ==================================================================================== *)
subsection \<open>Constants and Type Definitions\<close>
(* ==================================================================================== *)

text \<open>
  We define a few type synonyms and constants to reason about addresses
\<close>
type_synonym ulong_t = "64 word"
type_synonym uint_t = "32 word"
type_synonym ushort_t = "16 word"

abbreviation "addrlimit \<equiv> (0xffffffffffffffff::ulong_t)"
abbreviation "addrlimitnat \<equiv> (0xffffffffffffffff::nat)"

lemma "addrlimit = of_nat addrlimitnat"
  by(auto)
lemma "unat (addrlimit) = addrlimitnat"
  by(auto)


declare[[show_types ]]
sledgehammer_params[timeout = 120, provers = cvc4 z3 spass e vampire]
  

(* ==================================================================================== *)
subsection \<open>Helper Lemmas\<close>
(* ==================================================================================== *)

lemma unat_64word_eq_lt_lt:
 "unat (C::ulong_t) = ULONG_MAX \<Longrightarrow> (D::ulong_t) < C \<Longrightarrow> unat (D) < ULONG_MAX"
  by(simp add: word_less_nat_alt)

lemma unat_32word_eq_lt_lt:
 "unat (C::uint_t) = UINT_MAX \<Longrightarrow> (D::uint_t) < C \<Longrightarrow> unat (D) < UINT_MAX"
  by(simp add: word_less_nat_alt)

lemma unat_64word_lt_lt_lt:
 "unat (C::ulong_t) < ULONG_MAX \<Longrightarrow> (D::ulong_t) < C \<Longrightarrow> unat (D) < ULONG_MAX"
  by(simp add: word_less_nat_alt)

lemma unat_32word_lt_lt_lt:
 "unat (C::uint_t) < UINT_MAX \<Longrightarrow> (D::uint_t) < C \<Longrightarrow> unat (D) < UINT_MAX"
  by(simp add: word_less_nat_alt)

lemma unat_64word_leq_lt_lt: 
  "unat (C::ulong_t) \<le> ULONG_MAX \<Longrightarrow> (D::ulong_t) < C \<Longrightarrow> unat (D) < ULONG_MAX"
  using unat_64word_eq_lt_lt unat_64word_lt_lt_lt PackedTypes.order_leE 
  by blast

lemma unat_32word_leq_lt_lt: 
  "unat (C::uint_t) \<le> UINT_MAX \<Longrightarrow> (D::uint_t) < C \<Longrightarrow> unat (D) < UINT_MAX"
  using unat_32word_eq_lt_lt unat_32word_lt_lt_lt PackedTypes.order_leE 
  by blast

lemma unat_64word_lt_succ_leq:
  "unat (C::ulong_t) \<le> ULONG_MAX \<Longrightarrow> (D::ulong_t) < C \<Longrightarrow> Suc (unat (D)) \<le> ULONG_MAX"
  using unat_64word_leq_lt_lt  by (simp add: less_eq_Suc_le) 

lemma unat_32word_lt_succ_leq:
  "unat (C::uint_t) \<le> ULONG_MAX \<Longrightarrow> (D::uint_t) < C \<Longrightarrow> Suc (unat (D)) \<le> UINT_MAX"
  using unat_32word_leq_lt_lt  by (simp add: less_eq_Suc_le) 

lemma unat_64word_succ_mod:
  assumes sz: "1 < unat N"  and hlt: "H < N"
  shows
  "unat (((H::ulong_t) + 1) mod (N::ulong_t)) = Suc (unat (H)) mod unat (N)"
  using sz hlt  
  by (metis add.commute less_is_non_zero_p1 unatSuc unat_mod)

lemma unat_32word_succ_mod:
  assumes sz: "1 < unat N"  and hlt: "H < N"
  shows
  "unat (((H::uint_t) + 1) mod (N::uint_t)) = Suc (unat (H)) mod unat (N)"
  using sz hlt  
  by (metis add.commute less_is_non_zero_p1 unatSuc unat_mod)

lemma unat_word_lt: 
  "a < b \<Longrightarrow> unat a < unat b"
  by (simp add: unat_mono)

lemma unat_word_leq: 
  "a \<le> b \<Longrightarrow> unat a \<le> unat b"
  by (simp add: word_le_nat_alt)

lemma word64_mult_inequality:
  assumes notzero: "c \<noteq> 0" 
    and inrangex: "x * unat(c) <  2 ^ 64"
    and inrangey: "unat(y) * unat(c) <  2 ^ 64"
    and neq: "x \<noteq> unat y"
  shows "((of_nat x)::ulong_t) * (c::ulong_t) \<noteq> (y::ulong_t) * (c::ulong_t)"
proof -
  from notzero inrangex have xlim:
    "x < 2 ^ 64"
    by (metis linorder_neqE_nat multi_lessD not_less0 unat_gt_0)

  have xc_limit:
    "unat ((of_nat x)::ulong_t) * unat c < 2 ^ 64"
    using  xlim unat_of_nat64 word_bits_conv inrangex by(auto)

  have xc_equiv:
    "unat (((of_nat x)::ulong_t) * c) = x * unat c"
    using xc_limit unat_mult_lem unat_of_nat64 word_bits_conv inrangex by fastforce
  
  have yc_equiv: 
    "unat (y * c) = unat(y) * unat (c)"
    using inrangey  unat_mult_lem by fastforce

  show ?thesis
    using xc_equiv yc_equiv neq notzero unat_eq_zero
    by force
qed

lemma word64_mult_inequality2:
  assumes notzero: "c \<noteq> 0" 
    and inrangex: " x * unat(c) \<le> unat addrlimit"
    and inrangey: "unat (y) * unat (c) \<le> unat  addrlimit"
    and neq: "x \<noteq> unat y"
  shows "((of_nat x)::ulong_t) * (c::ulong_t) \<noteq> (y::ulong_t) * (c::ulong_t)"
proof -
  from notzero inrangex have xlim0:
    "x \<le> unat addrlimit"
    using dual_order.trans unat_eq_zero by fastforce

  from xlim0 have xlim:
    "x < 2 ^ 64"
    by (metis (mono_tags, hide_lams) le_unat_uoi  word_bits_conv unat_less_2p_word_bits)

   from xlim have xc_limit:
    "unat ((of_nat x)::ulong_t) * unat c < 2 ^ 64"
     by (metis (no_types, hide_lams) le_unat_uoi unat_less_2p_word_bits
                                     unat_of_nat64 word_bits_conv inrangex)

    have xc_equiv:
    "unat (((of_nat x)::ulong_t) * c) = x * unat c"
    using inrangex le_unat_uoi by fastforce
  have yc_equiv: 
    "unat (y * c) = unat(y) * unat (c)"
    using inrangey le_unat_uoi by fastforce

  show ?thesis
    using xc_equiv yc_equiv neq notzero unat_eq_zero 
    by force
qed

lemma word64_multply_const_equaltiy:
assumes notzero: "c \<noteq> (0::ulong_t)"
  and hclimit:  "unat (h) * unat (c) < 2 ^ 64"
  and xclimit:  "x * unat (c) < 2 ^ 64"
shows "((of_nat x)::ulong_t) * (c::ulong_t) = (h::ulong_t) * (c::ulong_t) \<longleftrightarrow> x = unat (h)"
  using hclimit notzero word64_mult_inequality xclimit by fastforce

(* ==================================================================================== *)
subsection \<open>SimpleQ C Implementation\<close>
(* ==================================================================================== *)

text \<open>
  Next we load the CleanQ_SimpleQ.c implementation of a shared-memory ring buffer, and
  show that the C implementation refines the abstract ring buffer implementation.
\<close>

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

  (* heap_abs_syntax, *)
  (* Enable experimental heap abstraction syntactic sugar. *)

  (* skip_heap_abs *)
  (* Completely disable _heap abstraction_ *)


  (* word abstraction options *)

  unsigned_word_abs =   rb_can_deq rb_can_enq rb_enq rb_deq rb_deq_unfolded rb_enq_unfolded ,
  (* Use _word abstraction_  on unsigned integers in the given functions. *)

  no_signed_word_abs =   rb_can_deq rb_can_enq rb_enq rb_deq rb_deq_unfolded rb_enq_unfolded,
  (* Disable signed  _word abstraction_ on the given list of functions. *)

  (* skip_word_abs, *)
  (* Completely disable _word abstraction_. *)


  (* type strengthening options *)
  ts_rules =  pure option nondet, 
  (* Enable _type strengthening_ to the  following types. pure, option, gets nondet *)

  ts_force nondet =   rb_can_deq rb_can_enq rb_enq rb_deq rb_deq_unfolded rb_enq_unfolded,
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

text \<open>
 We can now enter the defined context by autocorres. 
\<close>

context CleanQ_SimpleQ begin

(* ==================================================================================== *)
subsection \<open>C Definitions\<close>
(* ==================================================================================== *)

abbreviation "ERR_OK \<equiv> (0)"
abbreviation "ERR_QUEUE_FULL \<equiv> (-1)"
abbreviation "ERR_QUEUE_EMPTY  \<equiv> (-2)"
abbreviation "ERR_NO_BUFFERS \<equiv> (-3)"

(* ==================================================================================== *)
subsection \<open>Invariant\<close>
(* ==================================================================================== *)

text \<open>
  We now define the validity invariant for the ring buffer struct. We first define
  abbrevations for each of the field
\<close>

abbreviation "c_rb_valid_is_valid s rb \<equiv> is_valid_rb_C s rb"
abbreviation "c_rb_valid_size s rb \<equiv> 1 <  (size_C (heap_rb_C s rb))"
abbreviation "c_rb_valid_head s rb \<equiv> head_C (heap_rb_C s rb) < size_C (heap_rb_C s rb)"
abbreviation "c_rb_valid_tail s rb \<equiv> tail_C (heap_rb_C s rb) < size_C (heap_rb_C s rb)"
abbreviation "c_rb_valid_ring s rb \<equiv> (\<forall>i \<le> uint (size_C (heap_rb_C s rb)). 
                                    is_valid_buffer_C s (ring_C (heap_rb_C s rb) +\<^sub>p i) \<and>
                                    ptr_val (ring_C (heap_rb_C s rb) +\<^sub>p i) \<le> addrlimit)"

(* this one should be the pre-condition for the operation *)
definition c_rb_valid :: "lifted_globals \<Rightarrow> rb_C ptr \<Rightarrow> bool"
  where "c_rb_valid s rb \<longleftrightarrow> c_rb_valid_is_valid s rb 
                            \<and> c_rb_valid_size s rb  \<and> c_rb_valid_head s rb
                            \<and> c_rb_valid_tail s rb  \<and> c_rb_valid_ring s rb"


text "We can now define the set of valid entries in the ring buffer"

definition c_rb_valid_entries :: "lifted_globals \<Rightarrow> rb_C ptr \<Rightarrow> nat list"
  where "c_rb_valid_entries s rb = 
            (if (tail_C (heap_rb_C s rb)) \<le> (head_C (heap_rb_C s rb))
             then [unat (tail_C (heap_rb_C s rb)) ..< unat (head_C (heap_rb_C s rb))]
             else [unat (tail_C (heap_rb_C s rb))..< unat (size_C (heap_rb_C s rb))]
                     @ [0..<unat (head_C (heap_rb_C s rb))])"


definition c_rb_empty ::  "lifted_globals \<Rightarrow> rb_C ptr \<Rightarrow> bool"
  where "c_rb_empty s rb = (tail_C (heap_rb_C s rb) = head_C (heap_rb_C s rb))"



lemma c_rb_not_empty_valid_entries:
  "c_rb_valid s0 rb \<Longrightarrow> \<not> c_rb_empty s0 rb \<Longrightarrow> c_rb_valid_entries s0 rb \<noteq> []"
  unfolding c_rb_valid_entries_def c_rb_valid_def c_rb_empty_def
  apply(auto simp add: word_le_nat_alt) 
  using dual_order.antisym apply fastforce
  using unat_eq_zero apply force
  using leD unat_word_lt by blast


lemma c_rb_valid_entries_head_not_in_set:
  "unat (head_C (heap_rb_C s0 rb)) \<notin> set (c_rb_valid_entries s0 rb)"
  unfolding c_rb_valid_entries_def 
  by (auto simp: word_le_nat_alt)



lemma c_rb_valid_entries_tail_first1:
  "c_rb_valid s0 rb \<Longrightarrow> \<not> c_rb_empty s0 rb \<Longrightarrow>
       unat (tail_C (heap_rb_C s0 rb)) = hd (c_rb_valid_entries s0 rb)"
proof -
  assume p1: "c_rb_valid s0 rb"
  assume p2: "\<not> c_rb_empty s0 rb"

  from p1 have p3: "  unat (tail_C (heap_rb_C s0 rb)) < unat (size_C (heap_rb_C s0 rb))"
    by(simp add:unat_mono c_rb_valid_def)

  show "unat (tail_C (heap_rb_C s0 rb)) = hd (c_rb_valid_entries s0 rb)"
    using p3  unfolding c_rb_valid_entries_def apply(auto simp:unat_word_lt)  
    by (metis CleanQ_SimpleQ.c_rb_empty_def hd_upt order_leE p2 word_less_nat_alt)
qed
  


lemma c_rb_valid_entries_tail_in_set:
  "c_rb_valid s0 rb \<Longrightarrow> \<not> c_rb_empty s0 rb \<Longrightarrow>
    unat (tail_C (heap_rb_C s0 rb)) \<in> set (c_rb_valid_entries s0 rb)"
  using c_rb_valid_entries_tail_first1 c_rb_not_empty_valid_entries
  by(auto)
  



(* ==================================================================================== *)
subsection \<open>State Lifting\<close>
(* ==================================================================================== *)


text \<open>
  We now define the lifting function which converts the \verb+rb_C+ object into a
  \verb+CleanQ_RB+ record. We use the \verb+buffer_C+ representation for the buffer 
  descriptor type in the record.
\<close>

(* 
definition
  the_rb :: "lifted_globals \<Rightarrow> buffer_C ptr \<Rightarrow> nat \<Rightarrow> buffer"
  where
  "the_rb s b i =  \<lparr> base = unat (offset_C (heap_buffer_C s (b  +\<^sub>p i))),
                     length = unat (length_C (heap_buffer_C s (b  +\<^sub>p i))) \<rparr>"
*)

(* XXX: Should the ring here be taking the size of the ring buffer into account? 
      ring = \<lambda>i. (if i <  size_C (heap_rb_C s rb) then heap_buffer_C s ((ring_C (heap_rb_C s rb))  +\<^sub>p i)),
*)
definition rb_C_to_CleanQ_RB :: "lifted_globals \<Rightarrow> rb_C ptr \<Rightarrow> buffer_C  CleanQ_RB"
  where "rb_C_to_CleanQ_RB s rb = \<lparr> 
                  ring = \<lambda>i. (if i < unat (size_C (heap_rb_C s rb))
                               then Some (heap_buffer_C s (ring_C (heap_rb_C s rb)  +\<^sub>p i))
                               else None),
                  head =  unat (head_C (heap_rb_C s rb)), 
                  tail =  unat (tail_C (heap_rb_C s rb)),
                  size =  unat (size_C (heap_rb_C s rb)) \<rparr>"

text \<open>
  We can now show that if the C ringbuffer is valid, then the lifted state is also
  satisfying the validity predicate of the \verb+CleanQ_RB+ model.
\<close>


lemma "c_rb_valid s rb \<longrightarrow> rb_valid (rb_C_to_CleanQ_RB s rb)"
  unfolding c_rb_valid_def rb_valid_def rb_C_to_CleanQ_RB_def
  using unat_word_lt
  oops


(* ==================================================================================== *)
subsection \<open>Dequeue Operation\<close>
(* ==================================================================================== *)

text \<open>
  Whether or not the dequeue operation performs the update, depends on whether the
  the ring buffer is empty or not. We first show that the \verb+rb_can_deq+ function in 
  C produces the same result as the corresponding definition in the \verb+CleanQ_RB+ 
  model.
\<close>

lemma c_can_deq:
  "\<lbrace> \<lambda>s. c_rb_valid s rb  \<rbrace>
   rb_can_deq_c_fun rb
   \<lbrace> \<lambda> r s. to_bool r =  rb_can_deq (rb_C_to_CleanQ_RB s rb) \<rbrace>!"
  apply(subst rb_can_deq_c_fun_def)
  apply(wp)
  apply (simp add:rb_can_deq_def rb_empty_def rb_C_to_CleanQ_RB_def c_rb_valid_def)
  done


lemma c_can_deq_return_values:
  "\<lbrace> \<lambda>s. is_valid_rb_C s rb  \<rbrace>
   rb_can_deq_c_fun rb 
   \<lbrace> \<lambda> r s. r =  0 \<or> r = 1  \<rbrace>!"
  unfolding rb_can_deq_c_fun_def
  by(wp, auto)  

text \<open>
  For the dequeue operation, we can show that the operation preserves the size of the
  ring buffer, and the head pointer.
\<close>

lemma c_rb_deq_preserves_size :
  fixes rb :: "rb_C ptr"
  shows
  "\<And>s0. \<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s \<and> is_valid_buffer_C s b \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. size_C (heap_rb_C s rb) = size_C (heap_rb_C s0 rb) \<rbrace>!"
   apply(simp add:rb_deq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_can_deq_c_fun_def)
  apply(wp_once)+
  apply(simp add:c_rb_valid_def)
  by (metis less_imp_le uint_0_iff uint_lt_0 unat_gt_0  word_less_def)
  


lemma c_rb_deq_preserves_size2 :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> size_C (heap_rb_C s rb) = k  \<and>  is_valid_buffer_C s b \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. size_C (heap_rb_C s rb) = k  \<rbrace>!"
   apply(simp add:rb_deq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_can_deq_c_fun_def)
  apply(wp_once)+
  apply(simp add:c_rb_valid_def)
  by (metis less_imp_le uint_0_iff uint_lt_0 unat_gt_0  word_less_def)


lemma c_rb_deq_preserves_head :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s  \<and>  is_valid_buffer_C s b \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. head_C (heap_rb_C s rb) = head_C (heap_rb_C s0 rb)  \<rbrace>!"
   apply(simp add:rb_deq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_can_deq_c_fun_def)
  apply(wp_once)+
  apply(simp add:c_rb_valid_def)
  by (metis less_imp_le uint_0_iff uint_lt_0 unat_gt_0  word_less_def)

lemma c_rb_deq_preserves_head2 :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and>  head_C (heap_rb_C s rb) = k  \<and> is_valid_buffer_C s b \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s.  head_C (heap_rb_C s rb) = k  \<rbrace>!"
  apply(simp add:rb_deq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_can_deq_c_fun_def)
  apply(wp_once)+
  apply(simp add:c_rb_valid_def)
  by (metis less_imp_le uint_0_iff uint_lt_0 unat_gt_0  word_less_def)


text \<open>
  If the queue is empty, and the dequeue operation cannot pull another buffer from
  the ring, then the ring buffer remains in the same state. .
\<close>


lemma c_rb_deq_preserves_tail :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s \<and> rb_can_deq_c_fun rb = return (0)  \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. tail_C (heap_rb_C s rb) = tail_C (heap_rb_C s0 rb)  \<rbrace>!"
  apply(simp add:rb_deq_c_fun_def)
  apply(wp_once)+
  apply(smt hoare_assume_preNF validNF_chain validNF_return)
  done

lemma c_rb_deq_preserves_tail2 :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> tail_C (heap_rb_C s rb) = k \<and> rb_can_deq_c_fun rb = return (0) \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. tail_C (heap_rb_C s rb) = k \<rbrace>!"
  apply(simp add:rb_deq_c_fun_def)
  apply(wp_once)+
  apply(smt hoare_assume_preNF validNF_chain validNF_return)
  done

text \<open>
  The dequeue operation does not change the ring at all
\<close>

lemma c_rb_deq_preserves_ring :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s \<and> is_valid_buffer_C s0 b  \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. ring_C (heap_rb_C s rb) = ring_C (heap_rb_C s0 rb)  \<rbrace>!"
   apply(simp add:rb_deq_c_fun_def)
  apply(wp_once)+
  apply(simp add:rb_can_deq_c_fun_def)
  apply(wp_once)+
  apply(auto simp add:c_rb_valid_def)
  using unat_word_lt apply fastforce
  using word_le_def word_le_less_eq apply blast 
  done

lemma c_rb_deq_preserves_ring2 :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> ring_C (heap_rb_C s rb) = k \<and> is_valid_buffer_C s b \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. ring_C (heap_rb_C s rb) = k  \<rbrace>!"
   apply(simp add:rb_deq_c_fun_def)
  apply(wp_once)+
  apply(simp add:rb_can_deq_c_fun_def)
  apply(wp_once)+
  apply(auto simp add:c_rb_valid_def)
  using unat_word_lt apply fastforce
  using word_le_def word_le_less_eq apply blast 
  done

text \<open>
  Also, the ring contents are not changed. 
\<close>

lemma c_rb_deq_preserves_ring_contents :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s \<and> is_valid_buffer_C s0 b 
    \<and> (\<forall>i < size_C (heap_rb_C s rb).  (ring_C (heap_rb_C s rb)  +\<^sub>p uint i) \<noteq> b)   \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. \<forall>i < size_C (heap_rb_C s rb). 
        heap_buffer_C s (ring_C (heap_rb_C s rb)  +\<^sub>p uint i) = 
        heap_buffer_C s0 (ring_C (heap_rb_C s0 rb) +\<^sub>p uint i)  \<rbrace>!"
   apply(simp add:rb_deq_c_fun_def)
  apply(wp_once)+
  apply(simp add:rb_can_deq_c_fun_def)
  apply(wp_once)+
  apply(auto simp add:c_rb_valid_def)
  using unat_word_lt apply fastforce
  using word_le_def word_le_less_eq apply blast 
  using unat_word_lt apply fastforce
  using less_imp_le word_le_def apply blast
  done


text \<open>
  In fact, if the ring buffer is empty, then the state is not altered at all.
\<close>

lemma c_rb_deq_empty_preserves_state:
  fixes rb :: "rb_C ptr" and b :: buffer_C
  shows "
   \<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s \<and> rb_can_enq_c_fun rb =  return (0)  \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. r \<noteq> 0 \<and> s = s0 \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
  apply(wp_once)+
  apply(simp)
  apply (smt hoare_assume_preNF validNF_chain validNF_return)
  done

text \<open>
  We can show that the dequeue function preserves the valid predicate.
\<close>

lemma c_rb_deq_remains_valid:
  fixes rb :: "rb_C ptr" 
  shows "
   \<lbrace> \<lambda>s. c_rb_valid s rb \<and> is_valid_buffer_C s b  \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s.  c_rb_valid s rb \<rbrace>!"
  apply(simp add:rb_deq_c_fun_def)
  apply(wp_once)+
  apply(simp add:rb_can_deq_c_fun_def)
  apply(wp_once)+
  apply(simp add:c_rb_valid_def)
  by (metis not_gr_zero not_less0 unat_0 word_le_def word_le_less_eq word_less_nat_alt 
            word_mod_less_divisor)


text \<open>
  Lastly, we can show that the C implementation of the dequeue operation produces the 
  same outcome as doing the abstraction operation.
\<close>

lemma c_rb_deq_state_update_head:
"\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s \<and> rb0 = rb_C_to_CleanQ_RB s rb  
        \<and> is_valid_buffer_C s0 b  \<rbrace>
   rb_deq_c_fun rb b
 \<lbrace> \<lambda> r s. head (rb_C_to_CleanQ_RB s rb) = head (snd (rb_deq rb0)) \<rbrace>!"
  unfolding rb_deq_c_fun_def
  apply(wp_once)+
  apply(simp add:rb_can_deq_c_fun_def)
  apply(wp_once)+
  apply(simp add:c_rb_valid_def rb_deq_equiv rb_deq_alt_def rb_C_to_CleanQ_RB_def)
  using less_imp_le unat_1_0  word_le_def word_le_less_eq by blast

  
lemma c_rb_deq_state_update_tail:
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s \<and> rb0 = rb_C_to_CleanQ_RB s rb   \<and> is_valid_buffer_C s0 b  \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. (r = ERR_OK \<or> r = ERR_QUEUE_EMPTY) \<and>
      (if r = ERR_OK then tail (rb_C_to_CleanQ_RB s rb) = tail (snd (rb_deq rb0)) 
       else s = s0)  \<rbrace>!"
  unfolding rb_deq_c_fun_def
  apply(wp_once)+
  apply(simp add:rb_can_deq_c_fun_def)
  apply(wp_once)+
  apply(auto simp add:c_rb_valid_def rb_deq_equiv rb_deq_alt_def rb_C_to_CleanQ_RB_def)
  using unat_32word_succ_mod unat_word_lt apply fastforce
  using unat_gt_0 apply fastforce
  using word_le_def word_le_less_eq by blast


lemma c_rb_deq_state_update_size:
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s 
                \<and> rb0 = rb_C_to_CleanQ_RB s rb  \<and> is_valid_buffer_C s0 b  \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s.  (r = ERR_OK \<or> r = ERR_QUEUE_EMPTY) \<and>
              size (rb_C_to_CleanQ_RB s rb) = size (snd (rb_deq rb0)) \<rbrace>!"
  unfolding rb_deq_c_fun_def
  apply(wp_once)+
  apply(simp add:rb_can_deq_c_fun_def)
  apply(wp_once)+
  apply(simp add:c_rb_valid_def rb_deq_equiv rb_deq_alt_def rb_C_to_CleanQ_RB_def)
  using less_imp_le unat_1_0  word_le_def word_le_less_eq by blast


lemma c_rb_deq_state_update_ring:
  assumes notinring: "(\<forall>i \<le> uint (size_C (heap_rb_C s0 rb)). 
                                     (ring_C (heap_rb_C s0 rb) +\<^sub>p i) \<noteq> b)"
  shows "
   \<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s  
                \<and> rb0 = rb_C_to_CleanQ_RB s rb  \<and> is_valid_buffer_C s b  \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. (r = ERR_OK \<or> r = ERR_QUEUE_EMPTY) \<and> 
         (if r = ERR_OK then \<forall> i < uint (size_C (heap_rb_C s rb)). ring (rb_C_to_CleanQ_RB s rb) i = ring (snd (rb_deq rb0)) i
         else s = s0)  \<rbrace>!"
  unfolding rb_deq_c_fun_def
  apply(wp_once)+
  apply(simp add:rb_can_deq_c_fun_def)
  apply(wp_once)+ 
  apply(auto simp:c_rb_valid_def  rb_deq_equiv rb_deq_alt_def)
  prefer 3 using word_le_def word_le_less_eq apply blast
   prefer 2 using unat_word_lt apply fastforce
  unfolding rb_C_to_CleanQ_RB_def using notinring by(auto)

lemma c_rb_deq_buffer:
  assumes notinring: "(\<forall>i \<le> uint (size_C (heap_rb_C s0 rb)). 
                                     (ring_C (heap_rb_C s0 rb) +\<^sub>p i) \<noteq> b)"
  shows "
   \<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s  \<and> rb0 = rb_C_to_CleanQ_RB s rb \<and>  is_valid_buffer_C s0 b  \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. (r = ERR_OK \<or> r = ERR_QUEUE_EMPTY) \<and> 
        (if r = ERR_OK then heap_buffer_C s b = fst (rb_deq rb0) else s = s0)
    \<rbrace>!"
  unfolding rb_deq_c_fun_def
  apply(wp_once)+
  apply(simp add:rb_can_deq_c_fun_def)
  apply(wp_once)+ 
  apply(auto simp:c_rb_valid_def  rb_deq_equiv rb_deq_alt_def)
  prefer 3 
  using word_le_def word_le_less_eq apply blast
   prefer 2  
  using unat_word_lt apply fastforce
  unfolding rb_C_to_CleanQ_RB_def rb_deq_def rb_read_tail_def
  apply (simp add: int_unat)
  using unat_word_lt by blast


lemma ringhelper:
  "ring_C (heap_rb_C (heap_rb_C_update (\<lambda>a::rb_C ptr \<Rightarrow> rb_C. a(rb := tail_C_update (\<lambda>a::32 word. (tail_C (heap_rb_C s0 rb) + (1::32 word)) mod size_C (heap_rb_C s0 rb)) (a rb)))
                      (heap_buffer_C_update (\<lambda>a::buffer_C ptr \<Rightarrow> buffer_C. a(b := heap_buffer_C s0 (ring_C (heap_rb_C s0 rb) +\<^sub>p uint (tail_C (heap_rb_C s0 rb))))) s0))
                    rb) = ring_C (heap_rb_C s0 rb)"
  by(auto)

lemma bufferhelper:
  " heap_buffer_C
                (heap_rb_C_update (\<lambda>a::rb_C ptr \<Rightarrow> rb_C. a(rb := tail_C_update (\<lambda>a::32 word. (tail_C (heap_rb_C s0 rb) + (1::32 word)) mod size_C (heap_rb_C s0 rb)) (a rb)))
                  (heap_buffer_C_update (\<lambda>a::buffer_C ptr \<Rightarrow> buffer_C. a(b := heap_buffer_C s0 (ring_C (heap_rb_C s0 rb) +\<^sub>p uint (tail_C (heap_rb_C s0 rb))))) s0)) = 
         heap_buffer_C
                  (heap_buffer_C_update (\<lambda>a::buffer_C ptr \<Rightarrow> buffer_C. a(b := heap_buffer_C s0 (ring_C (heap_rb_C s0 rb) +\<^sub>p uint (tail_C (heap_rb_C s0 rb))))) s0)"
  by(auto)

lemma bufferhelper2:
  " (i::nat) < uint (size_C (heap_rb_C s0 rb)) \<Longrightarrow> (ring_C (heap_rb_C s0 rb) +\<^sub>p i) \<noteq> b \<Longrightarrow>
  (heap_buffer_C (heap_buffer_C_update (\<lambda>a::buffer_C ptr \<Rightarrow> buffer_C. a(b := heap_buffer_C s0 (ring_C (heap_rb_C s0 rb) +\<^sub>p uint (tail_C (heap_rb_C s0 rb))))) s0) (ring_C (heap_rb_C s0 rb) +\<^sub>p int i)) 
  =  (heap_buffer_C (s0) (ring_C (heap_rb_C s0 rb) +\<^sub>p int i))"
  by(auto)

lemma c_rb_deq_correct:
  assumes notinring: "(\<forall>i < uint (size_C (heap_rb_C s0 rb)). 
                                     (ring_C (heap_rb_C s0 rb) +\<^sub>p i) \<noteq> b)"
  shows "
   \<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s  \<and> rb0 = rb_C_to_CleanQ_RB s rb \<and>  is_valid_buffer_C s0 b  \<rbrace>
   rb_deq_c_fun rb b
   \<lbrace> \<lambda> r s. (r = ERR_OK \<or> r = ERR_QUEUE_EMPTY) \<and> 
        (if r = ERR_OK then rb_C_to_CleanQ_RB s rb = snd (rb_deq rb0) else s = s0)
    \<rbrace>!"
   unfolding rb_deq_c_fun_def
  apply(wp_once)+
  apply(simp add:rb_can_deq_c_fun_def)
  apply(wp_once)+ 
  apply(auto simp:c_rb_valid_def  rb_deq_equiv rb_deq_alt_def)
  prefer 3 
  using word_le_def word_le_less_eq apply blast
  prefer 2  
  using unat_word_lt apply fastforce
  unfolding rb_C_to_CleanQ_RB_def
  apply(auto)
  prefer 2 
  using unat_32word_succ_mod unat_word_lt apply fastforce
  apply(subst ringhelper)
  apply(subst bufferhelper)
(* WHOAH.... *)
proof -
  have "\<forall>n na. \<not> n < unat (size_C (heap_rb_C s0 rb)) \<or> \<not> na < unat (size_C (heap_rb_C s0 rb)) \<or> n < unat (size_C (heap_rb_C s0 rb)) \<and> na < unat (size_C (heap_rb_C s0 rb)) \<and> Some (heap_buffer_C (heap_buffer_C_update (\<lambda>f. f (b := heap_buffer_C s0 (ring_C (heap_rb_C s0 rb) +\<^sub>p uint (tail_C (heap_rb_C s0 rb))))) s0) (ring_C (heap_rb_C s0 rb) +\<^sub>p int na)) = Some (heap_buffer_C s0 (ring_C (heap_rb_C s0 rb) +\<^sub>p int na))"
    by (metis CleanQ_SimpleQ.bufferhelper2 int_unat notinring of_nat_less_iff)
  then show "(\<lambda>n. if n < unat (size_C (heap_rb_C s0 rb)) then Some (heap_buffer_C (heap_buffer_C_update (\<lambda>f. f (b := heap_buffer_C s0 (ring_C (heap_rb_C s0 rb) +\<^sub>p uint (tail_C (heap_rb_C s0 rb))))) s0) (ring_C (heap_rb_C s0 rb) +\<^sub>p int n)) else None) = (\<lambda>n. if n < unat (size_C (heap_rb_C s0 rb)) then Some (heap_buffer_C s0 (ring_C (heap_rb_C s0 rb) +\<^sub>p int n)) else None)"
    by meson
qed

 
thm rb_enq_c_fun_def
thm rb_can_enq_c_fun_def


(* ==================================================================================== *)
subsection \<open>Enqueue Operation\<close>
(* ==================================================================================== *)

text \<open>
  Whether or not the enqueue operation performs the update, depends on whether the
  the ring buffer is full or not. We first show that the \verb+rb_can_enq+ function in 
  C produces the same result as the corresponding definition in the \verb+CleanQ_RB+ 
  model.
\<close>

lemma c_can_enq:
  fixes rb :: "rb_C ptr"
  shows 
  "\<lbrace> \<lambda>s. c_rb_valid s rb  \<rbrace>
   rb_can_enq_c_fun rb
   \<lbrace> \<lambda> r s. to_bool r =  rb_can_enq (rb_C_to_CleanQ_RB s rb) \<rbrace>!"
  apply(subst rb_can_enq_c_fun_def)
  apply(wp, simp add:rb_can_enq_def rb_full_def rb_C_to_CleanQ_RB_def c_rb_valid_def)
  using Suc_le_eq unat_32word_leq_lt_lt unat_word_lt by fastforce


lemma c_can_enq_return_values:
  "\<lbrace> \<lambda>s. c_rb_valid s rb  \<rbrace>
   rb_can_enq_c_fun rb 
   \<lbrace> \<lambda> r s. r =  0 \<or> r = 1  \<rbrace>!"
  unfolding rb_can_enq_c_fun_def
  apply(wp, simp)
  using c_rb_valid_def unat_32word_leq_lt_lt unat_gt_0 by fastforce


text \<open>
  For the enqueue operation, we can show that the operation preserves the size of the
  ring buffer, and the tail pointer.
\<close>

lemma c_rb_enq_preserves_size :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. size_C (heap_rb_C s rb) = size_C (heap_rb_C s0 rb)  \<rbrace>!"
  apply(simp add:rb_enq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_can_enq_c_fun_def)
  apply(wp_once)+
  apply(simp add:c_rb_valid_def unat_word_leq word_less_nat_alt) 
  by (meson INT_MIN_MAX_lemmas(12) Suc_leI le_eq_less_or_eq less_le_trans un_ui_le)
  

lemma c_rb_enq_preserves_size2 :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> size_C (heap_rb_C s rb) = k \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. size_C (heap_rb_C s rb) = k  \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_can_enq_c_fun_def)
  apply(wp_once)+
  apply(simp add:c_rb_valid_def unat_word_leq word_less_nat_alt) 
  by (meson INT_MIN_MAX_lemmas(12) Suc_le_eq less_imp_le_nat less_le_trans un_ui_le)


lemma c_rb_enq_preserves_tail :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. tail_C (heap_rb_C s rb) = tail_C (heap_rb_C s0 rb)  \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_can_enq_c_fun_def)
  apply(wp_once)+
  apply(simp add:c_rb_valid_def word_less_nat_alt) 
  by (meson INT_MIN_MAX_lemmas(12) Suc_leI le_eq_less_or_eq less_le_trans un_ui_le)

lemma c_rb_enq_preserves_tail2 :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and>  tail_C (heap_rb_C s rb) = k \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s.  tail_C (heap_rb_C s rb) = k  \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:rb_can_enq_c_fun_def)
  apply(wp_once)+
  apply(simp add:c_rb_valid_def word_less_nat_alt) 
  by (meson INT_MIN_MAX_lemmas(12) Suc_le_eq less_imp_le_nat less_le_trans un_ui_le)


text \<open>
  If the queue is full, and the enqueue operation cannot put another buffer into
  the ring, then the ring buffer remains in the same state. .
\<close>


lemma c_rb_enq_preserves_head :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s \<and> rb_can_enq_c_fun rb = return (0)  \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. head_C (heap_rb_C s rb) = head_C (heap_rb_C s0 rb)  \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
   apply(wp_once)+
   apply(smt hoare_assume_preNF validNF_chain validNF_return)
   done

lemma c_rb_enq_preserves_head2 :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> head_C (heap_rb_C s rb) = k \<and> rb_can_enq_c_fun rb = return (0) \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. head_C (heap_rb_C s rb) = k \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
   apply(wp_once)+
   apply(smt hoare_assume_preNF validNF_chain validNF_return)
   done
 
lemma c_rb_enq_preserves_ring :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s \<and> rb_can_enq_c_fun rb = return (0)  \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. ring_C (heap_rb_C s rb) = ring_C (heap_rb_C s0 rb)  \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
   apply(wp_once)+
   apply(smt hoare_assume_preNF validNF_chain validNF_return)
   done


lemma c_rb_enq_preserves_ring2 :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> ring_C (heap_rb_C s rb) = k \<and> rb_can_enq_c_fun rb = return (0) \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. ring_C (heap_rb_C s rb) = k  \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
   apply(wp_once)+
   apply(smt hoare_assume_preNF validNF_chain validNF_return)
   done

text \<open>
  Also, the ring contents are not changed, if we're full
\<close>

lemma c_rb_enq_full_preserves_ring_contents :
  fixes rb :: "rb_C ptr"
  shows
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s \<and> rb_can_enq_c_fun rb = return (0) \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. heap_buffer_C s (ring_C (heap_rb_C s rb)  +\<^sub>p uint i) = 
            heap_buffer_C s0 (ring_C (heap_rb_C s0 rb) +\<^sub>p uint i)  \<rbrace>!"
  apply(simp add:rb_enq_c_fun_def)
  apply(wp_once)+
  by(smt hoare_assume_preNF validNF_chain validNF_return)


text \<open>
  In fact, if the ring buffer is full, then the state is not altered at all.
\<close>

lemma c_rb_enq_full_preserves_state:
  fixes rb :: "rb_C ptr" and b :: buffer_C
  shows "
   \<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s \<and> rb_can_enq_c_fun rb =  return (0)  \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. r \<noteq> 0 \<and> s = s0 \<rbrace>!"
   apply(simp add:rb_enq_c_fun_def)
  apply(wp_once)+
  apply(simp)
  apply (smt hoare_assume_preNF validNF_chain validNF_return)
  done


text \<open>
  We can show that the enqueue function preserves the valid predicate.
\<close>

lemma c_rb_enq_remains_valid:
  fixes rb :: "rb_C ptr" and b :: buffer_C
  shows "
   \<lbrace> \<lambda>s. c_rb_valid s rb  \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s.  c_rb_valid s rb \<rbrace>!"
  apply(simp add:rb_enq_c_fun_def)
  apply(wp_once)+
  apply(simp add:rb_can_enq_c_fun_def)
  apply(wp_once)+
  apply(simp add:c_rb_valid_def )
  by (meson INT_MIN_MAX_lemmas(12) less_eq_Suc_le less_trans not_less unat_1_0 
            unat_32word_leq_lt_lt word_le_less_eq word_less_1 word_less_def 
            word_mod_less_divisor)

  
text \<open>
  Lastly, we can show that the C implementation of the enqueue operation produces the 
  same outcome as doing the abstraction operation.
\<close>

lemma c_rb_enq_state_update_head:
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s  \<and> rb0 = rb_C_to_CleanQ_RB s rb   \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. (r = ERR_OK \<or> r = ERR_QUEUE_FULL) \<and> 
         (if r = ERR_OK then head (rb_C_to_CleanQ_RB s rb) = head (rb_enq b rb0)
         else s = s0) \<rbrace>!"
  unfolding rb_enq_c_fun_def  rb_C_to_CleanQ_RB_def rb_enq_equiv rb_enq_alt_def
  apply(wp_once)+
  apply(simp add:rb_can_enq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:c_rb_valid_def unat_32word_succ_mod Suc_leI unat_32word_leq_lt_lt 
                  word_less_nat_alt)
  using word_le_def word_le_less_eq word_less_nat_alt by blast

lemma c_rb_enq_state_update_tail:
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s  \<and> rb0 = rb_C_to_CleanQ_RB s rb   \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s.  (r = ERR_OK \<or> r = ERR_QUEUE_FULL) \<and> 
       tail (rb_C_to_CleanQ_RB s rb) = tail (rb_enq b rb0)  \<rbrace>!"
  unfolding rb_enq_c_fun_def rb_C_to_CleanQ_RB_def
  apply(wp_once)+
  apply(auto simp:rb_can_enq_c_fun_def)
  apply(wp_once)+
  apply(auto simp: rb_enq_alt_def rb_enq_equiv c_rb_valid_def word_less_nat_alt Suc_leI 
                   unat_32word_leq_lt_lt)
  by (meson le_eq_less_or_eq un_ui_le)

lemma c_rb_enq_state_update_size:
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s  \<and> rb0 = rb_C_to_CleanQ_RB s rb   \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s.  (r = ERR_OK \<or> r = ERR_QUEUE_FULL) \<and> 
       size (rb_C_to_CleanQ_RB s rb) = size (rb_enq b rb0)  \<rbrace>!"
  unfolding rb_enq_c_fun_def rb_C_to_CleanQ_RB_def
  apply(wp_once)+
  apply(auto simp:rb_can_enq_c_fun_def)
  apply(wp_once)+
  apply(auto simp: rb_enq_alt_def rb_enq_equiv c_rb_valid_def word_less_nat_alt Suc_leI 
                   unat_32word_leq_lt_lt)
  by (meson le_eq_less_or_eq un_ui_le)
  


lemma c_ring_ptr_different:
assumes neq: "x \<noteq> unat (head_C (heap_rb_C s0 rb)) \<and> x < unat (size_C (heap_rb_C s0 rb))" 
    and valid: "c_rb_valid s0 rb"
  shows "ring_C (heap_rb_C s0 rb) +\<^sub>p int x \<noteq> ring_C (heap_rb_C s0 rb) +\<^sub>p uint (head_C (heap_rb_C s0 rb))"
proof-
  have sizelimit:
    "(size_C (heap_rb_C s0 rb)) \<le> 0xffffffff"
    by (metis word_and_le1 word_and_max_simps(3))

  have unatsizelimit:
    "unat (size_C (heap_rb_C s0 rb)) \<le> 0xffffffff"
    using sizelimit UINT_MAX_def by auto

  have head_leq_size:
     "unat (head_C (heap_rb_C s0 rb)) < unat (size_C (heap_rb_C s0 rb))"
    using valid unfolding c_rb_valid_def
    using unat_word_lt by blast

  from head_leq_size unatsizelimit have headlim:
     "unat (head_C (heap_rb_C s0 rb)) \<le> 0xffffffff"
    by linarith

  have clim:
    "\<And>(c::64 word). c \<le> 0x40 \<Longrightarrow> unat c \<le> 0x40"
    using unat_word_leq by fastforce

  have xlim:
    "x \<le> 0xffffffff"
    using neq unatsizelimit by linarith

  have inrangex: 
    "\<And>(c::64 word). (c::64 word)\<le> 0x40 \<Longrightarrow> x * unat(c::64 word) \<le> unat addrlimit"
    using xlim clim mult_le_mono  by fastforce  

  have inrangey: 
    "\<And>(c::64 word). c \<le> 0x40 \<Longrightarrow> unat (head_C (heap_rb_C s0 rb)) * unat (c) \<le> unat addrlimit"
     using headlim clim unat_word_leq  mult_le_mono 
     by fastforce
     
  have ineq:
    "\<And>c. 0 < c \<Longrightarrow>  c \<le> 0x40 \<Longrightarrow> of_nat x * (c::ulong_t) \<noteq> of_int (uint (head_C (heap_rb_C s0 rb))) * (c::ulong_t)"
    proof -
      have f1: "\<forall>w n. of_int (int n) * (w::64 word) = of_int (int (n * unat w))"
        by simp
      have "\<And>c. 0 < c \<Longrightarrow> unat (head_C (heap_rb_C s0 rb)) * unat (c::64 word) \<noteq> x * unat (c::64 word)"
      using neq clim headlim unat_word_lt by fastforce 
    then have "\<And>c.  0 < c \<Longrightarrow> c \<le> 0x40 \<Longrightarrow> (of_int (int x)::64 word) * c \<noteq> of_int (int (unat (head_C (heap_rb_C s0 rb)))) * c"
    using f1 by (metis (no_types) inrangex inrangey le_unat_uoi of_int_of_nat_eq)
    then show "\<And>c. 0 < c \<Longrightarrow> c \<le> 0x40 \<Longrightarrow> of_nat x * (c::ulong_t) \<noteq> of_int (uint (head_C (heap_rb_C s0 rb))) * (c::ulong_t)"
    by (simp add: int_unat)
    qed

  thus ?thesis unfolding ptr_add_def
    by(auto)
qed

lemma c_rb_enq_state_update_ring_other:
assumes neq: "x \<noteq> unat (head_C (heap_rb_C s0 rb)) \<and> x < unat (size_C (heap_rb_C s0 rb))"
    and valid: "c_rb_valid s0 rb"
    and supd: "s = heap_buffer_C_update 
                          (\<lambda>a. a(ring_C (heap_rb_C s0 rb) 
                                +\<^sub>p uint (head_C (heap_rb_C s0 rb)) := b)) s0"
  shows "heap_buffer_C s (ring_C (heap_rb_C s rb) +\<^sub>p int x)
        = heap_buffer_C s0 (ring_C (heap_rb_C s0 rb) +\<^sub>p int x)"
  apply(subst supd)+ 
  using neq valid unfolding c_rb_valid_def apply(simp)
  using valid unfolding c_rb_valid_def 
  by (simp add: CleanQ_SimpleQ.c_ring_ptr_different valid)


lemma c_rb_enq_state_update_ring_head:
  assumes eq: "x = unat (head_C (heap_rb_C s0 rb))"
     and supd: "s = heap_buffer_C_update 
                        (\<lambda>a. a(ring_C (heap_rb_C s0 rb)
                               +\<^sub>p uint (head_C (heap_rb_C s0 rb)) := b)) s0"
  shows "heap_buffer_C s (ring_C (heap_rb_C s rb) +\<^sub>p int x) = b"
  using eq  by (simp add: int_unat supd)

lemma c_rb_enq_state_ring_lifted_head:
  assumes eq:  "x = unat (head_C (heap_rb_C s rb))"
    shows  "ring (rb_enq b (rb_C_to_CleanQ_RB s rb)) x = Some b"
  unfolding rb_C_to_CleanQ_RB_def rb_enq_alt_def rb_enq_equiv
  using eq by(auto)

lemma c_rb_enq_state_ring_lifted_other:
  assumes eq:  "x \<noteq> unat (head_C (heap_rb_C s rb))"
    shows  "ring (rb_enq b (rb_C_to_CleanQ_RB s rb)) x = ring (rb_C_to_CleanQ_RB s rb) x"
  unfolding rb_C_to_CleanQ_RB_def rb_enq_alt_def rb_enq_equiv
  using eq by(auto)

lemma c_rb_enq_state_ring_head:
  assumes eq:  "x = unat (head_C (heap_rb_C s0 rb))" 
     and supd: "s = heap_buffer_C_update 
                        (\<lambda>a. a(ring_C (heap_rb_C s0 rb)
                                         +\<^sub>p uint (head_C (heap_rb_C s0 rb)) := b)) s0"
     and hupd: "s1 = heap_rb_C_update
                        (\<lambda>a. a(rb := head_C_update (\<lambda>a. 
                              (a + (1)) mod size_C (heap_rb_C s0 rb)) (a rb))) s"
     and valid: "c_rb_valid s0 rb"
   shows "ring (rb_C_to_CleanQ_RB s1 rb) x = Some b"
   apply(auto simp:rb_C_to_CleanQ_RB_def)
  unfolding rb_C_to_CleanQ_RB_def using eq valid  
   apply(auto simp:supd hupd int_unat c_rb_valid_def)
  using unat_word_lt by blast
  

lemma c_rb_enq_state_update_ring:
  fixes rb :: "rb_C ptr" and b :: buffer_C
  assumes notfull: " rb_can_enq_c_fun rb = return (1) "
  shows "
   \<lbrace> \<lambda>s. rb_can_enq_c_fun rb = return (1) \<and> (c_rb_valid s rb \<and> s0 = s 
                \<and> rb0 = rb_C_to_CleanQ_RB s rb)   \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s. \<forall>i < size rb0. ring (rb_C_to_CleanQ_RB s rb) i = ring (rb_enq b rb0) i \<rbrace>!"
  unfolding rb_enq_c_fun_def  rb_C_to_CleanQ_RB_def rb_enq_equiv rb_enq_alt_def
  apply(wp_once)+
  apply(subst notfull)+
  apply(wp_once)+
  apply(auto simp:fun_upd_def)
       prefer 6 using c_rb_valid_def apply blast
      prefer 5 using c_rb_valid_def less_imp_le word_le_def apply blast
     prefer 4 using c_rb_valid_def unat_gt_0 apply fastforce 
    prefer 3 apply (simp add: int_unat)
   prefer 2 apply (simp add: int_unat)
  using CleanQ_SimpleQ.c_ring_ptr_different by blast


lemma c_rb_enq_state_update_ring2:
  "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s  \<and> rb0 = rb_C_to_CleanQ_RB s rb   \<rbrace>
   rb_enq_c_fun rb b
   \<lbrace> \<lambda> r s.  (r = ERR_OK \<or> r = ERR_QUEUE_FULL) \<and> 
         (if r = ERR_OK then (\<forall>i < size rb0. ring (rb_C_to_CleanQ_RB s rb) i = ring (rb_enq b rb0) i) 
         else s = s0) \<rbrace>!"
  unfolding rb_enq_c_fun_def  rb_C_to_CleanQ_RB_def rb_enq_equiv rb_enq_alt_def
  apply(wp_once)+
  apply(simp add:rb_can_enq_c_fun_def)
  apply(wp_once)+
  apply(auto simp:fun_upd_def)
  using CleanQ_SimpleQ.c_ring_ptr_different apply blast
  unfolding c_rb_valid_def
  apply (simp_all add: int_unat)
  using unat_gt_0 apply fastforce
  using less_imp_le word_le_def apply blast
  using INT_MIN_MAX_lemmas(12) Suc_leI  unat_32word_leq_lt_lt apply blast
  using unat_gt_0 by fastforce     
  
   lemma enq_bufferhelper :
  "   heap_buffer_C
                (heap_rb_C_update
                  (\<lambda>a::rb_C ptr \<Rightarrow> rb_C. a
                      (rb :=
                         head_C_update
                          (\<lambda>a::32 word.
                              (head_C (heap_rb_C (heap_buffer_C_update (\<lambda>a::buffer_C ptr \<Rightarrow> buffer_C. a(ring_C (heap_rb_C s0 rb) +\<^sub>p uint (head_C (heap_rb_C s0 rb)) := b)) s0) rb) + (1::32 word)) mod
                              size_C (heap_rb_C (heap_buffer_C_update (\<lambda>a::buffer_C ptr \<Rightarrow> buffer_C. a(ring_C (heap_rb_C s0 rb) +\<^sub>p uint (head_C (heap_rb_C s0 rb)) := b)) s0) rb))
                          (a rb)))
                  (heap_buffer_C_update (\<lambda>a::buffer_C ptr \<Rightarrow> buffer_C. a(ring_C (heap_rb_C s0 rb) +\<^sub>p uint (head_C (heap_rb_C s0 rb)) := b)) s0)) = 


   heap_buffer_C
                
                  (heap_buffer_C_update (\<lambda>a::buffer_C ptr \<Rightarrow> buffer_C. a(ring_C (heap_rb_C s0 rb) +\<^sub>p uint (head_C (heap_rb_C s0 rb)) := b)) s0)"

     by(auto)

lemma enq_ringhelper:
"
 
                (ring_C
                  (heap_rb_C
                    (heap_rb_C_update
                      (\<lambda>a::rb_C ptr \<Rightarrow> rb_C. a
                          (rb :=
                             head_C_update
                              (\<lambda>a::32 word.
                                  (head_C (heap_rb_C (heap_buffer_C_update (\<lambda>a::buffer_C ptr \<Rightarrow> buffer_C. a(ring_C (heap_rb_C s0 rb) +\<^sub>p uint (head_C (heap_rb_C s0 rb)) := b)) s0) rb) + (1::32 word)) mod
                                  size_C (heap_rb_C (heap_buffer_C_update (\<lambda>a::buffer_C ptr \<Rightarrow> buffer_C. a(ring_C (heap_rb_C s0 rb) +\<^sub>p uint (head_C (heap_rb_C s0 rb)) := b)) s0) rb))
                              (a rb)))
                      (heap_buffer_C_update (\<lambda>a::buffer_C ptr \<Rightarrow> buffer_C. a(ring_C (heap_rb_C s0 rb) +\<^sub>p uint (head_C (heap_rb_C s0 rb)) := b)) s0))
                    rb) +\<^sub>p
                 int i)

 = 
                (ring_C
                  (heap_rb_C s0 rb) +\<^sub>p                int i)

"

  by(auto)

lemma 
 ring_upd_helper:
 "(heap_buffer_C (heap_buffer_C_update (\<lambda>a::buffer_C ptr \<Rightarrow> buffer_C. a(ring_C (heap_rb_C s0 rb) +\<^sub>p uint (head_C (heap_rb_C s0 rb)) := b)) s0) (ring_C (heap_rb_C s0 rb) +\<^sub>p int i))
  = (if i = unat (head_C (heap_rb_C s0 rb)) then b else (heap_buffer_C (heap_buffer_C_update (\<lambda>a::buffer_C ptr \<Rightarrow> buffer_C. a(ring_C (heap_rb_C s0 rb) +\<^sub>p uint (head_C (heap_rb_C s0 rb)) := b)) s0) (ring_C (heap_rb_C s0 rb) +\<^sub>p int i)))"
  apply(simp add: int_unat)

  done

lemmas unat_of_nat32' = unat_of_nat_eq[where 'a=32]
lemmas unat_of_nat32 = unat_of_nat32'[unfolded word_bits_len_of]

lemma ring_upd_helper2:
  assumes ii:" j \<noteq> unat (head_C (heap_rb_C s0 rb)) \<and>  j <  unat (size_C (heap_rb_C s0 rb)) "
shows  " (heap_buffer_C (heap_buffer_C_update (\<lambda>a::buffer_C ptr \<Rightarrow> buffer_C. a(ring_C (heap_rb_C s0 rb) +\<^sub>p uint (head_C (heap_rb_C s0 rb)) := b)) s0) (ring_C (heap_rb_C s0 rb) +\<^sub>p int j))
 =(heap_buffer_C s0 (ring_C (heap_rb_C s0 rb) +\<^sub>p int j))"
proof -
  from ii have ilimit:
    "j < UINT_MAX"
    using INT_MIN_MAX_lemmas(12) less_le_trans by blast

  have is64: 
    "unat((0x40::64 word)) = 64"
    by(auto)

  have inrangex: "j * unat((0x40::64 word)) < 2 ^ 64"
    using ii ilimit apply(subst is64) by(auto simp:UINT_MAX_def)

  have hlim:
    "unat (of_int (uint (head_C (heap_rb_C s0 rb)))::64 word)  \<le> UINT_MAX"
    by (metis (mono_tags, hide_lams) INT_MIN_MAX_lemmas(12) int_unat le_less le_trans of_int_of_nat_eq unat_le_helper)
  
  have inrangey: "unat (of_int (uint (head_C (heap_rb_C s0 rb)))::64 word) * unat((0x40::64 word)) < 2 ^ 64"
    using hlim apply(subst is64) by(auto simp:UINT_MAX_def)   

    have hlim2:
    "unat (head_C (heap_rb_C s0 rb)) < 2 ^ 32"
      using unat_lt2p 
      by (metis len32)

  have "unat (head_C (heap_rb_C s0 rb)) = unat ((of_int (uint (head_C (heap_rb_C s0 rb)))::64 word))"
    using hlim2 apply(subst of_int_uint_ucast)
    by(simp add:unat_ucast)
    

  have newq: "j \<noteq> unat ((of_int (uint (head_C (heap_rb_C s0 rb)))::64 word))"
    using ii hlim2
    apply(subst of_int_uint_ucast)
    by(simp add:unat_ucast)


  have  "x < 2^ 32 \<Longrightarrow> unat ((of_nat x)::64 word) = x"
    by (simp add: unat_of_nat64 word_bits_conv)

  have  "x < 2^ 32 \<Longrightarrow> unat ((of_nat x)::32 word) = x"
    by (simp add: unat_of_nat32 word_bits_conv)
 
  have  "x < 2^ 32 \<Longrightarrow> unat ((of_nat x)::64 word) = unat ((of_nat x)::32 word)"
    by (simp add: unat_of_nat64 unat_of_nat32 word_bits_conv)

  show ?thesis      
  using ii inrangex inrangey newq apply(auto simp add:ptr_add_def)
    by(simp add:word64_mult_inequality2)
    
qed



lemma c_rb_enq_correct:
   "\<lbrace> \<lambda>s. c_rb_valid s rb \<and> s0 = s \<and> rb0 = rb_C_to_CleanQ_RB s rb  \<rbrace>
           rb_enq_c_fun rb b
    \<lbrace> \<lambda>r s.  (r = ERR_OK \<or> r = ERR_QUEUE_FULL) \<and> 
              (if r = ERR_OK then rb_C_to_CleanQ_RB s rb = rb_enq b rb0
               else s = s0) \<rbrace>!"
  unfolding rb_enq_c_fun_def  rb_C_to_CleanQ_RB_def rb_enq_equiv rb_enq_alt_def
  apply(wp_once)+
  apply(simp add:rb_can_enq_c_fun_def)
  apply(wp_once)+
  apply(auto)
  prefer 8 using c_rb_valid_def apply blast
  prefer 7 using c_rb_valid_def unat_gt_0 apply fastforce
  prefer 6 using INT_MIN_MAX_lemmas(12) Suc_leI c_rb_valid_def unat_32word_leq_lt_lt apply blast
  prefer 5 using c_rb_valid_def apply blast 
  prefer 4 using c_rb_valid_def word_le_def word_le_less_eq apply blast
  prefer 3 using c_rb_valid_def unat_gt_0 apply fastforce
  prefer 2 using c_rb_valid_def unat_32word_succ_mod unat_word_lt apply fastforce
  apply(subst enq_bufferhelper)
  apply(subst enq_ringhelper)
  apply(simp add:fun_upd_def)
  apply(subst ring_upd_helper)
  using ring_upd_helper2 c_rb_valid_def unat_word_lt 
  by fastforce

  
(* ####################################################### *)


lemma "rb_enq_c_fun rb b = rb_enq_unfolded_c_fun rb b"
  unfolding  rb_enq_c_fun_def  rb_enq_unfolded_c_fun_def rb_can_enq_c_fun_def
  apply(monad_eq)
  apply(auto simp add: int_unat)
  done




lemma "rb_deq_c_fun rb b = rb_deq_unfolded_c_fun rb b"
  unfolding rb_deq_c_fun_def rb_deq_unfolded_c_fun_def rb_can_deq_c_fun_def
  apply(monad_eq)  (* seems to take a while... *)
  apply(auto simp add: int_unat)
  done


thm rb_enq_unfolded_c_fun_def




lemma "(a::nat) \<le> 64 \<Longrightarrow> (b::nat) < 2^32 \<Longrightarrow> a * b < 2^64"
proof -
  assume p1 :"(a::nat) \<le> 64"
  assume p2: "(b::nat) < 2^32"

  have x1: "(64::nat) * 2^32  \<le> 2^64"
    by(simp)

  have x2: "(a::nat) \<le> 64 \<Longrightarrow> (b::nat) < 2^32 \<Longrightarrow>  a * b < 64 * 2^32" 
    by (meson le_less_trans mult_less_cancel1 mult_right_mono zero_le zero_less_numeral)

  show ?thesis using order_trans x2 x1 p1 p2 
    by linarith
qed
  

lemma "(a::nat) < 2^32 \<Longrightarrow> (b::nat) < 2^32 \<Longrightarrow> a * b < 2^64"
proof -
  assume p1 :"(a::nat) < 2^32"
  assume p2: "(b::nat) < 2^32"
  
  have X1: "(0xffffffff::nat) * 0xffffffff \<le> 0xffffffffffffffff"
    by(auto)

  have X2: "(a::nat) \<le> 0xffffffff \<Longrightarrow> (b::nat) \<le> 0xffffffff \<Longrightarrow> a * b \<le> 0xffffffffffffffff"
    using X1 mult_le_mono order_trans by blast

  have X3: "(a::nat) <  2^32 \<Longrightarrow> (b::nat) < 2^32 \<Longrightarrow>  a * b < (2^32 * 2^32)"
    using X2  by simp

  show ?thesis
    using p1 p2 X3 by auto
qed


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
