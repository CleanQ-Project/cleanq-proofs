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
  CRB  :: "CleanQ_Buffer CleanQ_RB_State"
  buf_x :: "CleanQ_Buffer"
  buf_y :: "CleanQ_Buffer"
  local_x :: "CleanQ_Buffer"
  local_y :: "CleanQ_Buffer"
  uni :: "CleanQ_Buffer set"
(*>*)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Redifining writing/reading a buffer\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
   In reality the writes and reads to a buffer (or the buffer struct) are 
   one per field and concurrent actions can happen during each write. In order
   to model this, we redefine writing and reading a buffer to smaller steps 
\<close>


definition CleanQ_RB_read_tail_region_x :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer"
  where 
    "CleanQ_RB_read_tail_region_x rb b = b \<lparr> region := region (rb_read_tail (rTYX rb)) \<rparr>"

definition CleanQ_RB_read_tail_region_y :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where 
    "CleanQ_RB_read_tail_region_y rb b = b \<lparr> region := region (rb_read_tail (rTXY rb)) \<rparr>"

definition CleanQ_RB_read_tail_offset_x :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where 
    "CleanQ_RB_read_tail_offset_x rb b = b \<lparr> offset := offset (rb_read_tail (rTYX rb)) \<rparr>"

definition CleanQ_RB_read_tail_offset_y :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where 
    "CleanQ_RB_read_tail_offset_y rb b = b \<lparr> offset := offset (rb_read_tail (rTXY rb)) \<rparr>"

definition CleanQ_RB_read_tail_length_x :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where 
   "CleanQ_RB_read_tail_length_x rb b = b \<lparr> length := length (rb_read_tail (rTYX rb)) \<rparr>"

definition CleanQ_RB_read_tail_length_y :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where 
    "CleanQ_RB_read_tail_length_y rb b = b \<lparr> length := length (rb_read_tail (rTXY rb)) \<rparr>"

definition CleanQ_RB_read_tail_valid_offset_x :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where "CleanQ_RB_read_tail_valid_offset_x rb b = 
            b \<lparr> valid_offset := valid_offset (rb_read_tail (rTYX rb)) \<rparr>"

definition CleanQ_RB_read_tail_valid_offset_y :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where "CleanQ_RB_read_tail_valid_offset_y rb b = 
            b \<lparr> valid_offset := valid_offset (rb_read_tail (rTXY rb)) \<rparr>"

definition CleanQ_RB_read_tail_valid_length_x :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where "CleanQ_RB_read_tail_valid_length_x rb b = 
            b \<lparr> valid_length := valid_length (rb_read_tail (rTYX rb)) \<rparr>"

definition CleanQ_RB_read_tail_valid_length_y :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where "CleanQ_RB_read_tail_valid_length_y rb b = 
            b \<lparr> valid_length := valid_length (rb_read_tail (rTXY rb)) \<rparr>"

definition CleanQ_RB_read_tail_flags_x :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where 
   "CleanQ_RB_read_tail_flags_x rb b = b \<lparr> flags := flags (rb_read_tail (rTYX rb)) \<rparr>"

definition CleanQ_RB_read_tail_flags_y :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where 
    "CleanQ_RB_read_tail_flags_y rb b = b \<lparr> flags := flags (rb_read_tail (rTXY rb)) \<rparr>"



definition CleanQ_RB_write_head_region_x :: 
  "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_region_x val rb = 
      rb \<lparr> rTXY := rb_write_head ((rb_read_head (rTXY rb))\<lparr> region := val\<rparr>) (rTXY rb) \<rparr>"

definition CleanQ_RB_write_head_region_y :: 
  "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_region_y val rb = 
      rb \<lparr> rTYX := rb_write_head ((rb_read_head (rTYX rb))\<lparr>region := val\<rparr>) (rTYX rb) \<rparr>"

definition CleanQ_RB_write_head_offset_x :: 
  "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_offset_x val rb = 
      rb \<lparr> rTXY := rb_write_head ((rb_read_head (rTXY rb))\<lparr>offset := val\<rparr>) (rTXY rb) \<rparr>"

definition CleanQ_RB_write_head_offset_y :: 
  "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_offset_y val rb = 
      rb \<lparr> rTYX := rb_write_head ((rb_read_head (rTYX rb))\<lparr>offset := val\<rparr>) (rTYX rb) \<rparr>"

definition CleanQ_RB_write_head_length_x :: 
  "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_length_x val rb = 
      rb \<lparr> rTXY := rb_write_head ((rb_read_head (rTXY rb))\<lparr>length := val\<rparr>) (rTXY rb) \<rparr>"

definition CleanQ_RB_write_head_length_y :: 
  "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_length_y val rb = 
      rb \<lparr> rTYX := rb_write_head ((rb_read_head (rTYX rb))\<lparr>length := val\<rparr>) (rTYX rb) \<rparr>"

definition CleanQ_RB_write_head_valid_offset_x :: 
  "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_valid_offset_x val rb = 
      rb \<lparr> rTXY := rb_write_head ((rb_read_head (rTXY rb))\<lparr>valid_offset := val\<rparr>) (rTXY rb) \<rparr>"

definition CleanQ_RB_write_head_valid_offset_y :: 
  "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_valid_offset_y val rb = 
      rb \<lparr> rTYX := rb_write_head ((rb_read_head (rTYX rb))\<lparr>valid_offset := val\<rparr>) (rTYX rb) \<rparr>"

definition CleanQ_RB_write_head_valid_length_x :: 
  "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_valid_length_x val rb = 
      rb \<lparr> rTXY := rb_write_head ((rb_read_head (rTXY rb))\<lparr>valid_length := val\<rparr>) (rTXY rb) \<rparr>"

definition CleanQ_RB_write_head_valid_length_y :: 
  "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_valid_length_y val rb = 
      rb \<lparr> rTYX := rb_write_head ((rb_read_head (rTYX rb))\<lparr>valid_length := val\<rparr>) (rTYX rb) \<rparr>"

definition CleanQ_RB_write_head_flags_x :: 
  "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_flags_x val rb = 
      rb \<lparr> rTXY := rb_write_head ((rb_read_head (rTXY rb))\<lparr>flags := val\<rparr>) (rTXY rb) \<rparr>"

definition CleanQ_RB_write_head_flags_y :: 
  "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_flags_y val rb = 
      rb \<lparr> rTYX := rb_write_head ((rb_read_head (rTYX rb))\<lparr>flags := val\<rparr>) (rTYX rb) \<rparr>"


text \<open>
  Show equality 
\<close>

lemma CleanQ_RB_read_tail_x_fields_eq :
  shows "CleanQ_RB_read_tail_x rb = 
    (CleanQ_RB_read_tail_valid_offset_x rb
    (CleanQ_RB_read_tail_valid_length_x rb
    (CleanQ_RB_read_tail_flags_x rb
    (CleanQ_RB_read_tail_length_x rb 
    (CleanQ_RB_read_tail_offset_x rb
    (CleanQ_RB_read_tail_region_x rb buf))))))"
  unfolding CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_region_x_def
    CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_x_def 
    CleanQ_RB_read_tail_valid_offset_x_def CleanQ_RB_read_tail_valid_length_x_def
    CleanQ_RB_read_tail_flags_x_def
  by simp

lemma CleanQ_RB_read_tail_y_fields_eq :
  shows "CleanQ_RB_read_tail_y rb = 
    (CleanQ_RB_read_tail_valid_offset_y rb
    (CleanQ_RB_read_tail_valid_length_y rb
    (CleanQ_RB_read_tail_flags_y rb
    (CleanQ_RB_read_tail_length_y rb 
    (CleanQ_RB_read_tail_offset_y rb
    (CleanQ_RB_read_tail_region_y rb buf))))))"
  unfolding CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_region_y_def
    CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def 
    CleanQ_RB_read_tail_valid_offset_y_def CleanQ_RB_read_tail_valid_length_y_def
    CleanQ_RB_read_tail_flags_y_def
  by simp


text \<open>
  Other helper lemmas (mostly added to simp set for easier proofs)
\<close>

paragraph \<open>Read Tail Y, write Head X\<close>

lemma CleanQ_RB_read_tail_y_write_head_flags_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_y (CleanQ_RB_write_head_flags_x f rb) = CleanQ_RB_read_tail_y rb "
  by (simp add: CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_read_tail_y_write_head_region_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_y (CleanQ_RB_write_head_region_x f rb) = CleanQ_RB_read_tail_y rb "
  by (simp add: CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_read_tail_y_write_head_offset_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_y (CleanQ_RB_write_head_offset_x f rb) = CleanQ_RB_read_tail_y rb "
  by (simp add: CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_read_tail_y_write_head_length_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_y (CleanQ_RB_write_head_length_x f rb) = CleanQ_RB_read_tail_y rb "
  by (simp add: CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_read_tail_y_write_head_valid_length_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_y (CleanQ_RB_write_head_valid_length_x f rb) = CleanQ_RB_read_tail_y rb "
  by (simp add: CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def CleanQ_RB_write_head_valid_length_x_def)

lemma CleanQ_RB_read_tail_y_write_head_valid_offset_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_y (CleanQ_RB_write_head_valid_offset_x f rb) = CleanQ_RB_read_tail_y rb "
  by (simp add: CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def CleanQ_RB_write_head_valid_offset_x_def)

lemmas CleanQ_RB_read_tail_y_write_head[simp] = 
     CleanQ_RB_read_tail_y_write_head_flags_x
     CleanQ_RB_read_tail_y_write_head_region_x
     CleanQ_RB_read_tail_y_write_head_offset_x
     CleanQ_RB_read_tail_y_write_head_length_x
     CleanQ_RB_read_tail_y_write_head_valid_length_x
     CleanQ_RB_read_tail_y_write_head_valid_offset_x

paragraph \<open>Read Tail x, write Head y\<close>

lemma CleanQ_RB_read_tail_x_write_head_flags_x:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_x (CleanQ_RB_write_head_flags_y f rb) = CleanQ_RB_read_tail_x rb "
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_read_tail_x_write_head_region_x:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_x (CleanQ_RB_write_head_region_y f rb) = CleanQ_RB_read_tail_x rb "
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_read_tail_x_write_head_offset_x:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_x (CleanQ_RB_write_head_offset_y f rb) = CleanQ_RB_read_tail_x rb "
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_read_tail_x_write_head_length_x:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_x (CleanQ_RB_write_head_length_y f rb) = CleanQ_RB_read_tail_x rb "
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_read_tail_x_write_head_valid_length_x:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_x (CleanQ_RB_write_head_valid_length_y f rb) = CleanQ_RB_read_tail_x rb "
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_x_def CleanQ_RB_write_head_valid_length_y_def)

lemma CleanQ_RB_read_tail_x_write_head_valid_offset_x:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_x (CleanQ_RB_write_head_valid_offset_y f rb) = CleanQ_RB_read_tail_x rb "
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemmas CleanQ_RB_read_tail_x_write_head[simp] = 
     CleanQ_RB_read_tail_x_write_head_flags_x
     CleanQ_RB_read_tail_x_write_head_region_x
     CleanQ_RB_read_tail_x_write_head_offset_x
     CleanQ_RB_read_tail_x_write_head_length_x
     CleanQ_RB_read_tail_x_write_head_valid_length_x
     CleanQ_RB_read_tail_x_write_head_valid_offset_x

paragraph \<open>Write X read Y Unchanged \<close>

lemma CleanQ_RB_read_head_x_write_length_y:
  "CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_y v rb) = CleanQ_RB_read_head_x rb"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_read_head_x_write_offset_y:
  "CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_y v rb) = CleanQ_RB_read_head_x rb"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_read_head_x_write_region_y:
  "CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_y v rb) = CleanQ_RB_read_head_x rb"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_read_head_x_write_flags_y:
  "CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_y v rb) = CleanQ_RB_read_head_x rb"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_read_head_x_write_valid_length_y:
  "CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_y v rb) = CleanQ_RB_read_head_x rb"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_y_def)

lemma CleanQ_RB_read_head_x_write_valid_offset_y:
  "CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_y v rb) = CleanQ_RB_read_head_x rb"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemmas CleanQ_RB_read_head_x_write_y[simp] = 
   CleanQ_RB_read_head_x_write_length_y
   CleanQ_RB_read_head_x_write_offset_y
   CleanQ_RB_read_head_x_write_region_y
   CleanQ_RB_read_head_x_write_flags_y
   CleanQ_RB_read_head_x_write_valid_length_y
   CleanQ_RB_read_head_x_write_valid_offset_y

paragraph \<open>Write Y read X Unchanged \<close>

lemma CleanQ_RB_read_head_y_write_length_x:
  "CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_x v rb) = CleanQ_RB_read_head_y rb"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_read_head_y_write_offset_x:
  "CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_x v rb) = CleanQ_RB_read_head_y rb"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_read_head_y_write_region_x:
  "CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_x v rb) = CleanQ_RB_read_head_y rb"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_read_head_y_write_flags_x:
  "CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_x v rb) = CleanQ_RB_read_head_y rb"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_read_head_y_write_valid_length_x:
  "CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_x v rb) = CleanQ_RB_read_head_y rb"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_x_def)

lemma CleanQ_RB_read_head_y_write_valid_offset_x:
  "CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_x v rb) = CleanQ_RB_read_head_y rb"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_x_def)

lemmas CleanQ_RB_read_head_y_write_x[simp] = 
   CleanQ_RB_read_head_y_write_length_x
   CleanQ_RB_read_head_y_write_offset_x
   CleanQ_RB_read_head_y_write_region_x
   CleanQ_RB_read_head_y_write_flags_x
   CleanQ_RB_read_head_y_write_valid_length_x
   CleanQ_RB_read_head_y_write_valid_offset_x





paragraph \<open>Length Unchangend when X writes and X reads \<close>

lemma CleanQ_RB_write_head_offset_x_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_x x rb)) = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_region_x_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_x x rb)) = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_flags_x_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_x x rb)) = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_x x rb)) = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_x x rb)) = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_x_def)

lemmas CleanQ_RB_write_head_x_read_x_length_unchanged_simps[simp] = 
    CleanQ_RB_write_head_offset_x_read_x_length_unchanged
    CleanQ_RB_write_head_region_x_read_x_length_unchanged
    CleanQ_RB_write_head_flags_x_read_x_length_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_x_length_unchanged
    CleanQ_RB_write_head_valid_length_x_read_x_length_unchanged


paragraph \<open>Length Unchangend when X writes and Y reads \<close>


lemma CleanQ_RB_write_head_offset_x_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_x x rb)) = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_region_x_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_x x rb)) = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_flags_x_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_x x rb)) = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_x x rb)) = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_x x rb)) = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_x_def)

lemmas CleanQ_RB_write_head_x_read_y_length_unchanged_simps[simp] = 
    CleanQ_RB_write_head_offset_x_read_y_length_unchanged
    CleanQ_RB_write_head_region_x_read_y_length_unchanged
    CleanQ_RB_write_head_flags_x_read_y_length_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_y_length_unchanged
    CleanQ_RB_write_head_valid_length_x_read_y_length_unchanged


paragraph \<open>Length Unchangend when Y writes and Y reads \<close>

lemma CleanQ_RB_write_head_offset_y_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_y x rb)) = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_region_y_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_y x rb)) = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_flags_y_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_y x rb)) = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_y x rb)) = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_y x rb)) = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_y_length_unchanged_simps[simp] = 
    CleanQ_RB_write_head_offset_y_read_y_length_unchanged
    CleanQ_RB_write_head_region_y_read_y_length_unchanged
    CleanQ_RB_write_head_flags_y_read_y_length_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_y_length_unchanged
    CleanQ_RB_write_head_valid_length_y_read_y_length_unchanged


paragraph \<open>Length Unchangend when Y writes and Y reads \<close>

lemma CleanQ_RB_write_head_offset_y_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_y x rb)) = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_region_y_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_y x rb)) = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_flags_y_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_y x rb)) = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_y x rb)) = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_y x rb)) = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_x_length_unchanged_simps[simp] = 
    CleanQ_RB_write_head_offset_y_read_x_length_unchanged
    CleanQ_RB_write_head_region_y_read_x_length_unchanged
    CleanQ_RB_write_head_flags_y_read_x_length_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_x_length_unchanged
    CleanQ_RB_write_head_valid_length_y_read_x_length_unchanged




paragraph \<open>Offset Unchanged when X writes and X reads\<close>

lemma CleanQ_RB_write_head_length_x_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_x x rb)) = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_region_x_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_x x rb)) = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_flags_x_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_x x rb)) = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_x x rb)) = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_x x rb)) = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_x_def)
 

lemmas CleanQ_RB_write_head_x_read_x_offset_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_x_offset_unchanged
    CleanQ_RB_write_head_region_x_read_x_offset_unchanged
    CleanQ_RB_write_head_flags_x_read_x_offset_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_x_offset_unchanged
    CleanQ_RB_write_head_valid_length_x_read_x_offset_unchanged


paragraph \<open>Offset Unchanged when X writes and Y reads\<close>

lemma CleanQ_RB_write_head_length_x_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_x x rb)) = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_region_x_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_x x rb)) = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_flags_x_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_x x rb)) = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_x x rb)) = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_x x rb)) = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_x_def)

lemmas CleanQ_RB_write_head_x_read_y_offset_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_y_offset_unchanged
    CleanQ_RB_write_head_region_x_read_y_offset_unchanged
    CleanQ_RB_write_head_flags_x_read_y_offset_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_y_offset_unchanged
    CleanQ_RB_write_head_valid_length_x_read_y_offset_unchanged


paragraph \<open>Offset Unchanged when Y writes and Y reads\<close>

lemma CleanQ_RB_write_head_length_y_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_y x rb)) = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_region_y_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_y x rb)) = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_flags_y_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_y x rb)) = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_y x rb)) = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_y x rb)) = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_y_offset_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_y_offset_unchanged
    CleanQ_RB_write_head_region_y_read_y_offset_unchanged
    CleanQ_RB_write_head_flags_y_read_y_offset_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_y_offset_unchanged
    CleanQ_RB_write_head_valid_length_y_read_y_offset_unchanged


paragraph \<open>Offset Unchanged when Y writes and X reads\<close>

lemma CleanQ_RB_write_head_length_y_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_y x rb)) = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_region_y_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_y x rb)) = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_flags_y_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_y x rb)) = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_y x rb)) = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_y x rb)) = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_x_offset_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_x_offset_unchanged
    CleanQ_RB_write_head_region_y_read_x_offset_unchanged
    CleanQ_RB_write_head_flags_y_read_x_offset_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_x_offset_unchanged
    CleanQ_RB_write_head_valid_length_y_read_x_offset_unchanged


paragraph \<open>Flags Unchanged when X writes and X reads\<close>

lemma CleanQ_RB_write_head_length_x_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_x x rb)) = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_region_x_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_x x rb)) = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_offset_x_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_x x rb)) = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_x x rb)) = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_x x rb)) = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_x_def)
  

lemmas CleanQ_RB_write_head_x_read_x_flags_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_x_flags_unchanged
    CleanQ_RB_write_head_region_x_read_x_flags_unchanged
    CleanQ_RB_write_head_offset_x_read_x_flags_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_x_flags_unchanged
    CleanQ_RB_write_head_valid_length_x_read_x_flags_unchanged

paragraph \<open>Flags Unchanged when X writes and Y reads\<close>

lemma CleanQ_RB_write_head_length_x_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_x x rb)) = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_region_x_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_x x rb)) = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_offset_x_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_x x rb)) = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_x x rb)) = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_x x rb)) = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_x_def)

lemmas CleanQ_RB_write_head_x_read_y_flags_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_y_flags_unchanged
    CleanQ_RB_write_head_region_x_read_y_flags_unchanged
    CleanQ_RB_write_head_offset_x_read_y_flags_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_y_flags_unchanged
    CleanQ_RB_write_head_valid_length_x_read_y_flags_unchanged


paragraph \<open>Flags Unchanged when Y writes and Y reads\<close>

lemma CleanQ_RB_write_head_length_y_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_y x rb)) = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_region_y_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_y x rb)) = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_offset_y_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_y x rb)) = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_y x rb)) = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_y x rb)) = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_y_flags_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_y_flags_unchanged
    CleanQ_RB_write_head_region_y_read_y_flags_unchanged
    CleanQ_RB_write_head_offset_y_read_y_flags_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_y_flags_unchanged
    CleanQ_RB_write_head_valid_length_y_read_y_flags_unchanged

paragraph \<open>Flags Unchanged when Y writes and X reads\<close>

lemma CleanQ_RB_write_head_length_y_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_y x rb)) = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_region_y_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_y x rb)) = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_offset_y_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_y x rb)) = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_y x rb)) = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_y x rb)) = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_x_flags_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_x_flags_unchanged
    CleanQ_RB_write_head_region_y_read_x_flags_unchanged
    CleanQ_RB_write_head_offset_y_read_x_flags_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_x_flags_unchanged
    CleanQ_RB_write_head_valid_length_y_read_x_flags_unchanged


paragraph \<open>Region Unchanged when X writes and X reads\<close>

lemma CleanQ_RB_write_head_length_x_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_x x rb)) = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_flags_x_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_x x rb)) = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_offset_x_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_x x rb)) = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_x x rb)) = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_x x rb)) = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_x_def)
  

lemmas CleanQ_RB_write_head_x_read_x_region_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_x_region_unchanged
    CleanQ_RB_write_head_flags_x_read_x_region_unchanged
    CleanQ_RB_write_head_offset_x_read_x_region_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_x_region_unchanged
    CleanQ_RB_write_head_valid_length_x_read_x_region_unchanged


paragraph \<open>Region Unchanged when X writes and Y reads\<close>

lemma CleanQ_RB_write_head_length_x_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_x x rb)) = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_flags_x_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_x x rb)) = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_offset_x_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_x x rb)) = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_x x rb)) = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_x x rb)) = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_x_def)

lemmas CleanQ_RB_write_head_x_read_y_region_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_y_region_unchanged
    CleanQ_RB_write_head_flags_x_read_y_region_unchanged
    CleanQ_RB_write_head_offset_x_read_y_region_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_y_region_unchanged
    CleanQ_RB_write_head_valid_length_x_read_y_region_unchanged

paragraph \<open>Region Unchanged when Y writes and Y reads\<close>

lemma CleanQ_RB_write_head_length_y_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_y x rb)) = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_flags_y_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_y x rb)) = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_offset_y_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_y x rb)) = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_y x rb)) = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_y x rb)) = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_y_region_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_y_region_unchanged
    CleanQ_RB_write_head_flags_y_read_y_region_unchanged
    CleanQ_RB_write_head_offset_y_read_y_region_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_y_region_unchanged
    CleanQ_RB_write_head_valid_length_y_read_y_region_unchanged

paragraph \<open>Region Unchanged when Y writes and Y reads\<close>

lemma CleanQ_RB_write_head_length_y_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_y x rb)) = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_flags_y_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_y x rb)) = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_offset_y_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_y x rb)) = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_y x rb)) = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_y x rb)) = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_x_region_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_x_region_unchanged
    CleanQ_RB_write_head_flags_y_read_x_region_unchanged
    CleanQ_RB_write_head_offset_y_read_x_region_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_x_region_unchanged
    CleanQ_RB_write_head_valid_length_y_read_x_region_unchanged



paragraph \<open>Valid Offset Unchanged when X writes and X reads\<close>

lemma CleanQ_RB_write_head_length_x_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_x x rb)) = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_flags_x_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_x x rb)) = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_offset_x_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_x x rb)) = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_region_x_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_x x rb)) = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_x x rb)) = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_x_def)
 

lemmas CleanQ_RB_write_head_x_read_x_valid_offset_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_x_valid_offset_unchanged
    CleanQ_RB_write_head_flags_x_read_x_valid_offset_unchanged
    CleanQ_RB_write_head_offset_x_read_x_valid_offset_unchanged
    CleanQ_RB_write_head_region_x_read_x_valid_offset_unchanged
    CleanQ_RB_write_head_valid_length_x_read_x_valid_offset_unchanged



paragraph \<open>Valid Offset Unchanged when X writes and Y reads\<close>

lemma CleanQ_RB_write_head_length_x_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_x x rb)) = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_flags_x_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_x x rb)) = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_offset_x_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_x x rb)) = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_region_x_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_x x rb)) = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_x x rb)) = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_x_def)

lemmas CleanQ_RB_write_head_x_read_y_valid_offset_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_y_valid_offset_unchanged
    CleanQ_RB_write_head_flags_x_read_y_valid_offset_unchanged
    CleanQ_RB_write_head_offset_x_read_y_valid_offset_unchanged
    CleanQ_RB_write_head_region_x_read_y_valid_offset_unchanged
    CleanQ_RB_write_head_valid_length_x_read_y_valid_offset_unchanged


paragraph \<open>Valid Offset Unchanged when Y writes and Y reads\<close>

lemma CleanQ_RB_write_head_length_y_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_y x rb)) = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_flags_y_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_y x rb)) = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_offset_y_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_y x rb)) = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_region_y_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_y x rb)) = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_y x rb)) = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_y_valid_offset_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_y_valid_offset_unchanged
    CleanQ_RB_write_head_flags_y_read_y_valid_offset_unchanged
    CleanQ_RB_write_head_offset_y_read_y_valid_offset_unchanged
    CleanQ_RB_write_head_region_y_read_y_valid_offset_unchanged
    CleanQ_RB_write_head_valid_length_y_read_y_valid_offset_unchanged


paragraph \<open>Valid Offset Unchanged when Y writes and X reads\<close>

lemma CleanQ_RB_write_head_length_y_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_y x rb)) = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_flags_y_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_y x rb)) = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_offset_y_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_y x rb)) = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_region_y_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_y x rb)) = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_y x rb)) = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_x_valid_offset_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_x_valid_offset_unchanged
    CleanQ_RB_write_head_flags_y_read_x_valid_offset_unchanged
    CleanQ_RB_write_head_offset_y_read_x_valid_offset_unchanged
    CleanQ_RB_write_head_region_y_read_x_valid_offset_unchanged
    CleanQ_RB_write_head_valid_length_y_read_x_valid_offset_unchanged


paragraph \<open>Valid Offset Unchanged when X writes and X reads\<close>

lemma CleanQ_RB_write_head_length_x_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_x x rb)) = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_flags_x_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_x x rb)) = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_offset_x_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_x x rb)) = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_region_x_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_x x rb)) = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_x x rb)) = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_x_def)

lemmas CleanQ_RB_write_head_x_read_x_valid_length_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_x_valid_length_unchanged
    CleanQ_RB_write_head_flags_x_read_x_valid_length_unchanged
    CleanQ_RB_write_head_offset_x_read_x_valid_length_unchanged
    CleanQ_RB_write_head_region_x_read_x_valid_length_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_x_valid_length_unchanged



paragraph \<open>Valid Offset Unchanged when X writes and Y reads\<close>

lemma CleanQ_RB_write_head_length_x_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_x x rb)) = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_flags_x_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_x x rb)) = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_offset_x_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_x x rb)) = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_region_x_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_x x rb)) = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_x x rb)) = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_x_def)

lemmas CleanQ_RB_write_head_x_read_y_valid_length_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_y_valid_length_unchanged
    CleanQ_RB_write_head_flags_x_read_y_valid_length_unchanged
    CleanQ_RB_write_head_offset_x_read_y_valid_length_unchanged
    CleanQ_RB_write_head_region_x_read_y_valid_length_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_y_valid_length_unchanged


paragraph \<open>Valid Offset Unchanged when Y writes and Y reads\<close>

lemma CleanQ_RB_write_head_length_y_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_y x rb)) = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_flags_y_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_y x rb)) = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_offset_y_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_y x rb)) = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_region_y_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_y x rb)) = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_y x rb)) = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_y_def)

lemmas CleanQ_RB_write_head_y_read_y_valid_length_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_y_valid_length_unchanged
    CleanQ_RB_write_head_flags_y_read_y_valid_length_unchanged
    CleanQ_RB_write_head_offset_y_read_y_valid_length_unchanged
    CleanQ_RB_write_head_region_y_read_y_valid_length_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_y_valid_length_unchanged


paragraph \<open>Valid Offset Unchanged when Y writes and X reads\<close>

lemma CleanQ_RB_write_head_length_y_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_y x rb)) = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_flags_y_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_y x rb)) = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_offset_y_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_y x rb)) = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_region_y_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_y x rb)) = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_y x rb)) = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemmas CleanQ_RB_write_head_y_read_x_valid_length_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_x_valid_length_unchanged
    CleanQ_RB_write_head_flags_y_read_x_valid_length_unchanged
    CleanQ_RB_write_head_offset_y_read_x_valid_length_unchanged
    CleanQ_RB_write_head_region_y_read_x_valid_length_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_x_valid_length_unchanged




paragraph \<open>Write head Invariant X\<close>

lemma CleanQ_RB_write_head_x_offset_inv:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_offset_x x rb)"
  by (metis CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_Invariant CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_x_length_inv:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_length_x x rb)"
  by (metis CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_Invariant CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_x_region_inv:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_region_x x rb)"
  by (metis CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_Invariant CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_x_valid_length_inv:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_valid_length_x x rb)"
  by (metis CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_Invariant CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_x_valid_offset_inv:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_valid_offset_x x rb)"
  by (metis CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_Invariant CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_x_flags_inv:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_flags_x x rb)"
  by (metis CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_Invariant CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_write_head_x_invariant[simp] = 
   CleanQ_RB_write_head_x_offset_inv
   CleanQ_RB_write_head_x_length_inv
   CleanQ_RB_write_head_x_region_inv
   CleanQ_RB_write_head_x_valid_length_inv
   CleanQ_RB_write_head_x_valid_offset_inv
   CleanQ_RB_write_head_x_flags_inv


paragraph \<open>Write head Invariant Y\<close>

lemma CleanQ_RB_write_head_y_offset_inv:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_offset_y x rb)"
  by (metis CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_y_Invariant CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_y_length_inv:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_length_y x rb)"
  by (metis CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_Invariant CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_y_region_inv:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_region_y x rb)"
  by (metis CleanQ_RB_write_head_region_y_def CleanQ_RB_write_head_y_Invariant CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_y_valid_length_inv:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_valid_length_y x rb)"
  by (metis CleanQ_RB_write_head_valid_length_y_def CleanQ_RB_write_head_y_Invariant CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_y_valid_offset_inv:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_valid_offset_y x rb)"
  by (metis CleanQ_RB_write_head_valid_offset_y_def CleanQ_RB_write_head_y_Invariant CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_y_flags_inv:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_flags_y x rb)"
  by (metis CleanQ_RB_write_head_flags_y_def CleanQ_RB_write_head_y_Invariant CleanQ_RB_write_head_y_def)

lemmas CleanQ_RB_write_head_y_invariant[simp] = 
   CleanQ_RB_write_head_y_offset_inv
   CleanQ_RB_write_head_y_length_inv
   CleanQ_RB_write_head_y_region_inv
   CleanQ_RB_write_head_y_valid_length_inv
   CleanQ_RB_write_head_y_valid_offset_inv
   CleanQ_RB_write_head_y_flags_inv


paragraph \<open>Write X Enq Remains Possible X\<close>

lemma CleanQ_RB_write_head_length_x_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_length_x x rb) = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_can_enq_x CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_offset_x_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_offset_x x rb) = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_can_enq_x CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_region_x_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_region_x x rb) = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_can_enq_x CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_flags_x_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_flags_x x rb) = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_can_enq_x CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_length_x_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_valid_length_x x rb) = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_can_enq_x CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_valid_offset_x x rb) = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_can_enq_x CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_write_head_x_enq_x_possible[simp] = 
   CleanQ_RB_write_head_length_x_enq_x_possible
   CleanQ_RB_write_head_offset_x_enq_x_possible
   CleanQ_RB_write_head_region_x_enq_x_possible
   CleanQ_RB_write_head_flags_x_enq_x_possible
   CleanQ_RB_write_head_valid_length_x_enq_x_possible
   CleanQ_RB_write_head_valid_offset_x_enq_x_possible

paragraph \<open>Read Tail Valid Length Y\<close>

lemma CleanQ_RB_read_tail_region_y_valid_length_y:
 "b = CleanQ_RB_read_tail_region_y rb b \<Longrightarrow> CleanQ_RB_read_tail_region_y rb (CleanQ_RB_read_tail_valid_length_y rb b) = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_valid_length_y_def)

lemma CleanQ_RB_read_tail_offset_y_valid_length_y:
  "b = CleanQ_RB_read_tail_offset_y rb b \<Longrightarrow> CleanQ_RB_read_tail_offset_y rb (CleanQ_RB_read_tail_valid_length_y rb b) = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_valid_length_y_def)

lemma CleanQ_RB_read_tail_flags_y_valid_length_y:
  "b = CleanQ_RB_read_tail_flags_y rb b \<Longrightarrow> CleanQ_RB_read_tail_flags_y rb (CleanQ_RB_read_tail_valid_length_y rb b) = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(5) CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_valid_length_y_def)

lemma CleanQ_RB_read_tail_length_y_valid_length_y:
  "b = CleanQ_RB_read_tail_length_y rb b \<Longrightarrow> CleanQ_RB_read_tail_length_y rb (CleanQ_RB_read_tail_valid_length_y rb b) = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_valid_length_y_def)

lemma CleanQ_RB_read_tail_valid_offset_y_valid_length_y:
  "b = CleanQ_RB_read_tail_valid_offset_y rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y rb (CleanQ_RB_read_tail_valid_length_y rb b) = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemma CleanQ_RB_read_tail_valid_length_y_valid_length_y:
  "CleanQ_RB_read_tail_valid_length_y rb (CleanQ_RB_read_tail_valid_length_y rb b) = CleanQ_RB_read_tail_valid_length_y rb b"
  by (simp add: CleanQ_RB_read_tail_valid_length_y_def)

lemmas CleanQ_RB_read_tail_valid_length_y_simps[simp] = 
  CleanQ_RB_read_tail_region_y_valid_length_y
  CleanQ_RB_read_tail_length_y_valid_length_y
  CleanQ_RB_read_tail_flags_y_valid_length_y
  CleanQ_RB_read_tail_offset_y_valid_length_y
  CleanQ_RB_read_tail_valid_offset_y_valid_length_y
  CleanQ_RB_read_tail_valid_length_y_valid_length_y

paragraph \<open>Read Tail Valid Length X \<close>

lemma CleanQ_RB_read_tail_region_x_valid_length_x:
 "b = CleanQ_RB_read_tail_region_x rb b \<Longrightarrow> CleanQ_RB_read_tail_region_x rb (CleanQ_RB_read_tail_valid_length_x rb b) = CleanQ_RB_read_tail_valid_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_region_x_def CleanQ_RB_read_tail_valid_length_x_def)

lemma CleanQ_RB_read_tail_offset_x_valid_length_x:
  "b = CleanQ_RB_read_tail_offset_x rb b \<Longrightarrow> CleanQ_RB_read_tail_offset_x rb (CleanQ_RB_read_tail_valid_length_x rb b) = CleanQ_RB_read_tail_valid_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_valid_length_x_def)

lemma CleanQ_RB_read_tail_flags_x_valid_length_x:
  "b = CleanQ_RB_read_tail_flags_x rb b \<Longrightarrow> CleanQ_RB_read_tail_flags_x rb (CleanQ_RB_read_tail_valid_length_x rb b) = CleanQ_RB_read_tail_valid_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(5) CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_valid_length_x_def)

lemma CleanQ_RB_read_tail_length_x_valid_length_x:
  "b = CleanQ_RB_read_tail_length_x rb b \<Longrightarrow> CleanQ_RB_read_tail_length_x rb (CleanQ_RB_read_tail_valid_length_x rb b) = CleanQ_RB_read_tail_valid_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_valid_length_x_def)

lemma CleanQ_RB_read_tail_valid_offset_x_valid_length_x:
  "b = CleanQ_RB_read_tail_valid_offset_x rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x rb (CleanQ_RB_read_tail_valid_length_x rb b) = CleanQ_RB_read_tail_valid_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_valid_length_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemma CleanQ_RB_read_tail_valid_length_x_valid_length_x:
  "CleanQ_RB_read_tail_valid_length_x rb (CleanQ_RB_read_tail_valid_length_x rb b) = CleanQ_RB_read_tail_valid_length_x rb b"
  by (simp add: CleanQ_RB_read_tail_valid_length_x_def)

lemmas CleanQ_RB_read_tail_x_simps[simp] = 
  CleanQ_RB_read_tail_region_x_valid_length_x
  CleanQ_RB_read_tail_length_x_valid_length_x
  CleanQ_RB_read_tail_flags_x_valid_length_x
  CleanQ_RB_read_tail_offset_x_valid_length_x
  CleanQ_RB_read_tail_valid_offset_x_valid_length_x
  CleanQ_RB_read_tail_valid_length_x_valid_length_x


paragraph \<open>Read Tail Valid Offset Y\<close>

lemma CleanQ_RB_read_tail_region_y_valid_offset_y:
 "b = CleanQ_RB_read_tail_region_y rb b \<Longrightarrow> CleanQ_RB_read_tail_region_y rb (CleanQ_RB_read_tail_valid_offset_y rb b) = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(4) CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemma CleanQ_RB_read_tail_offset_y_valid_offset_y:
  "b = CleanQ_RB_read_tail_offset_y rb b \<Longrightarrow> CleanQ_RB_read_tail_offset_y rb (CleanQ_RB_read_tail_valid_offset_y rb b) = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(4) CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemma CleanQ_RB_read_tail_flags_y_valid_offset_y:
  "b = CleanQ_RB_read_tail_flags_y rb b \<Longrightarrow> CleanQ_RB_read_tail_flags_y rb (CleanQ_RB_read_tail_valid_offset_y rb b) = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemma CleanQ_RB_read_tail_length_y_valid_offset_y:
  "b = CleanQ_RB_read_tail_length_y rb b \<Longrightarrow> CleanQ_RB_read_tail_length_y rb (CleanQ_RB_read_tail_valid_offset_y rb b) = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(4) CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemma CleanQ_RB_read_tail_valid_length_y_valid_offset_y:
  "b = CleanQ_RB_read_tail_valid_length_y rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y rb (CleanQ_RB_read_tail_valid_offset_y rb b) = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemma CleanQ_RB_read_tail_valid_offset_y_valid_offset_y:
  "CleanQ_RB_read_tail_valid_offset_y rb (CleanQ_RB_read_tail_valid_offset_y rb b) = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (simp add: CleanQ_RB_read_tail_valid_offset_y_def)

lemmas CleanQ_RB_read_tail_valid_offset_y_simps[simp] = 
  CleanQ_RB_read_tail_region_y_valid_offset_y
  CleanQ_RB_read_tail_length_y_valid_offset_y
  CleanQ_RB_read_tail_flags_y_valid_offset_y
  CleanQ_RB_read_tail_offset_y_valid_offset_y
  CleanQ_RB_read_tail_valid_offset_y_valid_offset_y
  CleanQ_RB_read_tail_valid_length_y_valid_offset_y


paragraph \<open>Read Tail Valid Offset X\<close>

lemma CleanQ_RB_read_tail_region_x_valid_offset_x:
 "b = CleanQ_RB_read_tail_region_x rb b \<Longrightarrow> CleanQ_RB_read_tail_region_x rb (CleanQ_RB_read_tail_valid_offset_x rb b) = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(4) CleanQ_RB_read_tail_region_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemma CleanQ_RB_read_tail_offset_x_valid_offset_x:
  "b = CleanQ_RB_read_tail_offset_x rb b \<Longrightarrow> CleanQ_RB_read_tail_offset_x rb (CleanQ_RB_read_tail_valid_offset_x rb b) = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(4) CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemma CleanQ_RB_read_tail_flags_x_valid_offset_x:
  "b = CleanQ_RB_read_tail_flags_x rb b \<Longrightarrow> CleanQ_RB_read_tail_flags_x rb (CleanQ_RB_read_tail_valid_offset_x rb b) = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemma CleanQ_RB_read_tail_length_x_valid_offset_x:
  "b = CleanQ_RB_read_tail_length_x rb b \<Longrightarrow> CleanQ_RB_read_tail_length_x rb (CleanQ_RB_read_tail_valid_offset_x rb b) = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(4) CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemma CleanQ_RB_read_tail_valid_length_x_valid_offset_x:
  "b = CleanQ_RB_read_tail_valid_length_x rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x rb (CleanQ_RB_read_tail_valid_offset_x rb b) = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_valid_length_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemma CleanQ_RB_read_tail_valid_offset_x_valid_offset_x:
  "CleanQ_RB_read_tail_valid_offset_x rb (CleanQ_RB_read_tail_valid_offset_x rb b) = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (simp add: CleanQ_RB_read_tail_valid_offset_x_def)

lemmas CleanQ_RB_read_tail_valid_offset_x_simps[simp] = 
  CleanQ_RB_read_tail_region_x_valid_offset_x
  CleanQ_RB_read_tail_length_x_valid_offset_x
  CleanQ_RB_read_tail_flags_x_valid_offset_x
  CleanQ_RB_read_tail_offset_x_valid_offset_x
  CleanQ_RB_read_tail_valid_length_x_valid_offset_x
  CleanQ_RB_read_tail_valid_offset_x_valid_offset_x


paragraph \<open>Read Tail Length Y\<close>

lemma CleanQ_RB_read_tail_region_y_length_y:
 "b = CleanQ_RB_read_tail_region_y rb b \<Longrightarrow> CleanQ_RB_read_tail_region_y rb (CleanQ_RB_read_tail_length_y rb b) = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(3) CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_region_y_def)

lemma CleanQ_RB_read_tail_offset_y_length_y:
  "b = CleanQ_RB_read_tail_offset_y rb b \<Longrightarrow> CleanQ_RB_read_tail_offset_y rb (CleanQ_RB_read_tail_length_y rb b) = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(3) CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_offset_y_def)

lemma CleanQ_RB_read_tail_flags_y_length_y:
  "b = CleanQ_RB_read_tail_flags_y rb b \<Longrightarrow> CleanQ_RB_read_tail_flags_y rb (CleanQ_RB_read_tail_length_y rb b) = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_length_y_def)

lemma CleanQ_RB_read_tail_valid_offset_y_length_y:
  "b = CleanQ_RB_read_tail_valid_offset_y rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y rb (CleanQ_RB_read_tail_length_y rb b) = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_Buffer.cases_scheme CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(4) CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemma CleanQ_RB_read_tail_valid_length_y_length_y:
  "b = CleanQ_RB_read_tail_valid_length_y rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y rb (CleanQ_RB_read_tail_length_y rb b) = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_valid_length_y_def)

lemma CleanQ_RB_read_tail_length_y_length_y:
  "CleanQ_RB_read_tail_length_y rb (CleanQ_RB_read_tail_length_y rb b) = CleanQ_RB_read_tail_length_y rb b"
  by (simp add: CleanQ_RB_read_tail_length_y_def)

lemmas CleanQ_RB_read_tail_length_y_simps[simp] = 
  CleanQ_RB_read_tail_region_y_length_y
  CleanQ_RB_read_tail_length_y_length_y
  CleanQ_RB_read_tail_flags_y_length_y
  CleanQ_RB_read_tail_offset_y_length_y
  CleanQ_RB_read_tail_valid_offset_y_length_y
  CleanQ_RB_read_tail_valid_length_y_length_y

paragraph \<open>Read Tail Length X\<close>

lemma CleanQ_RB_read_tail_region_x_length_x:
 "b = CleanQ_RB_read_tail_region_x rb b \<Longrightarrow> CleanQ_RB_read_tail_region_x rb (CleanQ_RB_read_tail_length_x rb b) = CleanQ_RB_read_tail_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(3) CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_region_x_def)

lemma CleanQ_RB_read_tail_offset_x_length_x:
  "b = CleanQ_RB_read_tail_offset_x rb b \<Longrightarrow> CleanQ_RB_read_tail_offset_x rb (CleanQ_RB_read_tail_length_x rb b) = CleanQ_RB_read_tail_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(3) CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_offset_x_def)

lemma CleanQ_RB_read_tail_flags_x_length_x:
  "b = CleanQ_RB_read_tail_flags_x rb b \<Longrightarrow> CleanQ_RB_read_tail_flags_x rb (CleanQ_RB_read_tail_length_x rb b) = CleanQ_RB_read_tail_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_length_x_def)

lemma CleanQ_RB_read_tail_valid_offset_x_length_x:
  "b = CleanQ_RB_read_tail_valid_offset_x rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x rb (CleanQ_RB_read_tail_length_x rb b) = CleanQ_RB_read_tail_length_x rb b"
  by (metis CleanQ_Buffer.cases_scheme CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(4) CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemma CleanQ_RB_read_tail_valid_length_x_length_x:
  "b = CleanQ_RB_read_tail_valid_length_x rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x rb (CleanQ_RB_read_tail_length_x rb b) = CleanQ_RB_read_tail_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_valid_length_x_def)

lemma CleanQ_RB_read_tail_length_x_length_x:
  "CleanQ_RB_read_tail_length_x rb (CleanQ_RB_read_tail_length_x rb b) = CleanQ_RB_read_tail_length_x rb b"
  by (simp add: CleanQ_RB_read_tail_length_x_def)

lemmas CleanQ_RB_read_tail_length_x_simps[simp] = 
  CleanQ_RB_read_tail_region_x_length_x
  CleanQ_RB_read_tail_length_x_length_x
  CleanQ_RB_read_tail_flags_x_length_x
  CleanQ_RB_read_tail_offset_x_length_x
  CleanQ_RB_read_tail_valid_offset_x_length_x
  CleanQ_RB_read_tail_valid_length_x_length_x

paragraph \<open>Read Tail  Offset Y\<close>

lemma CleanQ_RB_read_tail_region_y_offset_y:
 "b = CleanQ_RB_read_tail_region_y rb b \<Longrightarrow> CleanQ_RB_read_tail_region_y rb (CleanQ_RB_read_tail_offset_y rb b) = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_Buffer.simps(8) CleanQ_Buffer.simps(9) CleanQ_Buffer.surjective CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_region_y_def)

lemma CleanQ_RB_read_tail_offset_y_offset_y:
  "CleanQ_RB_read_tail_offset_y rb (CleanQ_RB_read_tail_offset_y rb b) = CleanQ_RB_read_tail_offset_y rb b"
  by(simp add:CleanQ_RB_read_tail_offset_y_def)

lemma CleanQ_RB_read_tail_flags_y_offset_y:
  "b = CleanQ_RB_read_tail_flags_y rb b \<Longrightarrow> CleanQ_RB_read_tail_flags_y rb (CleanQ_RB_read_tail_offset_y rb b) = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_Buffer.simps(13) CleanQ_Buffer.simps(9) CleanQ_Buffer.surjective CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_offset_y_def)
  

lemma CleanQ_RB_read_tail_length_y_offset_y:
  "b = CleanQ_RB_read_tail_length_y rb b \<Longrightarrow> CleanQ_RB_read_tail_length_y rb (CleanQ_RB_read_tail_offset_y rb b) = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_Buffer.cases_scheme CleanQ_Buffer.simps(10) CleanQ_Buffer.simps(9) CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_offset_y_def)

lemma CleanQ_RB_read_tail_valid_length_y_offset_y:
  "b = CleanQ_RB_read_tail_valid_length_y rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y rb (CleanQ_RB_read_tail_offset_y rb b) = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_valid_length_y_def)

lemma CleanQ_RB_read_tail_valid_offset_y_offset_y:
  "b = CleanQ_RB_read_tail_valid_offset_y rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y rb (CleanQ_RB_read_tail_offset_y rb b) = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(4) CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemmas CleanQ_RB_read_tail_offset_y_simps[simp] = 
  CleanQ_RB_read_tail_region_y_offset_y
  CleanQ_RB_read_tail_length_y_offset_y
  CleanQ_RB_read_tail_flags_y_offset_y
  CleanQ_RB_read_tail_offset_y_offset_y
  CleanQ_RB_read_tail_valid_length_y_offset_y
  CleanQ_RB_read_tail_valid_offset_y_offset_y

paragraph \<open>Read Tail  Offset X\<close>

lemma CleanQ_RB_read_tail_region_x_offset_x:
 "b = CleanQ_RB_read_tail_region_x rb b \<Longrightarrow> CleanQ_RB_read_tail_region_x rb (CleanQ_RB_read_tail_offset_x rb b) = CleanQ_RB_read_tail_offset_x rb b"
  by (metis CleanQ_Buffer.simps(8) CleanQ_Buffer.simps(9) CleanQ_Buffer.surjective CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_region_x_def)

lemma CleanQ_RB_read_tail_offset_x_offset_x:
  "CleanQ_RB_read_tail_offset_x rb (CleanQ_RB_read_tail_offset_x rb b) = CleanQ_RB_read_tail_offset_x rb b"
  by(simp add:CleanQ_RB_read_tail_offset_x_def)

lemma CleanQ_RB_read_tail_flags_x_offset_x:
  "b = CleanQ_RB_read_tail_flags_x rb b \<Longrightarrow> CleanQ_RB_read_tail_flags_x rb (CleanQ_RB_read_tail_offset_x rb b) = CleanQ_RB_read_tail_offset_x rb b"
  by (metis CleanQ_Buffer.simps(13) CleanQ_Buffer.simps(9) CleanQ_Buffer.surjective CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_offset_x_def)
  

lemma CleanQ_RB_read_tail_length_x_offset_x:
  "b = CleanQ_RB_read_tail_length_x rb b \<Longrightarrow> CleanQ_RB_read_tail_length_x rb (CleanQ_RB_read_tail_offset_x rb b) = CleanQ_RB_read_tail_offset_x rb b"
  by (metis CleanQ_Buffer.cases_scheme CleanQ_Buffer.simps(10) CleanQ_Buffer.simps(9) CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_offset_x_def)

lemma CleanQ_RB_read_tail_valid_length_x_offset_x:
  "b = CleanQ_RB_read_tail_valid_length_x rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x rb (CleanQ_RB_read_tail_offset_x rb b) = CleanQ_RB_read_tail_offset_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_valid_length_x_def)

lemma CleanQ_RB_read_tail_valid_offset_x_offset_x:
  "b = CleanQ_RB_read_tail_valid_offset_x rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x rb (CleanQ_RB_read_tail_offset_x rb b) = CleanQ_RB_read_tail_offset_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(4) CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemmas CleanQ_RB_read_tail_offset_x_simps[simp] = 
  CleanQ_RB_read_tail_region_x_offset_x
  CleanQ_RB_read_tail_length_x_offset_x
  CleanQ_RB_read_tail_flags_x_offset_x
  CleanQ_RB_read_tail_offset_x_offset_x
  CleanQ_RB_read_tail_valid_length_x_offset_x
  CleanQ_RB_read_tail_valid_offset_x_offset_x

paragraph \<open>Read Tail  Region X\<close>

lemma CleanQ_RB_read_tail_region_y_region_y:
 "CleanQ_RB_read_tail_region_y rb (CleanQ_RB_read_tail_region_y rb b) = CleanQ_RB_read_tail_region_y rb b"
  by(simp add:CleanQ_RB_read_tail_region_y_def)

lemma CleanQ_RB_read_tail_offset_y_region_y:
  "b = CleanQ_RB_read_tail_offset_y rb b \<Longrightarrow> CleanQ_RB_read_tail_offset_y rb (CleanQ_RB_read_tail_region_y rb b) = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_Buffer.cases_scheme CleanQ_Buffer.simps(8) CleanQ_Buffer.simps(9) CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_region_y_def)

lemma CleanQ_RB_read_tail_flags_y_region_y:
  "b = CleanQ_RB_read_tail_flags_y rb b \<Longrightarrow> CleanQ_RB_read_tail_flags_y rb (CleanQ_RB_read_tail_region_y rb b) = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_Buffer.simps(13) CleanQ_Buffer.simps(8) CleanQ_Buffer.surjective CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_region_y_def)
  
lemma CleanQ_RB_read_tail_length_y_region_y:
  "b = CleanQ_RB_read_tail_length_y rb b \<Longrightarrow> CleanQ_RB_read_tail_length_y rb (CleanQ_RB_read_tail_region_y rb b) = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(3) CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_region_y_def)

lemma CleanQ_RB_read_tail_valid_length_y_region_y:
  "b = CleanQ_RB_read_tail_valid_length_y rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y rb (CleanQ_RB_read_tail_region_y rb b) = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_valid_length_y_def)

lemma CleanQ_RB_read_tail_valid_offset_y_region_y:
  "b = CleanQ_RB_read_tail_valid_offset_y rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y rb (CleanQ_RB_read_tail_region_y rb b) = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(4) CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemmas CleanQ_RB_read_tail_region_y_simps[simp] = 
  CleanQ_RB_read_tail_region_y_region_y
  CleanQ_RB_read_tail_length_y_region_y
  CleanQ_RB_read_tail_flags_y_region_y
  CleanQ_RB_read_tail_offset_y_region_y
  CleanQ_RB_read_tail_valid_length_y_region_y
  CleanQ_RB_read_tail_valid_offset_y_region_y

paragraph \<open>Read Tail  Region X\<close>

lemma CleanQ_RB_read_tail_region_x_region_x:
 "CleanQ_RB_read_tail_region_x rb (CleanQ_RB_read_tail_region_x rb b) = CleanQ_RB_read_tail_region_x rb b"
  by(simp add:CleanQ_RB_read_tail_region_x_def)

lemma CleanQ_RB_read_tail_offset_x_region_x:
  "b = CleanQ_RB_read_tail_offset_x rb b \<Longrightarrow> CleanQ_RB_read_tail_offset_x rb (CleanQ_RB_read_tail_region_x rb b) = CleanQ_RB_read_tail_region_x rb b"
  by (metis CleanQ_Buffer.cases_scheme CleanQ_Buffer.simps(8) CleanQ_Buffer.simps(9) CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_region_x_def)

lemma CleanQ_RB_read_tail_flags_x_region_x:
  "b = CleanQ_RB_read_tail_flags_x rb b \<Longrightarrow> CleanQ_RB_read_tail_flags_x rb (CleanQ_RB_read_tail_region_x rb b) = CleanQ_RB_read_tail_region_x rb b"
  by (metis CleanQ_Buffer.simps(13) CleanQ_Buffer.simps(8) CleanQ_Buffer.surjective CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_region_x_def)
  
lemma CleanQ_RB_read_tail_length_x_region_x:
  "b = CleanQ_RB_read_tail_length_x rb b \<Longrightarrow> CleanQ_RB_read_tail_length_x rb (CleanQ_RB_read_tail_region_x rb b) = CleanQ_RB_read_tail_region_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(3) CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_region_x_def)

lemma CleanQ_RB_read_tail_valid_length_x_region_x:
  "b = CleanQ_RB_read_tail_valid_length_x rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x rb (CleanQ_RB_read_tail_region_x rb b) = CleanQ_RB_read_tail_region_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_region_x_def CleanQ_RB_read_tail_valid_length_x_def)

lemma CleanQ_RB_read_tail_valid_offset_x_region_x:
  "b = CleanQ_RB_read_tail_valid_offset_x rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x rb (CleanQ_RB_read_tail_region_x rb b) = CleanQ_RB_read_tail_region_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(4) CleanQ_RB_read_tail_region_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemmas CleanQ_RB_read_tail_region_x_simps[simp] = 
  CleanQ_RB_read_tail_region_x_region_x
  CleanQ_RB_read_tail_length_x_region_x
  CleanQ_RB_read_tail_flags_x_region_x
  CleanQ_RB_read_tail_offset_x_region_x
  CleanQ_RB_read_tail_valid_length_x_region_x
  CleanQ_RB_read_tail_valid_offset_x_region_x


paragraph \<open>Read Tail  Flags Y\<close>

lemma CleanQ_RB_read_tail_flags_y_flags_y:
 "CleanQ_RB_read_tail_flags_y rb (CleanQ_RB_read_tail_flags_y rb b) = CleanQ_RB_read_tail_flags_y rb b"
  by(simp add:CleanQ_RB_read_tail_flags_y_def)

lemma CleanQ_RB_read_tail_offset_y_flags_y:
  "b = CleanQ_RB_read_tail_offset_y rb b \<Longrightarrow> CleanQ_RB_read_tail_offset_y rb (CleanQ_RB_read_tail_flags_y rb b) = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_offset_y_def)

lemma CleanQ_RB_read_tail_region_y_flags_y:
  "b = CleanQ_RB_read_tail_region_y rb b \<Longrightarrow> CleanQ_RB_read_tail_region_y rb (CleanQ_RB_read_tail_flags_y rb b) = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_region_y_def)
  
lemma CleanQ_RB_read_tail_length_y_flags_y:
  "b = CleanQ_RB_read_tail_length_y rb b \<Longrightarrow> CleanQ_RB_read_tail_length_y rb (CleanQ_RB_read_tail_flags_y rb b) = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_length_y_def)

lemma CleanQ_RB_read_tail_valid_length_y_flags_y:
  "b = CleanQ_RB_read_tail_valid_length_y rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y rb (CleanQ_RB_read_tail_flags_y rb b) = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(5) CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_valid_length_y_def)

lemma CleanQ_RB_read_tail_valid_offset_y_flags_y:
  "b = CleanQ_RB_read_tail_valid_offset_y rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y rb (CleanQ_RB_read_tail_flags_y rb b) = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemmas CleanQ_RB_read_tail_flags_y_simps[simp] = 
  CleanQ_RB_read_tail_flags_y_flags_y
  CleanQ_RB_read_tail_length_y_flags_y
  CleanQ_RB_read_tail_region_y_flags_y
  CleanQ_RB_read_tail_offset_y_flags_y
  CleanQ_RB_read_tail_valid_length_y_flags_y
  CleanQ_RB_read_tail_valid_offset_y_flags_y


paragraph \<open>Read Tail  Flags X\<close>

lemma CleanQ_RB_read_tail_flags_x_flags_x:
 "CleanQ_RB_read_tail_flags_x rb (CleanQ_RB_read_tail_flags_x rb b) = CleanQ_RB_read_tail_flags_x rb b"
  by(simp add:CleanQ_RB_read_tail_flags_x_def)

lemma CleanQ_RB_read_tail_offset_x_flags_x:
  "b = CleanQ_RB_read_tail_offset_x rb b \<Longrightarrow> CleanQ_RB_read_tail_offset_x rb (CleanQ_RB_read_tail_flags_x rb b) = CleanQ_RB_read_tail_flags_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_offset_x_def)

lemma CleanQ_RB_read_tail_region_x_flags_x:
  "b = CleanQ_RB_read_tail_region_x rb b \<Longrightarrow> CleanQ_RB_read_tail_region_x rb (CleanQ_RB_read_tail_flags_x rb b) = CleanQ_RB_read_tail_flags_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_region_x_def)
  
lemma CleanQ_RB_read_tail_length_x_flags_x:
  "b = CleanQ_RB_read_tail_length_x rb b \<Longrightarrow> CleanQ_RB_read_tail_length_x rb (CleanQ_RB_read_tail_flags_x rb b) = CleanQ_RB_read_tail_flags_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_length_x_def)

lemma CleanQ_RB_read_tail_valid_length_x_flags_x:
  "b = CleanQ_RB_read_tail_valid_length_x rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x rb (CleanQ_RB_read_tail_flags_x rb b) = CleanQ_RB_read_tail_flags_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(5) CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_valid_length_x_def)

lemma CleanQ_RB_read_tail_valid_offset_x_flags_x:
  "b = CleanQ_RB_read_tail_valid_offset_x rb b \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x rb (CleanQ_RB_read_tail_flags_x rb b) = CleanQ_RB_read_tail_flags_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemmas CleanQ_RB_read_tail_flags_x_simps[simp] = 
  CleanQ_RB_read_tail_flags_x_flags_x
  CleanQ_RB_read_tail_length_x_flags_x
  CleanQ_RB_read_tail_region_x_flags_x
  CleanQ_RB_read_tail_offset_x_flags_x
  CleanQ_RB_read_tail_valid_length_x_flags_x
  CleanQ_RB_read_tail_valid_offset_x_flags_x


paragraph \<open>Read Y, Writes X Unchanged\<close>

lemma CleanQ_RB_read_tail_region_y_write_flags_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_region_y (CleanQ_RB_write_head_flags_x f rb) b = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_region_y_write_region_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_region_y (CleanQ_RB_write_head_region_x f rb) b = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_region_y_write_offset_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_region_y (CleanQ_RB_write_head_offset_x f rb) b = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_region_y_write_length_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_region_y (CleanQ_RB_write_head_length_x f rb) b = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_region_y_write_valid_offset_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_region_y (CleanQ_RB_write_head_valid_offset_x f rb) b = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_region_y_write_valid_length_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_region_y (CleanQ_RB_write_head_valid_length_x f rb) b = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_read_tail_region_y_write_x[simp] = 
     CleanQ_RB_read_tail_region_y_write_flags_x
     CleanQ_RB_read_tail_region_y_write_region_x
     CleanQ_RB_read_tail_region_y_write_offset_x
     CleanQ_RB_read_tail_region_y_write_length_x
     CleanQ_RB_read_tail_region_y_write_valid_offset_x
     CleanQ_RB_read_tail_region_y_write_valid_length_x


lemma CleanQ_RB_read_tail_offset_y_write_flags_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_offset_y (CleanQ_RB_write_head_flags_x f rb) b = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_offset_y_write_region_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_offset_y (CleanQ_RB_write_head_region_x f rb) b = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_offset_y_write_offset_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_offset_y (CleanQ_RB_write_head_offset_x f rb) b = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_offset_y_write_length_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_offset_y (CleanQ_RB_write_head_length_x f rb) b = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_offset_y_write_valid_offset_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_offset_y (CleanQ_RB_write_head_valid_offset_x f rb) b = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_offset_y_write_valid_length_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_offset_y (CleanQ_RB_write_head_valid_length_x f rb) b = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_read_tail_offset_y_write_x[simp] = 
     CleanQ_RB_read_tail_offset_y_write_flags_x
     CleanQ_RB_read_tail_offset_y_write_region_x
     CleanQ_RB_read_tail_offset_y_write_offset_x
     CleanQ_RB_read_tail_offset_y_write_length_x
     CleanQ_RB_read_tail_offset_y_write_valid_offset_x
     CleanQ_RB_read_tail_offset_y_write_valid_length_x

lemma CleanQ_RB_read_tail_length_y_write_flags_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_length_y (CleanQ_RB_write_head_flags_x f rb) b = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_length_y_write_region_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_length_y (CleanQ_RB_write_head_region_x f rb) b = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_length_y_write_offset_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_length_y (CleanQ_RB_write_head_offset_x f rb) b = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_length_y_write_length_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_length_y (CleanQ_RB_write_head_length_x f rb) b = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_length_y_write_valid_offset_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_length_y (CleanQ_RB_write_head_valid_offset_x f rb) b = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_length_y_write_valid_length_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_length_y (CleanQ_RB_write_head_valid_length_x f rb) b = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_read_tail_length_y_write_x[simp] = 
     CleanQ_RB_read_tail_length_y_write_flags_x
     CleanQ_RB_read_tail_length_y_write_region_x
     CleanQ_RB_read_tail_length_y_write_offset_x
     CleanQ_RB_read_tail_length_y_write_length_x
     CleanQ_RB_read_tail_length_y_write_valid_offset_x
     CleanQ_RB_read_tail_length_y_write_valid_length_x


lemma CleanQ_RB_read_tail_flags_y_write_flags_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_flags_y (CleanQ_RB_write_head_flags_x f rb) b = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_flags_y_write_region_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_flags_y (CleanQ_RB_write_head_region_x f rb) b = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_flags_y_write_offset_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_flags_y (CleanQ_RB_write_head_offset_x f rb) b = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_flags_y_write_length_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_flags_y (CleanQ_RB_write_head_length_x f rb) b = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_flags_y_write_valid_offset_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_flags_y (CleanQ_RB_write_head_valid_offset_x f rb) b = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_flags_y_write_valid_length_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_flags_y (CleanQ_RB_write_head_valid_length_x f rb) b = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_read_tail_flags_y_write_x[simp] = 
     CleanQ_RB_read_tail_flags_y_write_flags_x
     CleanQ_RB_read_tail_flags_y_write_region_x
     CleanQ_RB_read_tail_flags_y_write_offset_x
     CleanQ_RB_read_tail_flags_y_write_length_x
     CleanQ_RB_read_tail_flags_y_write_valid_offset_x
     CleanQ_RB_read_tail_flags_y_write_valid_length_x

lemma CleanQ_RB_read_tail_valid_offset_y_write_flags_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y (CleanQ_RB_write_head_flags_x f rb) b = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_offset_y_write_region_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y (CleanQ_RB_write_head_region_x f rb) b = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_offset_y_write_offset_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y (CleanQ_RB_write_head_offset_x f rb) b = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_offset_y_write_length_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y (CleanQ_RB_write_head_length_x f rb) b = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_offset_y_write_valid_offset_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y (CleanQ_RB_write_head_valid_offset_x f rb) b = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_offset_y_write_valid_length_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y (CleanQ_RB_write_head_valid_length_x f rb) b = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_read_tail_valid_offset_y_write_x[simp] = 
     CleanQ_RB_read_tail_valid_offset_y_write_flags_x
     CleanQ_RB_read_tail_valid_offset_y_write_region_x
     CleanQ_RB_read_tail_valid_offset_y_write_offset_x
     CleanQ_RB_read_tail_valid_offset_y_write_length_x
     CleanQ_RB_read_tail_valid_offset_y_write_valid_offset_x
     CleanQ_RB_read_tail_valid_offset_y_write_valid_length_x

lemma CleanQ_RB_read_tail_valid_length_y_write_flags_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y (CleanQ_RB_write_head_flags_x f rb) b = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_length_y_write_region_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y (CleanQ_RB_write_head_region_x f rb) b = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_length_y_write_offset_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y (CleanQ_RB_write_head_offset_x f rb) b = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_length_y_write_length_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y (CleanQ_RB_write_head_length_x f rb) b = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_length_y_write_valid_offset_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y (CleanQ_RB_write_head_valid_offset_x f rb) b = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_length_y_write_valid_length_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y (CleanQ_RB_write_head_valid_length_x f rb) b = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_read_tail_valid_length_y_write_x[simp] = 
     CleanQ_RB_read_tail_valid_length_y_write_flags_x
     CleanQ_RB_read_tail_valid_length_y_write_region_x
     CleanQ_RB_read_tail_valid_length_y_write_offset_x
     CleanQ_RB_read_tail_valid_length_y_write_length_x
     CleanQ_RB_read_tail_valid_length_y_write_valid_offset_x
     CleanQ_RB_read_tail_valid_length_y_write_valid_length_x



paragraph \<open>Read X, Writes Y Unchanged\<close>


lemma CleanQ_RB_read_tail_valid_length_x_write_flags_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x (CleanQ_RB_write_head_flags_y f rb) b = CleanQ_RB_read_tail_valid_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_length_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_read_tail_valid_length_x_write_region_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x (CleanQ_RB_write_head_region_y f rb) b = CleanQ_RB_read_tail_valid_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_length_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_read_tail_valid_length_x_write_offset_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x (CleanQ_RB_write_head_offset_y f rb) b = CleanQ_RB_read_tail_valid_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_length_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_read_tail_valid_length_x_write_length_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x (CleanQ_RB_write_head_length_y f rb) b = CleanQ_RB_read_tail_valid_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_length_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_read_tail_valid_length_x_write_valid_offset_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x (CleanQ_RB_write_head_valid_offset_y f rb) b = CleanQ_RB_read_tail_valid_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_length_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_read_tail_valid_length_x_write_valid_length_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x (CleanQ_RB_write_head_valid_length_y f rb) b = CleanQ_RB_read_tail_valid_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_length_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_read_tail_valid_length_x_write_y[simp] = 
     CleanQ_RB_read_tail_valid_length_x_write_flags_y
     CleanQ_RB_read_tail_valid_length_x_write_region_y
     CleanQ_RB_read_tail_valid_length_x_write_offset_y
     CleanQ_RB_read_tail_valid_length_x_write_length_y
     CleanQ_RB_read_tail_valid_length_x_write_valid_offset_y
     CleanQ_RB_read_tail_valid_length_x_write_valid_length_y



lemma CleanQ_RB_read_tail_valid_offset_x_write_flags_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x (CleanQ_RB_write_head_flags_y f rb) b = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_offset_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_read_tail_valid_offset_x_write_region_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x (CleanQ_RB_write_head_region_y f rb) b = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_offset_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_read_tail_valid_offset_x_write_offset_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x (CleanQ_RB_write_head_offset_y f rb) b = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_offset_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_read_tail_valid_offset_x_write_length_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x (CleanQ_RB_write_head_length_y f rb) b = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_offset_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_read_tail_valid_offset_x_write_valid_offset_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x (CleanQ_RB_write_head_valid_offset_y f rb) b = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_offset_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_read_tail_valid_offset_x_write_valid_length_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x (CleanQ_RB_write_head_valid_length_y f rb) b = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_offset_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_read_tail_valid_offset_x_write_y[simp] = 
     CleanQ_RB_read_tail_valid_offset_x_write_flags_y
     CleanQ_RB_read_tail_valid_offset_x_write_region_y
     CleanQ_RB_read_tail_valid_offset_x_write_offset_y
     CleanQ_RB_read_tail_valid_offset_x_write_length_y
     CleanQ_RB_read_tail_valid_offset_x_write_valid_offset_y
     CleanQ_RB_read_tail_valid_offset_x_write_valid_length_y

lemma CleanQ_RB_read_tail_flags_x_write_flags_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_flags_x (CleanQ_RB_write_head_flags_y f rb) b = CleanQ_RB_read_tail_flags_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_flags_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_read_tail_flags_x_write_region_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_flags_x (CleanQ_RB_write_head_region_y f rb) b = CleanQ_RB_read_tail_flags_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_flags_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_read_tail_flags_x_write_offset_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_flags_x (CleanQ_RB_write_head_offset_y f rb) b = CleanQ_RB_read_tail_flags_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_flags_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_read_tail_flags_x_write_length_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_flags_x (CleanQ_RB_write_head_length_y f rb) b = CleanQ_RB_read_tail_flags_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_flags_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_read_tail_flags_x_write_valid_offset_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_flags_x (CleanQ_RB_write_head_valid_offset_y f rb) b = CleanQ_RB_read_tail_flags_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_flags_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_read_tail_flags_x_write_valid_length_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_flags_x (CleanQ_RB_write_head_valid_length_y f rb) b = CleanQ_RB_read_tail_flags_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_flags_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_read_tail_flags_x_write_y[simp] = 
     CleanQ_RB_read_tail_flags_x_write_flags_y
     CleanQ_RB_read_tail_flags_x_write_region_y
     CleanQ_RB_read_tail_flags_x_write_offset_y
     CleanQ_RB_read_tail_flags_x_write_length_y
     CleanQ_RB_read_tail_flags_x_write_valid_offset_y
     CleanQ_RB_read_tail_flags_x_write_valid_length_y


lemma CleanQ_RB_read_tail_offset_x_write_flags_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_offset_x (CleanQ_RB_write_head_flags_y f rb) b = CleanQ_RB_read_tail_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_offset_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_read_tail_offset_x_write_region_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_offset_x (CleanQ_RB_write_head_region_y f rb) b = CleanQ_RB_read_tail_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_offset_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_read_tail_offset_x_write_offset_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_offset_x (CleanQ_RB_write_head_offset_y f rb) b = CleanQ_RB_read_tail_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_offset_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_read_tail_offset_x_write_length_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_offset_x (CleanQ_RB_write_head_length_y f rb) b = CleanQ_RB_read_tail_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_offset_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_read_tail_offset_x_write_valid_offset_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_offset_x (CleanQ_RB_write_head_valid_offset_y f rb) b = CleanQ_RB_read_tail_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_offset_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_read_tail_offset_x_write_valid_length_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_offset_x (CleanQ_RB_write_head_valid_length_y f rb) b = CleanQ_RB_read_tail_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_offset_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_read_tail_offset_x_write_y[simp] = 
     CleanQ_RB_read_tail_offset_x_write_flags_y
     CleanQ_RB_read_tail_offset_x_write_region_y
     CleanQ_RB_read_tail_offset_x_write_offset_y
     CleanQ_RB_read_tail_offset_x_write_length_y
     CleanQ_RB_read_tail_offset_x_write_valid_offset_y
     CleanQ_RB_read_tail_offset_x_write_valid_length_y

lemma CleanQ_RB_read_tail_length_x_write_flags_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_length_x (CleanQ_RB_write_head_flags_y f rb) b = CleanQ_RB_read_tail_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_length_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_read_tail_length_x_write_region_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_length_x (CleanQ_RB_write_head_region_y f rb) b = CleanQ_RB_read_tail_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_length_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_read_tail_length_x_write_offset_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_length_x (CleanQ_RB_write_head_offset_y f rb) b = CleanQ_RB_read_tail_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_length_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_read_tail_length_x_write_length_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_length_x (CleanQ_RB_write_head_length_y f rb) b = CleanQ_RB_read_tail_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_length_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_read_tail_length_x_write_valid_offset_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_length_x (CleanQ_RB_write_head_valid_offset_y f rb) b = CleanQ_RB_read_tail_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_length_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_read_tail_length_x_write_valid_length_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_length_x (CleanQ_RB_write_head_valid_length_y f rb) b = CleanQ_RB_read_tail_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_length_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_read_tail_length_x_write_y[simp] = 
     CleanQ_RB_read_tail_length_x_write_flags_y
     CleanQ_RB_read_tail_length_x_write_region_y
     CleanQ_RB_read_tail_length_x_write_offset_y
     CleanQ_RB_read_tail_length_x_write_length_y
     CleanQ_RB_read_tail_length_x_write_valid_offset_y
     CleanQ_RB_read_tail_length_x_write_valid_length_y


lemma CleanQ_RB_read_tail_region_x_write_flags_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_region_x (CleanQ_RB_write_head_flags_y f rb) b = CleanQ_RB_read_tail_region_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_region_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_read_tail_region_x_write_region_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_region_x (CleanQ_RB_write_head_region_y f rb) b = CleanQ_RB_read_tail_region_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_region_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_read_tail_region_x_write_offset_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_region_x (CleanQ_RB_write_head_offset_y f rb) b = CleanQ_RB_read_tail_region_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_region_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_read_tail_region_x_write_length_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_region_x (CleanQ_RB_write_head_length_y f rb) b = CleanQ_RB_read_tail_region_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_region_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_read_tail_region_x_write_valid_offset_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_region_x (CleanQ_RB_write_head_valid_offset_y f rb) b = CleanQ_RB_read_tail_region_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_region_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_read_tail_region_x_write_valid_length_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_region_x (CleanQ_RB_write_head_valid_length_y f rb) b = CleanQ_RB_read_tail_region_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_region_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_read_tail_region_x_write_y[simp] = 
     CleanQ_RB_read_tail_region_x_write_flags_y
     CleanQ_RB_read_tail_region_x_write_region_y
     CleanQ_RB_read_tail_region_x_write_offset_y
     CleanQ_RB_read_tail_region_x_write_length_y
     CleanQ_RB_read_tail_region_x_write_valid_offset_y
     CleanQ_RB_read_tail_region_x_write_valid_length_y

paragraph \<open>Read Y, Enq X\<close>

lemma CleanQ_RB_read_tail_region_y_enq_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_region_y (CleanQ_RB_enq_x b2 rb) b = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_enq_x)

lemma CleanQ_RB_read_tail_offset_y_enq_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_offset_y (CleanQ_RB_enq_x b2 rb) b = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_enq_x)

lemma CleanQ_RB_read_tail_length_y_enq_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_length_y (CleanQ_RB_enq_x b2 rb) b = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_enq_x)

lemma CleanQ_RB_read_tail_flags_y_enq_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_flags_y (CleanQ_RB_enq_x b2 rb) b = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_enq_x)

lemma CleanQ_RB_read_tail_valid_offset_y_enq_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y (CleanQ_RB_enq_x b2 rb) b = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_enq_x)

lemma CleanQ_RB_read_tail_valid_length_y_enq_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y (CleanQ_RB_enq_x b2 rb) b = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_enq_x)

lemmas CleanQ_RB_read_tail__y_enq_x_simps[simp] = 
     CleanQ_RB_read_tail_region_y_enq_x
     CleanQ_RB_read_tail_offset_y_enq_x
     CleanQ_RB_read_tail_length_y_enq_x
     CleanQ_RB_read_tail_flags_y_enq_x
     CleanQ_RB_read_tail_valid_offset_y_enq_x
     CleanQ_RB_read_tail_valid_length_y_enq_x

paragraph \<open>Read X, Enq Y\<close>

lemma CleanQ_RB_read_tail_region_x_enq_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_region_x (CleanQ_RB_enq_y b2 rb) b = CleanQ_RB_read_tail_region_x rb b"
  by (metis CleanQ_RB_read_tail_region_x_def CleanQ_RB_read_tail_x_def CleanQ_RB_read_tail_x_enq_y)

lemma CleanQ_RB_read_tail_offset_x_enq_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_offset_x (CleanQ_RB_enq_y b2 rb) b = CleanQ_RB_read_tail_offset_x rb b"
  by (metis CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_x_def CleanQ_RB_read_tail_x_enq_y)

lemma CleanQ_RB_read_tail_length_x_enq_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_length_x (CleanQ_RB_enq_y b2 rb) b = CleanQ_RB_read_tail_length_x rb b"
  by (metis CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_x_def CleanQ_RB_read_tail_x_enq_y)

lemma CleanQ_RB_read_tail_flags_x_enq_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_flags_x (CleanQ_RB_enq_y b2 rb) b = CleanQ_RB_read_tail_flags_x rb b"
  by (metis CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_x_def CleanQ_RB_read_tail_x_enq_y)

lemma CleanQ_RB_read_tail_valid_offset_x_enq_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x (CleanQ_RB_enq_y b2 rb) b = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_x_def CleanQ_RB_read_tail_x_def CleanQ_RB_read_tail_x_enq_y)

lemma CleanQ_RB_read_tail_valid_length_x_enq_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x (CleanQ_RB_enq_y b2 rb) b = CleanQ_RB_read_tail_valid_length_x rb b"
  by (metis CleanQ_RB_read_tail_valid_length_x_def CleanQ_RB_read_tail_x_def CleanQ_RB_read_tail_x_enq_y)

lemmas CleanQ_RB_read_tail_x_enq_y_simps[simp] = 
     CleanQ_RB_read_tail_region_x_enq_y
     CleanQ_RB_read_tail_offset_x_enq_y
     CleanQ_RB_read_tail_length_x_enq_y
     CleanQ_RB_read_tail_flags_x_enq_y
     CleanQ_RB_read_tail_valid_offset_x_enq_y
     CleanQ_RB_read_tail_valid_length_x_enq_y


paragraph \<open>Read Y, Deq X\<close>

lemma CleanQ_RB_read_tail_region_y_deq_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_region_y (CleanQ_RB_deq_x  rb) b = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_deq_x)

lemma CleanQ_RB_read_tail_offset_y_deq_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_offset_y (CleanQ_RB_deq_x  rb) b = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_deq_x)

lemma CleanQ_RB_read_tail_length_y_deq_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_length_y (CleanQ_RB_deq_x rb) b = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_deq_x)

lemma CleanQ_RB_read_tail_flags_y_deq_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_flags_y (CleanQ_RB_deq_x  rb) b = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_deq_x)

lemma CleanQ_RB_read_tail_valid_offset_y_deq_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y (CleanQ_RB_deq_x rb) b = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_deq_x)

lemma CleanQ_RB_read_tail_valid_length_y_deq_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y (CleanQ_RB_deq_x rb) b = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_deq_x)

lemmas CleanQ_RB_read_tail__y_deq_x_simps[simp] = 
     CleanQ_RB_read_tail_region_y_deq_x
     CleanQ_RB_read_tail_offset_y_deq_x
     CleanQ_RB_read_tail_length_y_deq_x
     CleanQ_RB_read_tail_flags_y_deq_x
     CleanQ_RB_read_tail_valid_offset_y_deq_x
     CleanQ_RB_read_tail_valid_length_y_deq_x


paragraph \<open>Read X, Deq Y\<close>

lemma CleanQ_RB_read_tail_region_x_deq_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_region_x (CleanQ_RB_deq_y rb) b = CleanQ_RB_read_tail_region_x rb b"
  by (metis CleanQ_RB_read_tail_region_x_def CleanQ_RB_read_tail_x_def CleanQ_RB_read_tail_x_deq_y)

lemma CleanQ_RB_read_tail_offset_x_deq_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_offset_x (CleanQ_RB_deq_y rb) b = CleanQ_RB_read_tail_offset_x rb b"
  by (metis CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_x_def CleanQ_RB_read_tail_x_deq_y)

lemma CleanQ_RB_read_tail_length_x_deq_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_length_x (CleanQ_RB_deq_y rb) b = CleanQ_RB_read_tail_length_x rb b"
  by (metis CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_x_def CleanQ_RB_read_tail_x_deq_y)

lemma CleanQ_RB_read_tail_flags_x_deq_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_flags_x (CleanQ_RB_deq_y  rb) b = CleanQ_RB_read_tail_flags_x rb b"
  by (metis CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_x_def CleanQ_RB_read_tail_x_deq_y)

lemma CleanQ_RB_read_tail_valid_offset_x_deq_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x (CleanQ_RB_deq_y  rb) b = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_x_def CleanQ_RB_read_tail_x_def CleanQ_RB_read_tail_x_deq_y)

lemma CleanQ_RB_read_tail_valid_length_x_deq_y:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x (CleanQ_RB_deq_y  rb) b = CleanQ_RB_read_tail_valid_length_x rb b"
  by (metis CleanQ_RB_read_tail_valid_length_x_def CleanQ_RB_read_tail_x_def CleanQ_RB_read_tail_x_deq_y)

lemmas CleanQ_RB_read_tail_x_deq_y_simps[simp] = 
     CleanQ_RB_read_tail_region_x_deq_y
     CleanQ_RB_read_tail_offset_x_deq_y
     CleanQ_RB_read_tail_length_x_deq_y
     CleanQ_RB_read_tail_flags_x_deq_y
     CleanQ_RB_read_tail_valid_offset_x_deq_y
     CleanQ_RB_read_tail_valid_length_x_deq_y


paragraph \<open>Enq Possible/Deq Possible\<close>

lemma CleanQ_RB_deq_y_remains_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_deq_x rb) = CleanQ_RB_deq_y_possible rb"
  by (simp add: CleanQ_RB_deq_x_def CleanQ_RB_deq_y_possible_def prod.case_eq_if)

lemma CleanQ_RB_deq_x_remains_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_deq_y rb) = CleanQ_RB_deq_x_possible rb"
  by (simp add: CleanQ_RB_deq_y_def CleanQ_RB_deq_x_possible_def prod.case_eq_if)

lemma CleanQ_RB_enq_y_remains_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_enq_x b rb) = CleanQ_RB_enq_y_possible rb"
  by (simp add: CleanQ_RB_enq_x_def CleanQ_RB_enq_y_possible_def prod.case_eq_if)

lemma CleanQ_RB_enq_x_remains_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_enq_y b rb) = CleanQ_RB_enq_x_possible rb"
  by (simp add: CleanQ_RB_enq_y_def CleanQ_RB_enq_x_possible_def prod.case_eq_if)

lemmas CleanQ_RB_enq_deq_remains_possible[simp] = 
    CleanQ_RB_deq_y_remains_possible 
    CleanQ_RB_deq_x_remains_possible
    CleanQ_RB_enq_y_remains_possible
    CleanQ_RB_enq_x_remains_possible

paragraph \<open>Write Y Enq Remains Possible Y\<close>

lemma CleanQ_RB_write_head_length_y_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_length_y x rb) = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_can_enq_y CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_offset_y_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_offset_y x rb) = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_y_can_enq_y CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_region_y_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_region_y x rb) = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_region_y_def CleanQ_RB_write_head_y_can_enq_y CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_flags_y_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_flags_y x rb) = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_flags_y_def CleanQ_RB_write_head_y_can_enq_y CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_length_y_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_valid_length_y x rb) = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_valid_length_y_def CleanQ_RB_write_head_y_can_enq_y CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_valid_offset_y x rb) = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_valid_offset_y_def CleanQ_RB_write_head_y_can_enq_y CleanQ_RB_write_head_y_def)

lemmas CleanQ_RB_write_head_y_enq_y_possible[simp] = 
   CleanQ_RB_write_head_length_y_enq_y_possible
   CleanQ_RB_write_head_offset_y_enq_y_possible
   CleanQ_RB_write_head_region_y_enq_y_possible
   CleanQ_RB_write_head_flags_y_enq_y_possible
   CleanQ_RB_write_head_valid_length_y_enq_y_possible
   CleanQ_RB_write_head_valid_offset_y_enq_y_possible


paragraph \<open>Write Y Enq Remains Possible X\<close>

lemma CleanQ_RB_write_head_length_y_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_length_y x rb) = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_can_enq_x CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_offset_y_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_offset_y x rb) = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_y_can_enq_x CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_region_y_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_region_y x rb) = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_region_y_def CleanQ_RB_write_head_y_can_enq_x CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_flags_y_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_flags_y x rb) = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_flags_y_def CleanQ_RB_write_head_y_can_enq_x CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_length_y_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_valid_length_y x rb) = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_valid_length_y_def CleanQ_RB_write_head_y_can_enq_x CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_valid_offset_y x rb) = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_valid_offset_y_def CleanQ_RB_write_head_y_can_enq_x CleanQ_RB_write_head_y_def)

lemmas CleanQ_RB_write_head_y_enq_x_possible[simp] = 
   CleanQ_RB_write_head_length_y_enq_x_possible
   CleanQ_RB_write_head_offset_y_enq_x_possible
   CleanQ_RB_write_head_region_y_enq_x_possible
   CleanQ_RB_write_head_flags_y_enq_x_possible
   CleanQ_RB_write_head_valid_length_y_enq_x_possible
   CleanQ_RB_write_head_valid_offset_y_enq_x_possible

paragraph \<open>Write X Enq Remains Possible Y\<close>

lemma CleanQ_RB_write_head_length_x_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_length_x x rb) = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_can_enq_y CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_offset_x_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_offset_x x rb) = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_can_enq_y CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_region_x_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_region_x x rb) = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_can_enq_y CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_flags_x_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_flags_x x rb) = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_can_enq_y CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_length_x_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_valid_length_x x rb) = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_can_enq_y CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_valid_offset_x x rb) = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_can_enq_y CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_write_head_x_enq_y_possible[simp] = 
   CleanQ_RB_write_head_length_x_enq_y_possible
   CleanQ_RB_write_head_offset_x_enq_y_possible
   CleanQ_RB_write_head_region_x_enq_y_possible
   CleanQ_RB_write_head_flags_x_enq_y_possible
   CleanQ_RB_write_head_valid_length_x_enq_y_possible
   CleanQ_RB_write_head_valid_offset_x_enq_y_possible




paragraph \<open>Write X Deq Remains Possible X\<close>

lemma CleanQ_RB_write_head_length_x_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_length_x x rb) = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_can_deq_x CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_offset_x_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_offset_x x rb) = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_can_deq_x CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_region_x_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_region_x x rb) = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_can_deq_x CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_flags_x_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_flags_x x rb) = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_can_deq_x CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_length_x_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_valid_length_x x rb) = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_can_deq_x CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_valid_offset_x x rb) = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_can_deq_x CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_write_head_x_deq_x_possible[simp] = 
   CleanQ_RB_write_head_length_x_deq_x_possible
   CleanQ_RB_write_head_offset_x_deq_x_possible
   CleanQ_RB_write_head_region_x_deq_x_possible
   CleanQ_RB_write_head_flags_x_deq_x_possible
   CleanQ_RB_write_head_valid_length_x_deq_x_possible
   CleanQ_RB_write_head_valid_offset_x_deq_x_possible


paragraph \<open>Write Y Deq Remains Possible Y\<close>

lemma CleanQ_RB_write_head_length_y_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_length_y x rb) = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_can_deq_y CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_offset_y_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_offset_y x rb) = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_y_can_deq_y CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_region_y_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_region_y x rb) = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_region_y_def CleanQ_RB_write_head_y_can_deq_y CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_flags_y_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_flags_y x rb) = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_flags_y_def CleanQ_RB_write_head_y_can_deq_y CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_length_y_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_valid_length_y x rb) = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_valid_length_y_def CleanQ_RB_write_head_y_can_deq_y CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_valid_offset_y x rb) = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_valid_offset_y_def CleanQ_RB_write_head_y_can_deq_y CleanQ_RB_write_head_y_def)

lemmas CleanQ_RB_write_head_y_deq_y_possible[simp] = 
   CleanQ_RB_write_head_length_y_deq_y_possible
   CleanQ_RB_write_head_offset_y_deq_y_possible
   CleanQ_RB_write_head_region_y_deq_y_possible
   CleanQ_RB_write_head_flags_y_deq_y_possible
   CleanQ_RB_write_head_valid_length_y_deq_y_possible
   CleanQ_RB_write_head_valid_offset_y_deq_y_possible


paragraph \<open>Write Y Deq Remains Possible X\<close>

lemma CleanQ_RB_write_head_length_y_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_length_y x rb) = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_can_deq_x CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_offset_y_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_offset_y x rb) = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_y_can_deq_x CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_region_y_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_region_y x rb) = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_region_y_def CleanQ_RB_write_head_y_can_deq_x CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_flags_y_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_flags_y x rb) = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_flags_y_def CleanQ_RB_write_head_y_can_deq_x CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_length_y_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_valid_length_y x rb) = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_valid_length_y_def CleanQ_RB_write_head_y_can_deq_x CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_valid_offset_y x rb) = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_valid_offset_y_def CleanQ_RB_write_head_y_can_deq_x CleanQ_RB_write_head_y_def)

lemmas CleanQ_RB_write_head_y_deq_x_possible[simp] = 
   CleanQ_RB_write_head_length_y_deq_x_possible
   CleanQ_RB_write_head_offset_y_deq_x_possible
   CleanQ_RB_write_head_region_y_deq_x_possible
   CleanQ_RB_write_head_flags_y_deq_x_possible
   CleanQ_RB_write_head_valid_length_y_deq_x_possible
   CleanQ_RB_write_head_valid_offset_y_deq_x_possible

paragraph \<open>Write X Deq Remains Possible Y\<close>

lemma CleanQ_RB_write_head_length_x_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_length_x x rb) = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_can_deq_y CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_offset_x_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_offset_x x rb) = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_can_deq_y CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_region_x_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_region_x x rb) = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_can_deq_y CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_flags_x_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_flags_x x rb) = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_can_deq_y CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_length_x_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_valid_length_x x rb) = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_can_deq_y CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_valid_offset_x x rb) = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_can_deq_y CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_write_head_x_deq_y_possible[simp] = 
   CleanQ_RB_write_head_length_x_deq_y_possible
   CleanQ_RB_write_head_offset_x_deq_y_possible
   CleanQ_RB_write_head_region_x_deq_y_possible
   CleanQ_RB_write_head_flags_x_deq_y_possible
   CleanQ_RB_write_head_valid_length_x_deq_y_possible
   CleanQ_RB_write_head_valid_offset_x_deq_y_possible




paragraph \<open>Write X buf in SX\<close>

lemma CleanQ_RB_write_head_offset_x_SX_unchanged:
  "rSX (CleanQ_RB_write_head_offset_x v rb) = rSX rb"
  by (simp add: CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_length_x_SX_unchanged:
  "rSX (CleanQ_RB_write_head_length_x v rb) = rSX rb"
  by (simp add: CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_region_x_SX_unchanged:
  "rSX (CleanQ_RB_write_head_region_x v rb) = rSX rb"
  by (simp add: CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_flags_x_SX_unchanged:
  "rSX (CleanQ_RB_write_head_flags_x v rb) = rSX rb"
  by (simp add: CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_SX_unchanged:
  "rSX (CleanQ_RB_write_head_valid_offset_x v rb) = rSX rb"
  by (simp add: CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_SX_unchanged:
  "rSX (CleanQ_RB_write_head_valid_length_x v rb) = rSX rb"
  by (simp add: CleanQ_RB_write_head_valid_length_x_def)


lemmas CleanQ_RB_write_head_x_SX_unchanged[simp] = 
  CleanQ_RB_write_head_offset_x_SX_unchanged
  CleanQ_RB_write_head_length_x_SX_unchanged
  CleanQ_RB_write_head_region_x_SX_unchanged
  CleanQ_RB_write_head_flags_x_SX_unchanged
  CleanQ_RB_write_head_valid_offset_x_SX_unchanged
  CleanQ_RB_write_head_valid_length_x_SX_unchanged


paragraph \<open>Write Y buf in SX\<close>


lemma CleanQ_RB_write_head_offset_y_SX_unchanged:
  "rSX (CleanQ_RB_write_head_offset_y v rb) = rSX rb"
  by (simp add: CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_length_y_SX_unchanged:
  "rSX (CleanQ_RB_write_head_length_y v rb) = rSX rb"
  by (simp add: CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_region_y_SX_unchanged:
  "rSX (CleanQ_RB_write_head_region_y v rb) = rSX rb"
  by (simp add: CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_flags_y_SX_unchanged:
  "rSX (CleanQ_RB_write_head_flags_y v rb) = rSX rb"
  by (simp add: CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_SX_unchanged:
  "rSX (CleanQ_RB_write_head_valid_offset_y v rb) = rSX rb"
  by (simp add: CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_SX_unchanged:
  "rSX (CleanQ_RB_write_head_valid_length_y v rb) = rSX rb"
  by (simp add: CleanQ_RB_write_head_valid_length_y_def)


lemmas CleanQ_RB_write_head_y_SX_unchanged[simp] = 
  CleanQ_RB_write_head_offset_y_SX_unchanged
  CleanQ_RB_write_head_length_y_SX_unchanged
  CleanQ_RB_write_head_region_y_SX_unchanged
  CleanQ_RB_write_head_flags_y_SX_unchanged
  CleanQ_RB_write_head_valid_offset_y_SX_unchanged
  CleanQ_RB_write_head_valid_length_y_SX_unchanged




paragraph \<open>Write X buf in SY\<close>


lemma CleanQ_RB_write_head_offset_x_SY_unchanged:
  "rSY (CleanQ_RB_write_head_offset_x v rb) = rSY rb"
  by (simp add: CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_length_x_SY_unchanged:
  "rSY (CleanQ_RB_write_head_length_x v rb) = rSY rb"
  by (simp add: CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_region_x_SY_unchanged:
  "rSY (CleanQ_RB_write_head_region_x v rb) = rSY rb"
  by (simp add: CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_flags_x_SY_unchanged:
  "rSY (CleanQ_RB_write_head_flags_x v rb) = rSY rb"
  by (simp add: CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_SY_unchanged:
  "rSY (CleanQ_RB_write_head_valid_offset_x v rb) = rSY rb"
  by (simp add: CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_SY_unchanged:
  "rSY (CleanQ_RB_write_head_valid_length_x v rb) = rSY rb"
  by (simp add: CleanQ_RB_write_head_valid_length_x_def)


lemmas CleanQ_RB_write_head_x_SY_unchanged[simp] = 
  CleanQ_RB_write_head_offset_x_SY_unchanged
  CleanQ_RB_write_head_length_x_SY_unchanged
  CleanQ_RB_write_head_region_x_SY_unchanged
  CleanQ_RB_write_head_flags_x_SY_unchanged
  CleanQ_RB_write_head_valid_offset_x_SY_unchanged
  CleanQ_RB_write_head_valid_length_x_SY_unchanged


paragraph \<open>Write Y buf in SY\<close>


lemma CleanQ_RB_write_head_offset_y_SY_unchanged:
  "rSY (CleanQ_RB_write_head_offset_y v rb) = rSY rb"
  by (simp add: CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_length_y_SY_unchanged:
  "rSY (CleanQ_RB_write_head_length_y v rb) = rSY rb"
  by (simp add: CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_region_y_SY_unchanged:
  "rSY (CleanQ_RB_write_head_region_y v rb) = rSY rb"
  by (simp add: CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_flags_y_SY_unchanged:
  "rSY (CleanQ_RB_write_head_flags_y v rb) = rSY rb"
  by (simp add: CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_SY_unchanged:
  "rSY (CleanQ_RB_write_head_valid_offset_y v rb) = rSY rb"
  by (simp add: CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_SY_unchanged:
  "rSY (CleanQ_RB_write_head_valid_length_y v rb) = rSY rb"
  by (simp add: CleanQ_RB_write_head_valid_length_y_def)


lemmas CleanQ_RB_write_head_y_SY_unchanged[simp] = 
  CleanQ_RB_write_head_offset_y_SY_unchanged
  CleanQ_RB_write_head_length_y_SY_unchanged
  CleanQ_RB_write_head_region_y_SY_unchanged
  CleanQ_RB_write_head_flags_y_SY_unchanged
  CleanQ_RB_write_head_valid_offset_y_SY_unchanged
  CleanQ_RB_write_head_valid_length_y_SY_unchanged


paragraph \<open>Write X not none\<close>

lemma CleanQ_RB_write_head_flags_x_not_none:
  "\<not>CleanQ_RB_head_none_x (CleanQ_RB_write_head_flags_x v rb)"
  by (metis CleanQ_RB_head_write_x_not_none CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_flags_x_not_none2:
  "CleanQ_RB_head_none_x (CleanQ_RB_write_head_flags_y v rb) = CleanQ_RB_head_none_x rb "
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_offset_x_not_none:
  "\<not>CleanQ_RB_head_none_x (CleanQ_RB_write_head_offset_x v rb)"
  by (metis CleanQ_RB_head_write_x_not_none CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_offset_x_not_none2:
  "CleanQ_RB_head_none_x (CleanQ_RB_write_head_offset_y v rb) = CleanQ_RB_head_none_x rb "
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_length_x_not_none:
  "\<not>CleanQ_RB_head_none_x (CleanQ_RB_write_head_length_x v rb)"
  by (metis CleanQ_RB_head_write_x_not_none CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_length_x_not_none2:
  "CleanQ_RB_head_none_x (CleanQ_RB_write_head_length_y v rb) = CleanQ_RB_head_none_x rb "
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_region_x_not_none:
  "\<not>CleanQ_RB_head_none_x (CleanQ_RB_write_head_region_x v rb)"
  by (metis CleanQ_RB_head_write_x_not_none CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_region_x_not_none2:
  "CleanQ_RB_head_none_x (CleanQ_RB_write_head_region_y v rb) = CleanQ_RB_head_none_x rb "
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_valid_offset_x_not_none:
  "\<not>CleanQ_RB_head_none_x (CleanQ_RB_write_head_valid_offset_x v rb)"
  by (metis CleanQ_RB_head_write_x_not_none CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_not_none2:
  "CleanQ_RB_head_none_x (CleanQ_RB_write_head_valid_offset_y v rb) = CleanQ_RB_head_none_x rb "
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_x_not_none:
  "\<not>CleanQ_RB_head_none_x (CleanQ_RB_write_head_valid_length_x v rb)"
  by (metis CleanQ_RB_head_write_x_not_none CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_length_x_not_none2:
  "CleanQ_RB_head_none_x (CleanQ_RB_write_head_valid_length_y v rb) = CleanQ_RB_head_none_x rb "
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_x_not_none[simp] = 
     CleanQ_RB_write_head_flags_x_not_none
     CleanQ_RB_write_head_offset_x_not_none
     CleanQ_RB_write_head_length_x_not_none
     CleanQ_RB_write_head_region_x_not_none
     CleanQ_RB_write_head_valid_offset_x_not_none
     CleanQ_RB_write_head_valid_length_x_not_none
     CleanQ_RB_write_head_flags_x_not_none2
     CleanQ_RB_write_head_offset_x_not_none2
     CleanQ_RB_write_head_length_x_not_none2
     CleanQ_RB_write_head_region_x_not_none2
     CleanQ_RB_write_head_valid_offset_x_not_none2
     CleanQ_RB_write_head_valid_length_x_not_none2

paragraph \<open>Write Y not none\<close>

lemma CleanQ_RB_write_head_flags_y_not_none:
  "\<not>CleanQ_RB_head_none_y (CleanQ_RB_write_head_flags_y v rb)"
  by (metis CleanQ_RB_head_write_y_not_none CleanQ_RB_write_head_flags_y_def CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_flags_y_not_none2:
  "CleanQ_RB_head_none_y (CleanQ_RB_write_head_flags_x v rb) = CleanQ_RB_head_none_y rb "
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_offset_y_not_none:
  "\<not>CleanQ_RB_head_none_y (CleanQ_RB_write_head_offset_y v rb)"
  by (metis CleanQ_RB_head_write_y_not_none CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_offset_y_not_none2:
  "CleanQ_RB_head_none_y (CleanQ_RB_write_head_offset_x v rb) = CleanQ_RB_head_none_y rb "
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_length_y_not_none:
  "\<not>CleanQ_RB_head_none_y (CleanQ_RB_write_head_length_y v rb)"
  by (metis CleanQ_RB_head_write_y_not_none CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_length_y_not_none2:
  "CleanQ_RB_head_none_y (CleanQ_RB_write_head_length_x v rb) = CleanQ_RB_head_none_y rb "
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_region_y_not_none:
  "\<not>CleanQ_RB_head_none_y (CleanQ_RB_write_head_region_y v rb)"
  by (metis CleanQ_RB_head_write_y_not_none CleanQ_RB_write_head_region_y_def CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_region_y_not_none2:
  "CleanQ_RB_head_none_y (CleanQ_RB_write_head_region_x v rb) = CleanQ_RB_head_none_y rb "
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_valid_offset_y_not_none:
  "\<not>CleanQ_RB_head_none_y (CleanQ_RB_write_head_valid_offset_y v rb)"
  by (metis CleanQ_RB_head_write_y_not_none CleanQ_RB_write_head_valid_offset_y_def CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_not_none2:
  "CleanQ_RB_head_none_y (CleanQ_RB_write_head_valid_offset_x v rb) = CleanQ_RB_head_none_y rb "
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_y_not_none:
  "\<not>CleanQ_RB_head_none_y (CleanQ_RB_write_head_valid_length_y v rb)"
  by (metis CleanQ_RB_head_write_y_not_none CleanQ_RB_write_head_valid_length_y_def CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_length_y_not_none2:
  "CleanQ_RB_head_none_y (CleanQ_RB_write_head_valid_length_x v rb) = CleanQ_RB_head_none_y rb "
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_valid_length_x_def)

lemmas CleanQ_RB_write_head_y_not_none[simp] = 
     CleanQ_RB_write_head_flags_y_not_none
     CleanQ_RB_write_head_offset_y_not_none
     CleanQ_RB_write_head_length_y_not_none
     CleanQ_RB_write_head_region_y_not_none
     CleanQ_RB_write_head_valid_offset_y_not_none
     CleanQ_RB_write_head_valid_length_y_not_none
     CleanQ_RB_write_head_flags_y_not_none2
     CleanQ_RB_write_head_offset_y_not_none2
     CleanQ_RB_write_head_length_y_not_none2
     CleanQ_RB_write_head_region_y_not_none2
     CleanQ_RB_write_head_valid_offset_y_not_none2
     CleanQ_RB_write_head_valid_length_y_not_none2


(* those two won't work with all fields... *)

(*
lemma CleanQ_RB_write_head_offset_x_read [simp]:
  assumes "length (CleanQ_RB_read_head_x rb) = length buf" and
          "region (CleanQ_RB_read_head_x rb) = region buf"
        shows "buf = CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_x (offset buf) rb)"
proof -
  have f1: "CleanQ_Buffer.length (rb_read_head (rTXY rb)) = CleanQ_Buffer.length buf"
    by (metis CleanQ_RB_read_head_x_def assms(1))
  have "region (rb_read_head (rTXY rb)) = region buf"
    by (metis (no_types) CleanQ_RB_read_head_x_def assms(2))
  then show ?thesis
    using f1 by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_x_def)
qed
  

lemma CleanQ_RB_write_head_offset_y_read [simp]:
  assumes "length (CleanQ_RB_read_head_y rb) = length buf" and
          "region (CleanQ_RB_read_head_y rb) = region buf"
  shows "buf = CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_y (offset buf) rb)"
proof -
  have f1: "CleanQ_Buffer.length (rb_read_head (rTYX rb)) = CleanQ_Buffer.length buf"
    by (metis CleanQ_RB_read_head_y_def assms(1))
  have "region (rb_read_head (rTYX rb)) = region buf"
    by (metis (no_types) CleanQ_RB_read_head_y_def assms(2))
  then show ?thesis
    using f1 by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_y_def)
qed
  
  
lemma CleanQ_RB_write_head_length_x_read [simp]:
  assumes "offset (CleanQ_RB_read_head_x rb) = offset buf" and
          "region (CleanQ_RB_read_head_x rb) = region buf"
  shows "buf = CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_x (length buf) rb)"
proof -
  have f1: "offset (rb_read_head (rTXY rb)) = offset buf"
    by (metis (no_types) CleanQ_RB_read_head_x_def assms(1))
  have "region (rb_read_head (rTXY rb)) = region buf"
    by (metis CleanQ_RB_read_head_x_def assms(2))
  then show ?thesis
    using f1 by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_x_def)
qed
  
lemma CleanQ_RB_write_head_length_y_read [simp]:
  assumes "offset (CleanQ_RB_read_head_y rb) = offset buf"
          "region (CleanQ_RB_read_head_y rb) = region buf"
  shows "buf = CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_y (length buf) rb)"
proof -
  have f1: "offset (rb_read_head (rTYX rb)) = offset buf"
    by (metis CleanQ_RB_read_head_y_def assms(1))
  have "region (rb_read_head (rTYX rb)) = region buf"
    by (metis (no_types) CleanQ_RB_read_head_y_def assms(2))
  then show ?thesis
    using f1 by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_y_def)
qed

lemma CleanQ_RB_write_head_region_x_read [simp]:
  assumes "offset (CleanQ_RB_read_head_x rb) = offset buf"
          "length (CleanQ_RB_read_head_x rb) = length buf"
  shows "buf = CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_x (region buf) rb)"
proof -
  have f1: "offset (rb_read_head (rTXY rb)) = offset buf"
    by (metis CleanQ_RB_read_head_x_def assms(1))
  have "CleanQ_Buffer.length (rb_read_head (rTXY rb)) = CleanQ_Buffer.length buf"
    by (metis (no_types) CleanQ_RB_read_head_x_def assms(2))
  then show ?thesis
    using f1 by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_x_def)
qed

lemma CleanQ_RB_write_head_region_y_read [simp]:
  assumes "offset (CleanQ_RB_read_head_y rb) = offset buf"
          "length (CleanQ_RB_read_head_y rb) = length buf"
  shows "buf = CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_y (region buf) rb)"
proof -
  have f1: "CleanQ_Buffer.length (rb_read_head (rTYX rb)) = CleanQ_Buffer.length buf"
    by (metis (no_types) CleanQ_RB_read_head_y_def assms(2))
  have "offset (rb_read_head (rTYX rb)) = offset buf"
    by (metis (no_types) CleanQ_RB_read_head_y_def assms(1))
  then show ?thesis
    using f1 by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_y_def)
qed

*)


paragraph \<open>Unsorted for now !\<close>



lemma CleanQ_RB_write_head_length_y_rest_unchanged [simp]:
  assumes "offset (CleanQ_RB_read_head_y (CRB x)) = offset b2" and
          "offset (CleanQ_RB_read_head_x (CRB x)) = offset b" and
          "region (CleanQ_RB_read_head_y (CRB x)) = region b2" and
          "region (CleanQ_RB_read_head_x (CRB x)) = region b"
  shows "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_y (CleanQ_Buffer.length b2) (CRB x))) = offset b \<and>
         region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_y (CleanQ_Buffer.length b2) (CRB x))) = region b"
  by (metis CleanQ_RB_read_head_x_write_y CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_def assms(2) assms(4))
  

lemma CleanQ_RB_write_head_length_x_rest_unchanged [simp]:
  assumes "offset (CleanQ_RB_read_head_x (CRB x)) = offset b2" and
          "offset (CleanQ_RB_read_head_y (CRB x)) = offset b" and
          "region (CleanQ_RB_read_head_x (CRB x)) = region b2" and
          "region (CleanQ_RB_read_head_y (CRB x)) = region b"
  shows "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_x (CleanQ_Buffer.length b2) (CRB x))) = offset b \<and>
         region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_x (CleanQ_Buffer.length b2) (CRB x))) = region b"
  by (metis CleanQ_RB_read_head_y_write_x CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_def assms(2) assms(4))

lemma CleanQ_RB_write_head_offset_y_rest_unchanged [simp]:
  assumes "length (CleanQ_RB_read_head_y (CRB x)) = length b2" and
          "length (CleanQ_RB_read_head_x (CRB x)) = length b" and
          "region (CleanQ_RB_read_head_y (CRB x)) = region b2" and
          "region (CleanQ_RB_read_head_x (CRB x)) = region b"
  shows "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_y (CleanQ_Buffer.offset b2) (CRB x))) = length b \<and>
         region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_y (CleanQ_Buffer.offset b2) (CRB x))) = region b"
  by (metis (no_types) CleanQ_RB_read_head_x_write_y CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_y_def assms(2) assms(4))
  
lemma CleanQ_RB_write_head_offset_x_rest_unchanged [simp]:
  assumes "length (CleanQ_RB_read_head_x (CRB x)) = length b2" and
          "length (CleanQ_RB_read_head_y (CRB x)) = length b" and
          "region (CleanQ_RB_read_head_x (CRB x)) = region b2" and
          "region (CleanQ_RB_read_head_y (CRB x)) = region b"
  shows "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_x (CleanQ_Buffer.offset b2) (CRB x))) = length b \<and>
         region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_x (CleanQ_Buffer.offset b2) (CRB x))) = region b"
  by (metis (no_types) CleanQ_RB_read_head_y_write_x CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_def assms(2) assms(4))
  
lemma CleanQ_RB_write_head_region_y_rest_unchanged [simp]:
  assumes "length (CleanQ_RB_read_head_y (CRB x)) = length b2" and
          "length (CleanQ_RB_read_head_x (CRB x)) = length b" and
          "offset (CleanQ_RB_read_head_y (CRB x)) = offset b2" and
          "offset (CleanQ_RB_read_head_x (CRB x)) = offset b"
  shows "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_y (CleanQ_Buffer.region b2) (CRB x))) = length b \<and>
         offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_y (CleanQ_Buffer.region b2) (CRB x))) = offset b"
  by (metis CleanQ_RB_read_head_x_write_y CleanQ_RB_write_head_region_y_def CleanQ_RB_write_head_y_def assms(2) assms(4))


lemma CleanQ_RB_write_head_region_x_rest_unchanged [simp]:
  assumes "length (CleanQ_RB_read_head_x (CRB x)) = length b2" and
          "length (CleanQ_RB_read_head_y (CRB x)) = length b" and
          "offset (CleanQ_RB_read_head_x (CRB x)) = offset b2" and
          "offset (CleanQ_RB_read_head_y (CRB x)) = offset b"
  shows "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_x (CleanQ_Buffer.region b2) (CRB x))) = length b \<and>
         offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_x (CleanQ_Buffer.region b2) (CRB x))) = offset b"
  by (metis CleanQ_RB_read_head_y_write_x CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_def assms(2) assms(4))

lemma CleanQ_RB_deq_x_invariant [simp]:
  assumes inv: "CleanQ_RB_Invariants (uni x) (CRB x)" and
         can: " CleanQ_RB_deq_x_possible (CRB x)"
  shows "CleanQ_RB_Invariants (uni x) (CleanQ_RB_deq_x (CRB x))"
  using CleanQ_RB_deq_x_all_inv can inv by blast

lemma CleanQ_RB_deq_y_invariant [simp]:
  assumes inv: "CleanQ_RB_Invariants (uni x) (CRB x)" and
         can: " CleanQ_RB_deq_y_possible (CRB x)"
  shows "CleanQ_RB_Invariants (uni x) (CleanQ_RB_deq_y (CRB x))"
  using CleanQ_RB_deq_y_all_inv can inv by blast

lemma CleanQ_RB_enq_x_invariant [simp]:
  assumes inv: "CleanQ_RB_Invariants (uni x) (CRB x)" and
          can: " CleanQ_RB_enq_x_possible (CRB x)" and
          b: "b \<in> rSX (CRB x)"
  shows "CleanQ_RB_Invariants (uni x) (CleanQ_RB_enq_x b (CRB x))"
  by (meson CleanQ_RB_enq_x_inv_all b can inv)

lemma CleanQ_RB_enq_y_invariant [simp]:
  assumes inv: "CleanQ_RB_Invariants (uni x) (CRB x)" and
          can: " CleanQ_RB_enq_y_possible (CRB x)" and
          b: "b \<in> rSY (CRB x)"
  shows "CleanQ_RB_Invariants (uni x) (CleanQ_RB_enq_y b (CRB x))"
  by (meson CleanQ_RB_enq_y_inv_all b can inv)


lemma CleanQ_RB_enq_x_possible_enq_y_read [simp]:
  assumes "CleanQ_RB_enq_x_possible (CRB x)" and
          "CleanQ_RB_enq_y_possible (CRB x)" 
  shows "CleanQ_RB_enq_x_possible (CleanQ_RB_enq_y (CleanQ_RB_read_head_y (CRB x)) (CRB x))"
  by (metis CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(2) 
      CleanQ_RB_State.update_convs(4) CleanQ_RB_enq_x_possible_def CleanQ_RB_enq_y_def assms(1))

lemma CleanQ_RB_enq_y_possible_enq_x_read [simp]:
  assumes "CleanQ_RB_enq_x_possible (CRB x)" and
          "CleanQ_RB_enq_y_possible (CRB x)" 
 shows "CleanQ_RB_enq_y_possible (CleanQ_RB_enq_x (CleanQ_RB_read_head_x (CRB x)) (CRB x))"
  by (metis CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(1) 
      CleanQ_RB_State.update_convs(3) CleanQ_RB_enq_x_def CleanQ_RB_enq_y_possible_def assms(2))

(* TODO, seems like these four can not be matched in the proof somehow  ....*) 
lemma CleanQ_RB_head_not_none_write_head_length_y [simp]:
  shows "CleanQ_RB_head_none_y (CleanQ_RB_write_head_length_y (CleanQ_Buffer.length b2) (CRB x)) \<Longrightarrow> False"
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_head_not_none_write_head_length_x [simp]:
  shows "CleanQ_RB_head_none_x (CleanQ_RB_write_head_length_x (CleanQ_Buffer.length b2) (CRB x)) \<Longrightarrow> False"
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_head_not_none_write_head_offset_y [simp]:
  shows "CleanQ_RB_head_none_y (CleanQ_RB_write_head_offset_y (CleanQ_Buffer.offset b2) (CRB x)) \<Longrightarrow> False"
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_head_not_none_write_head_offset_x [simp]:
  shows "CleanQ_RB_head_none_x (CleanQ_RB_write_head_offset_x (CleanQ_Buffer.offset b2) (CRB x)) \<Longrightarrow> False"
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_offset_x_def)

(*
lemma CleanQ_RB_head_not_none_write_head_region_y [simp]:
  shows "CleanQ_RB_head_none_y (CleanQ_RB_write_head_region_y (CleanQ_Buffer.region b2) (CRB x)) \<Longrightarrow> False"
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_head_not_none_write_head_region_x [simp]:
  shows "CleanQ_RB_head_none_x (CleanQ_RB_write_head_region_x (CleanQ_Buffer.region b2) (CRB x)) \<Longrightarrow> False"
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_region_x_def)
*) 


lemma CleanQ_RB_read_tail_offset_x_mult :
  shows "CleanQ_RB_read_tail_offset_x (CRB x) (CleanQ_RB_read_tail_offset_x (CRB x) (buf_x x)) = CleanQ_RB_read_tail_offset_x (CRB x) (buf_x x)"
  by (simp add: CleanQ_RB_read_tail_offset_x_def)

lemma CleanQ_RB_read_tail_offset_y_mult :
  shows "CleanQ_RB_read_tail_offset_y (CRB x) (CleanQ_RB_read_tail_offset_y (CRB x) (buf_y x)) = CleanQ_RB_read_tail_offset_y (CRB x) (buf_y x)"
  by (simp add: CleanQ_RB_read_tail_offset_y_def)

lemma CleanQ_RB_read_tail_length_x_mult :
  shows "CleanQ_RB_read_tail_length_x (CRB x) (CleanQ_RB_read_tail_length_x (CRB x) (buf_x x)) = CleanQ_RB_read_tail_length_x (CRB x) (buf_x x)"
  by (simp add: CleanQ_RB_read_tail_length_x_def)

lemma CleanQ_RB_read_tail_length_y_mult :
  shows "CleanQ_RB_read_tail_length_y (CRB x) (CleanQ_RB_read_tail_length_y (CRB x) (buf_y x)) = CleanQ_RB_read_tail_length_y (CRB x) (buf_y x)"
  by (simp add: CleanQ_RB_read_tail_length_y_def)

lemma CleanQ_RB_read_tail_region_x_mult [simp]:
  shows " CleanQ_RB_read_tail_region_x (CRB x) (CleanQ_RB_read_tail_region_x (CRB x) (buf_x x)) = CleanQ_RB_read_tail_region_x (CRB x) (buf_x x)"
  by (simp add: CleanQ_RB_read_tail_region_x_def)

lemma CleanQ_RB_read_tail_region_y_mult [simp]:
  shows "CleanQ_RB_read_tail_region_y (CRB x) (CleanQ_RB_read_tail_region_y (CRB x) (buf_y x)) = CleanQ_RB_read_tail_region_y (CRB x) (buf_y x)"
  by (simp add: CleanQ_RB_read_tail_region_y_def)

lemma CleanQ_RB_read_tail_offset_y_region [simp]:
  assumes "buf_y x = CleanQ_RB_read_tail_region_y (CRB x) (buf_y x)"
  shows "CleanQ_RB_read_tail_region_y (CRB x) (CleanQ_RB_read_tail_offset_y (CRB x) (buf_y x)) = CleanQ_RB_read_tail_offset_y (CRB x) (buf_y x)"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(2) 
      CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_region_y_def assms)

lemma CleanQ_RB_read_tail_offset_y_length [simp]:
  assumes "buf_y x = CleanQ_RB_read_tail_length_y (CRB x) (buf_y x)"
  shows "CleanQ_RB_read_tail_length_y (CRB x) (CleanQ_RB_read_tail_offset_y (CRB x) (buf_y x)) = CleanQ_RB_read_tail_offset_y (CRB x) (buf_y x)"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(3) 
      CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_offset_y_def assms)

lemma CleanQ_RB_read_tail_length_y_offset [simp]:
  assumes "buf_y x = CleanQ_RB_read_tail_offset_y (CRB x) (buf_y x)"
  shows "CleanQ_RB_read_tail_offset_y (CRB x) (CleanQ_RB_read_tail_length_y (CRB x) (buf_y x)) = CleanQ_RB_read_tail_length_y (CRB x) (buf_y x)"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(3) 
      CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_offset_y_def assms)

lemma CleanQ_RB_read_tail_length_y_region [simp]:
  assumes "buf_y x = CleanQ_RB_read_tail_region_y (CRB x) (buf_y x)"
  shows "CleanQ_RB_read_tail_region_y (CRB x) (CleanQ_RB_read_tail_length_y (CRB x) (buf_y x)) = CleanQ_RB_read_tail_length_y (CRB x) (buf_y x)"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(3) 
      CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_region_y_def assms)
  
lemma CleanQ_RB_read_tail_region_y_offset [simp]:
  assumes "buf_y x = CleanQ_RB_read_tail_offset_y (CRB x) (buf_y x)"
  shows "CleanQ_RB_read_tail_offset_y (CRB x) (CleanQ_RB_read_tail_region_y (CRB x) (buf_y x)) = CleanQ_RB_read_tail_region_y (CRB x) (buf_y x)"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(2) 
      CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_region_y_def assms)
  
lemma CleanQ_RB_read_tail_region_y_length [simp]:
  assumes "buf_y x = CleanQ_RB_read_tail_length_y (CRB x) (buf_y x)"
  shows "CleanQ_RB_read_tail_length_y (CRB x) (CleanQ_RB_read_tail_region_y (CRB x) (buf_y x)) = CleanQ_RB_read_tail_region_y (CRB x) (buf_y x)"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(3) 
      CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_region_y_def assms)

lemma CleanQ_RB_read_tail_offset_x_region [simp]:
  assumes "buf_x x = CleanQ_RB_read_tail_region_x (CRB x) (buf_x x)"
  shows "CleanQ_RB_read_tail_region_x (CRB x) (CleanQ_RB_read_tail_offset_x (CRB x) (buf_x x)) = CleanQ_RB_read_tail_offset_x (CRB x) (buf_x x)"
  by (metis CleanQ_Buffer.cases_scheme CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(2) 
      CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_region_x_def assms)
 

lemma CleanQ_RB_read_tail_offset_x_length [simp]:
  assumes "buf_x x = CleanQ_RB_read_tail_length_x (CRB x) (buf_x x)"
  shows "CleanQ_RB_read_tail_length_x (CRB x) (CleanQ_RB_read_tail_offset_x (CRB x) (buf_x x)) = CleanQ_RB_read_tail_offset_x (CRB x) (buf_x x)"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(3) 
      CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_offset_x_def assms)
  
lemma CleanQ_RB_read_tail_length_x_offset [simp]:
  assumes "buf_x x = CleanQ_RB_read_tail_offset_x (CRB x) (buf_x x)"
  shows "CleanQ_RB_read_tail_offset_x (CRB x) (CleanQ_RB_read_tail_length_x (CRB x) (buf_x x)) = CleanQ_RB_read_tail_length_x (CRB x) (buf_x x)"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(3) 
      CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_offset_x_def assms)

lemma CleanQ_RB_read_tail_length_x_region [simp]:
  assumes "buf_x x = CleanQ_RB_read_tail_region_x (CRB x) (buf_x x)"
  shows "CleanQ_RB_read_tail_region_x (CRB x) (CleanQ_RB_read_tail_length_x (CRB x) (buf_x x)) = CleanQ_RB_read_tail_length_x (CRB x) (buf_x x)"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(3) 
      CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_region_x_def assms)
  
lemma CleanQ_RB_read_tail_region_x_offset [simp]:
  assumes "buf_x x = CleanQ_RB_read_tail_offset_x (CRB x) (buf_x x)"
  shows "CleanQ_RB_read_tail_offset_x (CRB x) (CleanQ_RB_read_tail_region_x (CRB x) (buf_x x)) = CleanQ_RB_read_tail_region_x (CRB x) (buf_x x)"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(2) 
      CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_region_x_def assms)
  
lemma CleanQ_RB_read_tail_region_x_length [simp]:
  assumes "buf_x x = CleanQ_RB_read_tail_length_x (CRB x) (buf_x x)"
  shows "CleanQ_RB_read_tail_length_x (CRB x) (CleanQ_RB_read_tail_region_x (CRB x) (buf_x x)) = CleanQ_RB_read_tail_region_x (CRB x) (buf_x x)"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(3) 
      CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_region_x_def assms)

lemma CleanQ_RB_can_enq_deq_x :
  assumes inv: "CleanQ_RB_Invariants K rb" and
          can: "CleanQ_RB_enq_x_possible rb"
  shows "CleanQ_RB_enq_x_possible (CleanQ_RB_deq_x rb)"
  unfolding CleanQ_RB_deq_x_def CleanQ_RB_enq_x_possible_def
  by (metis (mono_tags, lifting) CleanQ_RB_State.select_convs(3) CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(1) 
      CleanQ_RB_State.update_convs(4) CleanQ_RB_enq_x_possible_def can split_beta)

lemma CleanQ_RB_can_enq_deq_y :
  assumes inv: "CleanQ_RB_Invariants K rb" and
          can: "CleanQ_RB_enq_y_possible rb"
  shows "CleanQ_RB_enq_y_possible (CleanQ_RB_deq_y rb)"
  unfolding CleanQ_RB_deq_y_def CleanQ_RB_enq_y_possible_def
  by (metis CleanQ_RB_deq_y_def CleanQ_RB_deq_y_enq_y_possible CleanQ_RB_enq_y_possible_def can inv)

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

abbreviation "CleanQ_CRB_enq_mult_x b \<equiv> 
            \<lbrace> CleanQ_RB_Invariants \<acute>uni \<acute>CRB  \<rbrace>
            IF CleanQ_RB_enq_x_possible \<acute>CRB \<and> b \<in> rSX \<acute>CRB
            THEN
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_region_x (region b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region (CleanQ_RB_read_head_x \<acute>CRB) = region b 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_offset_x (offset b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region (CleanQ_RB_read_head_x \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_x \<acute>CRB) = offset b 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_length_x (length b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region (CleanQ_RB_read_head_x \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_x \<acute>CRB) = offset b \<and>
                length (CleanQ_RB_read_head_x \<acute>CRB) = length b
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_valid_offset_x (valid_offset b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region (CleanQ_RB_read_head_x \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_x \<acute>CRB) = offset b \<and>
                length (CleanQ_RB_read_head_x \<acute>CRB) = length b \<and>
                valid_offset (CleanQ_RB_read_head_x \<acute>CRB) = valid_offset b
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_valid_length_x (valid_length b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region (CleanQ_RB_read_head_x \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_x \<acute>CRB) = offset b \<and>
                length (CleanQ_RB_read_head_x \<acute>CRB) = length b \<and>
                valid_offset (CleanQ_RB_read_head_x \<acute>CRB) = valid_offset b \<and>
                valid_length (CleanQ_RB_read_head_x \<acute>CRB) = valid_length b
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_flags_x (flags b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_Q \<acute>uni \<acute>CRB b \<rbrace>
                \<acute>CRB := (CleanQ_RB_incr_head_x b \<acute>CRB)
            ELSE 
                \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
                SKIP
            FI"

abbreviation "CleanQ_CRB_enq_mult_y b \<equiv> 
            \<lbrace> CleanQ_RB_Invariants \<acute>uni \<acute>CRB  \<rbrace>
            IF CleanQ_RB_enq_y_possible \<acute>CRB \<and> b \<in> rSY \<acute>CRB
            THEN
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_region_y (region b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and> 
                region (CleanQ_RB_read_head_y \<acute>CRB) = region b 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_offset_y (offset b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and>  
                region (CleanQ_RB_read_head_y \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_y \<acute>CRB) = offset b 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_length_y (length b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and>  
                region (CleanQ_RB_read_head_y \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_y \<acute>CRB) = offset b \<and>
                length (CleanQ_RB_read_head_y \<acute>CRB) = length b 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_valid_offset_y (valid_offset b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and>  
                region (CleanQ_RB_read_head_y \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_y \<acute>CRB) = offset b \<and>
                length (CleanQ_RB_read_head_y \<acute>CRB) = length b \<and> 
                valid_offset (CleanQ_RB_read_head_y \<acute>CRB) = valid_offset b
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_valid_length_y (valid_length b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and>  
                region (CleanQ_RB_read_head_y \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_y \<acute>CRB) = offset b \<and>
                length (CleanQ_RB_read_head_y \<acute>CRB) = length b \<and> 
                valid_offset (CleanQ_RB_read_head_y \<acute>CRB) = valid_offset b \<and>
                valid_length (CleanQ_RB_read_head_y \<acute>CRB) = valid_length b
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_flags_y (flags b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_Q \<acute>uni \<acute>CRB b \<rbrace>
                \<acute>CRB := (CleanQ_RB_incr_head_y b \<acute>CRB)
            ELSE 
                \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
                SKIP
            FI"

abbreviation "CleanQ_CRB_deq_mult_x \<equiv> 
            \<lbrace> CleanQ_RB_Invariants \<acute>uni \<acute>CRB  \<rbrace>
            IF CleanQ_RB_deq_x_possible \<acute>CRB
            THEN
              \<lbrace> CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<rbrace>
                \<acute>buf_x := (CleanQ_RB_read_tail_region_x \<acute>CRB \<acute>buf_x) ;;
              \<lbrace> CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_region_x \<acute>CRB \<acute>buf_x
              \<rbrace>
                \<acute>buf_x := (CleanQ_RB_read_tail_offset_x \<acute>CRB \<acute>buf_x) ;;
              \<lbrace> CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_region_x \<acute>CRB \<acute>buf_x \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_offset_x \<acute>CRB \<acute>buf_x
              \<rbrace>
                \<acute>buf_x := (CleanQ_RB_read_tail_length_x \<acute>CRB \<acute>buf_x) ;;
              \<lbrace> CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_region_x \<acute>CRB \<acute>buf_x \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_offset_x \<acute>CRB \<acute>buf_x \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_length_x \<acute>CRB \<acute>buf_x 
              \<rbrace>
                \<acute>buf_x := (CleanQ_RB_read_tail_valid_offset_x \<acute>CRB \<acute>buf_x) ;;
              \<lbrace> CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_region_x \<acute>CRB \<acute>buf_x \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_offset_x \<acute>CRB \<acute>buf_x \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_length_x \<acute>CRB \<acute>buf_x \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_valid_offset_x \<acute>CRB \<acute>buf_x 
              \<rbrace>
                \<acute>buf_x := (CleanQ_RB_read_tail_valid_length_x \<acute>CRB \<acute>buf_x) ;;
              \<lbrace> CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_region_x \<acute>CRB \<acute>buf_x \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_offset_x \<acute>CRB \<acute>buf_x \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_length_x \<acute>CRB \<acute>buf_x \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_valid_offset_x \<acute>CRB \<acute>buf_x \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_valid_length_x \<acute>CRB \<acute>buf_x 
              \<rbrace>
                \<acute>buf_x := (CleanQ_RB_read_tail_flags_x \<acute>CRB \<acute>buf_x) ;;
              \<lbrace> CleanQ_RB_deq_x_Q \<acute>uni \<acute>CRB \<acute>buf_x\<rbrace>
                \<acute>CRB := (CleanQ_RB_incr_tail_x \<acute>buf_x \<acute>CRB)
            ELSE 
                \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
                SKIP
            FI"

abbreviation "CleanQ_CRB_deq_mult_y \<equiv> 
            \<lbrace> CleanQ_RB_Invariants \<acute>uni \<acute>CRB  \<rbrace>
            IF CleanQ_RB_deq_y_possible \<acute>CRB
            THEN
              \<lbrace> CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_y \<acute>CRB) \<rbrace>
                \<acute>buf_y := (CleanQ_RB_read_tail_region_y \<acute>CRB \<acute>buf_y) ;;
              \<lbrace> CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_y \<acute>CRB) \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_region_y \<acute>CRB \<acute>buf_y
              \<rbrace>
                \<acute>buf_y := (CleanQ_RB_read_tail_offset_y \<acute>CRB \<acute>buf_y) ;;
              \<lbrace> CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_y \<acute>CRB) \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_region_y \<acute>CRB \<acute>buf_y \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_offset_y \<acute>CRB \<acute>buf_y
              \<rbrace>
                \<acute>buf_y := (CleanQ_RB_read_tail_length_y \<acute>CRB \<acute>buf_y) ;;
              \<lbrace> CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_y \<acute>CRB) \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_region_y \<acute>CRB \<acute>buf_y \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_offset_y \<acute>CRB \<acute>buf_y \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_length_y \<acute>CRB \<acute>buf_y
              \<rbrace>
                \<acute>buf_y := (CleanQ_RB_read_tail_valid_offset_y \<acute>CRB \<acute>buf_y) ;;
              \<lbrace> CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_y \<acute>CRB) \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_region_y \<acute>CRB \<acute>buf_y \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_offset_y \<acute>CRB \<acute>buf_y \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_length_y \<acute>CRB \<acute>buf_y \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_valid_offset_y \<acute>CRB \<acute>buf_y
              \<rbrace>
                \<acute>buf_y := (CleanQ_RB_read_tail_valid_length_y \<acute>CRB \<acute>buf_y) ;;
              \<lbrace> CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_y \<acute>CRB) \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_region_y \<acute>CRB \<acute>buf_y \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_offset_y \<acute>CRB \<acute>buf_y \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_length_y \<acute>CRB \<acute>buf_y \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_valid_offset_y \<acute>CRB \<acute>buf_y \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_valid_length_y \<acute>CRB \<acute>buf_y
              \<rbrace>
                \<acute>buf_y := (CleanQ_RB_read_tail_flags_y \<acute>CRB \<acute>buf_y) ;;
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

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Concurrency proofs helper lemmas\<close>
(* ------------------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Concurrency proofs\<close>
(* ------------------------------------------------------------------------------------ *)

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
  by(oghoare, auto)

  
  
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
  by(oghoare, auto)

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
 by(oghoare, auto)
  
    
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
   by(oghoare, auto)
   
  
  
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
  by(oghoare, auto)


lemma " \<lbrace>CleanQ_RB_Invariants \<acute>uni \<acute>CRB\<rbrace> \<inter> \<lbrace>CleanQ_RB_enq_x_Q \<acute>uni \<acute>CRB b\<rbrace> \<subseteq> \<lbrace>CleanQ_RB_Invariants \<acute>uni (CleanQ_RB_incr_head_x b \<acute>CRB)\<rbrace>"
  by(auto)

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
  apply(oghoare) (* 106 subgoals *)
  using [[simp_trace]]
  apply simp
                         
                      apply(auto)[1]

                      apply(auto)[1]

using [[simp_trace=false]]
  by(auto)
    


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Helper lemmas specifically for last concurrency proof\<close>
(* ------------------------------------------------------------------------------------ *)

paragraph \<open>Write head behaves as expected for X\<close>

lemma CleanQ_RB_write_head_flags_x_eq:
  assumes reg: "region (CleanQ_RB_read_head_x (CRB x)) = region b2" and
          off: "offset (CleanQ_RB_read_head_x (CRB x)) = offset b2 " and
          len: "length (CleanQ_RB_read_head_x (CRB x)) = length b2" and
          vao: "valid_offset (CleanQ_RB_read_head_x (CRB x)) = valid_offset b2" and
          val:"valid_length (CleanQ_RB_read_head_x (CRB x)) = valid_length b2"
  shows "b2 = CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_x (flags b2) (CRB x))"
  using assms unfolding CleanQ_RB_write_head_flags_x_def CleanQ_RB_read_head_x_def
  by(auto)

lemma CleanQ_RB_write_head_region_x_eq :
  shows "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_x (region b2) (CRB x))) = region b2"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_offset_x_eq :
  shows "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_x (offset b2) (CRB x))) = offset b2"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_length_x_eq :
  shows "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_x (length b2) (CRB x))) = length b2"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_valid_length_x_eq :
  shows "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_x (valid_length b2) (CRB x))) = valid_length b2"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_x_def)
  

lemma CleanQ_RB_write_head_valid_offset_x_eq :
  shows "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_x (valid_offset b2) (CRB x))) = valid_offset b2"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_x_def)
  
lemmas CleanQ_RB_write_head_x_eq[simp] = 
  CleanQ_RB_write_head_region_x_eq
  CleanQ_RB_write_head_offset_x_eq 
  CleanQ_RB_write_head_length_x_eq
  CleanQ_RB_write_head_valid_offset_x_eq
  CleanQ_RB_write_head_valid_length_x_eq
  CleanQ_RB_write_head_flags_x_eq

paragraph \<open>Write head behaves as expected for Y\<close>

lemma CleanQ_RB_write_head_flags_y_eq:
  assumes reg: "region (CleanQ_RB_read_head_y (CRB x)) = region b2" and
          off: "offset (CleanQ_RB_read_head_y (CRB x)) = offset b2 " and
          len: "length (CleanQ_RB_read_head_y (CRB x)) = length b2" and
          vao: "valid_offset (CleanQ_RB_read_head_y (CRB x)) = valid_offset b2" and
          val:"valid_length (CleanQ_RB_read_head_y (CRB x)) = valid_length b2"
  shows "b2 = CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_y (flags b2) (CRB x))"
  using assms unfolding CleanQ_RB_write_head_flags_y_def CleanQ_RB_read_head_y_def
  by(auto)

lemma CleanQ_RB_write_head_region_y_eq :
  shows "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_y (region b2) (CRB y))) = region b2"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_offset_y_eq :
  shows "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_y (offset b2) (CRB y))) = offset b2"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_length_y_eq :
  shows "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_y (length b2) (CRB y))) = length b2"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_valid_length_y_eq :
  shows "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_y (valid_length b2) (CRB y))) = valid_length b2"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_y_def)
  
lemma CleanQ_RB_write_head_valid_offset_y_eq :
  shows "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_y (valid_offset b2) (CRB y))) = valid_offset b2"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_y_def)

lemmas CleanQ_RB_write_head_y_eq[simp] = 
  CleanQ_RB_write_head_region_y_eq
  CleanQ_RB_write_head_offset_y_eq 
  CleanQ_RB_write_head_length_y_eq
  CleanQ_RB_write_head_valid_offset_y_eq
  CleanQ_RB_write_head_valid_length_y_eq
  CleanQ_RB_write_head_flags_y_eq


(* These ones seem to be not used by simp yet*)
lemma CleanQ_RB_write_head_y_flags_none_false :
  "CleanQ_RB_head_none_y (CleanQ_RB_write_head_flags_y (flags b2) (CRB x)) \<Longrightarrow> False"
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_x_flags_none_false :
  "CleanQ_RB_head_none_x (CleanQ_RB_write_head_flags_x (flags b2) (CRB x)) \<Longrightarrow> False"
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_y_region_none_false :
  "CleanQ_RB_head_none_y (CleanQ_RB_write_head_region_y (flags b2) (CRB x)) \<Longrightarrow> False"
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_x_region_none_false :
  "CleanQ_RB_head_none_x (CleanQ_RB_write_head_region_x (flags b2) (CRB x)) \<Longrightarrow> False"
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_region_x_def)


lemmas CleanQ_RB_write_head_x_region_none[simp] = 
  CleanQ_RB_write_head_x_region_none_false
  CleanQ_RB_write_head_x_flags_none_false

lemmas CleanQ_RB_write_head_y_region_none[simp] = 
  CleanQ_RB_write_head_y_region_none_false
  CleanQ_RB_write_head_y_flags_none_false

lemma CleanQ_RB_read_tail_y_flags [simp]:
  assumes "buf_y x = CleanQ_RB_read_tail_region_y (CRB x) (buf_y x)" and
          "buf_y x = CleanQ_RB_read_tail_offset_y (CRB x) (buf_y x)" and
          "buf_y x = CleanQ_RB_read_tail_length_y (CRB x) (buf_y x)" and
          "buf_y x = CleanQ_RB_read_tail_valid_offset_y (CRB x) (buf_y x)" and
          "buf_y x = CleanQ_RB_read_tail_valid_length_y (CRB x) (buf_y x)"
  shows "CleanQ_RB_read_tail_flags_y (CRB x) (buf_y x) = CleanQ_RB_read_tail_y (CRB x)"
  unfolding CleanQ_RB_read_tail_flags_y_def
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(5) 
      CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_valid_length_y_def 
      CleanQ_RB_read_tail_valid_offset_y_def CleanQ_RB_read_tail_y_fields_eq assms(1) assms(2) assms(3) assms(4) assms(5))

lemma CleanQ_RB_read_tail_x_flags [simp]:
  assumes "buf_x x = CleanQ_RB_read_tail_region_x (CRB x) (buf_x x)" and
          "buf_x x = CleanQ_RB_read_tail_offset_x (CRB x) (buf_x x)" and
          "buf_x x = CleanQ_RB_read_tail_length_x (CRB x) (buf_x x)" and
          "buf_x x = CleanQ_RB_read_tail_valid_offset_x (CRB x) (buf_x x)" and
          "buf_x x = CleanQ_RB_read_tail_valid_length_x (CRB x) (buf_x x)"
  shows "CleanQ_RB_read_tail_flags_x (CRB x) (buf_x x) = CleanQ_RB_read_tail_x (CRB x)"
  unfolding CleanQ_RB_read_tail_flags_x_def
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(5) 
      CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_valid_length_x_def 
      CleanQ_RB_read_tail_valid_offset_x_def CleanQ_RB_read_tail_x_fields_eq assms(1) assms(2) assms(3) assms(4) assms(5)) 

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Final concurrency proof\<close>
(* ------------------------------------------------------------------------------------ *)

lemma CleanQ_RB_conc_mult_if_all:
     "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/{True}\<^esub>   
      COBEGIN
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         WHILE True INV \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         DO  
            CleanQ_CRB_enq_mult_x b;;
            CleanQ_CRB_deq_mult_x
         OD
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>  
         \<parallel> 
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         WHILE True INV \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
         DO 
            CleanQ_CRB_enq_mult_y b2;;
            CleanQ_CRB_deq_mult_y
         OD
         \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>
      COEND
      \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>, \<lbrace>True\<rbrace>" 
  apply(oghoare) (* 906 subgoals. Auto after this takes really really long*)
  apply(auto)[200]
  apply(auto)[200]
  apply(auto)[200]
  apply(auto)[200]
  apply(auto)
  done

end 