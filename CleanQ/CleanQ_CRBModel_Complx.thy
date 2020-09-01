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
(* valid_offset :: nat *)
(* valid_length :: nat *)
(* flags :: nat *)


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

(*
definition CleanQ_RB_read_tail_valid_offset_x :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where "CleanQ_RB_read_tail_valid_offset_x rb b = 
            b \<lparr> valid_offset := valid_offset (rb_read_tail (rTYX rb)) \<rparr>"

definition CleanQ_RB_read_tail_valid_offset_y :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where "CleanQ_RB_read_tail_valid_offset_y rb b = 
            b \<lparr> valid_offset := valid_offset (rb_read_tail (rTXY rb)) \<rparr>"
*)
(*
definition CleanQ_RB_read_tail_valid_length_x :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where "CleanQ_RB_read_tail_valid_length_x rb b = 
            b \<lparr> valid_length := valid_length (rb_read_tail (rTYX rb)) \<rparr>"

definition CleanQ_RB_read_tail_valid_length_y :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where "CleanQ_RB_read_tail_valid_length_y rb b = 
            b \<lparr> valid_length := valid_length (rb_read_tail (rTXY rb)) \<rparr>"
*)
(*
definition CleanQ_RB_read_tail_flags_x :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where 
   "CleanQ_RB_read_tail_flags_x rb b = b \<lparr> flags := flags (rb_read_tail (rTYX rb)) \<rparr>"

definition CleanQ_RB_read_tail_flags_y :: 
  "CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer \<Rightarrow> CleanQ_Buffer" 
  where 
    "CleanQ_RB_read_tail_flags_y rb b = b \<lparr> flags := flags (rb_read_tail (rTXY rb)) \<rparr>"
*)


definition CleanQ_RB_write_head_region_x :: "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_region_x val rb = rb \<lparr>rTXY := rb_write_head ((rb_read_head (rTXY rb))\<lparr>region := val\<rparr>  )  (rTXY rb) \<rparr>"

definition CleanQ_RB_write_head_region_y :: "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_region_y val rb = rb \<lparr>rTYX := rb_write_head ((rb_read_head (rTYX rb))\<lparr>region := val\<rparr>  )  (rTYX rb) \<rparr>"

definition CleanQ_RB_write_head_offset_x :: "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_offset_x val rb = rb \<lparr>rTXY := rb_write_head ((rb_read_head (rTXY rb))\<lparr>offset := val\<rparr>  )  (rTXY rb) \<rparr>"

definition CleanQ_RB_write_head_offset_y :: "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_offset_y val rb = rb \<lparr>rTYX := rb_write_head ((rb_read_head (rTYX rb))\<lparr>offset := val\<rparr>  )  (rTYX rb) \<rparr>"

definition CleanQ_RB_write_head_length_x :: "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_length_x val rb = rb \<lparr>rTXY := rb_write_head ((rb_read_head (rTXY rb))\<lparr>length := val\<rparr>  )  (rTXY rb) \<rparr>"

definition CleanQ_RB_write_head_length_y :: "nat \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_length_y val rb = rb \<lparr>rTYX := rb_write_head ((rb_read_head (rTYX rb))\<lparr>length := val\<rparr>  )  (rTYX rb) \<rparr>"

text \<open>
  Show equality 
\<close>

lemma CleanQ_RB_read_tail_x_fields_eq :
  shows "CleanQ_RB_read_tail_x rb = 
    (CleanQ_RB_read_tail_length_x rb 
    (CleanQ_RB_read_tail_offset_x rb
    (CleanQ_RB_read_tail_region_x rb buf)))"
  unfolding CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_region_x_def
    CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_x_def
  by simp

lemma CleanQ_RB_read_tail_y_fields_eq :
  shows "CleanQ_RB_read_tail_y rb = 
    (CleanQ_RB_read_tail_length_y rb 
    (CleanQ_RB_read_tail_offset_y rb
    (CleanQ_RB_read_tail_region_y rb buf)))"
  unfolding CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_region_y_def
    CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def 
  by simp

text \<open>
  Other helper lemmas (mostly added to simp set for easier proofs)
\<close>


lemma CleanQ_RB_write_head_x_length_unchanged [simp]:
  shows "length (CleanQ_RB_read_head_x rb) = length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_x x rb))"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_x_offset_unchanged [simp]:
  shows "offset (CleanQ_RB_read_head_x rb) = offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_x x rb))"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_y_length_unchanged [simp]:
  shows "length (CleanQ_RB_read_head_y rb) = length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_y x rb))"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_y_offset_unchanged [simp]:
  shows "offset (CleanQ_RB_read_head_y rb) = offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_y x rb))"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_x_offset_inv [simp]:
  assumes inv: "CleanQ_RB_Invariants K rb"
  shows "CleanQ_RB_Invariants K (CleanQ_RB_write_head_offset_x x rb)"
  by (metis CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_Invariant CleanQ_RB_write_head_x_def inv)

lemma CleanQ_RB_write_head_y_offset_inv [simp]:
  assumes inv: "CleanQ_RB_Invariants K rb"
  shows "CleanQ_RB_Invariants K (CleanQ_RB_write_head_offset_y x rb)"
  by (metis CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_y_Invariant CleanQ_RB_write_head_y_def inv)

lemma CleanQ_RB_write_head_x_length_inv [simp]:
  assumes inv: "CleanQ_RB_Invariants K rb"
  shows "CleanQ_RB_Invariants K (CleanQ_RB_write_head_length_x x rb)"
  by (metis CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_Invariant CleanQ_RB_write_head_x_def inv)

lemma CleanQ_RB_write_head_y_length_inv [simp]:
  assumes inv: "CleanQ_RB_Invariants K rb"
  shows "CleanQ_RB_Invariants K (CleanQ_RB_write_head_length_y x rb)"
  by (metis CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_Invariant CleanQ_RB_write_head_y_def inv)

lemma CleanQ_RB_write_head_length_enq_x_possible [simp]:
  assumes inv: "CleanQ_RB_Invariants K rb"
  assumes can: "CleanQ_RB_enq_x_possible rb"
  shows "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_length_x x rb)"
  by (metis CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_can_enq_x CleanQ_RB_write_head_x_def can)

lemma CleanQ_RB_write_head_length_enq_y_possible [simp]:
  assumes inv: "CleanQ_RB_Invariants K rb"
  assumes can: "CleanQ_RB_enq_y_possible rb"
  shows "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_length_y x rb)"
  by (metis CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_can_enq_y CleanQ_RB_write_head_y_def can)

lemma CleanQ_RB_write_head_length_enq_xy_possible [simp]:
  assumes inv: "CleanQ_RB_Invariants K rb"
  assumes can: "CleanQ_RB_enq_x_possible rb \<and> CleanQ_RB_enq_y_possible rb"
  shows "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_length_x x rb)"
  by (metis CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(3) 
      CleanQ_RB_enq_y_possible_def CleanQ_RB_write_head_length_x_def can)

lemma CleanQ_RB_write_head_length_enq_xy2_possible [simp]:
  assumes inv: "CleanQ_RB_Invariants K rb"
  assumes can: "CleanQ_RB_enq_x_possible rb \<and> CleanQ_RB_enq_y_possible rb"
  shows "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_length_y x rb)"
  by (metis CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_can_enq_x CleanQ_RB_write_head_y_def can)

lemma CleanQ_RB_write_head_offset_enq_xy_possible [simp]:
  assumes inv: "CleanQ_RB_Invariants K rb"
  assumes can: "CleanQ_RB_enq_x_possible rb \<and> CleanQ_RB_enq_y_possible rb"
  shows "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_offset_x x rb)"
  by (metis CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(3) 
      CleanQ_RB_enq_y_possible_def CleanQ_RB_write_head_offset_x_def can)

lemma CleanQ_RB_write_head_offset_enq_xy2_possible [simp]:
  assumes inv: "CleanQ_RB_Invariants K rb"
  assumes can: "CleanQ_RB_enq_x_possible rb \<and> CleanQ_RB_enq_y_possible rb"
  shows "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_offset_y x rb)"
  by (metis CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_y_can_enq_x CleanQ_RB_write_head_y_def can)

lemma CleanQ_RB_write_head_offset_enq_x_possible [simp]:
  assumes inv: "CleanQ_RB_Invariants K rb"
  assumes can: "CleanQ_RB_enq_x_possible rb"
  shows "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_offset_x x rb)"
  by (metis CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_can_enq_x CleanQ_RB_write_head_x_def can)

lemma CleanQ_RB_write_head_offset_enq_y_possible [simp]:
  assumes inv: "CleanQ_RB_Invariants K rb"
  assumes can: "CleanQ_RB_enq_y_possible rb"
  shows "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_offset_y x rb)"
  by (metis CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_y_can_enq_y CleanQ_RB_write_head_y_def can)

lemma CleanQ_RB_write_head_offset_x_sx_unchanged [simp]:
  assumes inv: "CleanQ_RB_Invariants K rb"
  assumes can: "buf \<in> (rSX rb)"
  shows "buf \<in> (rSX (CleanQ_RB_write_head_offset_x (offset buf) rb))"
  by (simp add: CleanQ_RB_write_head_offset_x_def can)

lemma CleanQ_RB_write_head_offset_y_sy_unchanged [simp]:
  assumes inv: "CleanQ_RB_Invariants K rb"
  assumes can: "buf \<in> (rSY rb)"
  shows "buf \<in> (rSY (CleanQ_RB_write_head_offset_y (offset buf) rb))"
  by (simp add: CleanQ_RB_write_head_offset_y_def can)

lemma CleanQ_RB_write_head_length_x_sx_unchanged [simp]:
  assumes inv: "CleanQ_RB_Invariants K rb"
  assumes can: "buf \<in> (rSX rb)"
  shows "buf \<in> (rSX (CleanQ_RB_write_head_length_x (length buf) rb))"
  by (simp add: CleanQ_RB_write_head_length_x_def can)

lemma CleanQ_RB_write_head_length_y_sy_unchanged [simp]:
  assumes inv: "CleanQ_RB_Invariants K rb"
  assumes can: "buf \<in> (rSY rb)"
  shows "buf \<in> (rSY (CleanQ_RB_write_head_length_y (length buf) rb))"
  by (simp add: CleanQ_RB_write_head_length_y_def can)

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


lemma CleanQ_RB_write_head_length_x_sy_unchanged [simp]:
  assumes "b2 \<in> rSY (CRB x)"
  shows "b2 \<in> rSY (CleanQ_RB_write_head_length_x (CleanQ_Buffer.length b) (CRB x))"
  by (simp add: CleanQ_RB_write_head_length_x_def assms)

lemma CleanQ_RB_write_head_length_y_sx_unchanged [simp]:
  assumes "b2 \<in> rSX (CRB x)"
  shows "b2 \<in> rSX (CleanQ_RB_write_head_length_y (CleanQ_Buffer.length b) (CRB x))"
  by (simp add: CleanQ_RB_write_head_length_y_def assms)

lemma CleanQ_RB_write_head_offset_x_sy_unchanged [simp]:
  assumes "b2 \<in> rSY (CRB x)"
  shows "b2 \<in> rSY (CleanQ_RB_write_head_offset_x (CleanQ_Buffer.offset b) (CRB x))"
  by (simp add: CleanQ_RB_write_head_offset_x_def assms)

lemma CleanQ_RB_write_head_offset_y_sx_unchanged [simp]:
  assumes "b2 \<in> rSX (CRB x)"
  shows "b2 \<in> rSX (CleanQ_RB_write_head_offset_y (CleanQ_Buffer.offset b) (CRB x))"
  by (simp add: CleanQ_RB_write_head_offset_y_def assms)

lemma CleanQ_RB_write_head_region_x_sy_unchanged [simp]:
  assumes "b2 \<in> rSY (CRB x)"
  shows "b2 \<in> rSY (CleanQ_RB_write_head_region_x (CleanQ_Buffer.region b) (CRB x))"
  by (simp add: CleanQ_RB_write_head_region_x_def assms)

lemma CleanQ_RB_write_head_region_y_sx_unchanged [simp]:
  assumes "b2 \<in> rSX (CRB x)"
  shows "b2 \<in> rSX (CleanQ_RB_write_head_region_y (CleanQ_Buffer.region b) (CRB x))"
  by (simp add: CleanQ_RB_write_head_region_y_def assms)

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

lemma CleanQ_RB_head_not_none_write_head_region_y [simp]:
  shows "CleanQ_RB_head_none_y (CleanQ_RB_write_head_region_y (CleanQ_Buffer.region b2) (CRB x)) \<Longrightarrow> False"
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_head_not_none_write_head_region_x [simp]:
  shows "CleanQ_RB_head_none_x (CleanQ_RB_write_head_region_x (CleanQ_Buffer.region b2) (CRB x)) \<Longrightarrow> False"
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_region_x_def)


lemma CleanQ_RB_deq_y_possible_write_head_length_x [simp]:
  assumes "CleanQ_RB_deq_y_possible(CRB x)"
  shows "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_length_x (CleanQ_Buffer.length b) (CRB x))"
  by (metis CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_can_deq_y CleanQ_RB_write_head_x_def assms)

lemma CleanQ_RB_deq_x_possible_write_head_length_y [simp]:
  assumes "CleanQ_RB_deq_x_possible(CRB x)"
  shows "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_length_y (CleanQ_Buffer.length b) (CRB x))"
  by (metis CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_can_deq_x CleanQ_RB_write_head_y_def assms)

lemma CleanQ_RB_deq_y_possible_write_head_length_y [simp]:
  assumes "CleanQ_RB_deq_y_possible(CRB x)"
  shows "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_length_y (CleanQ_Buffer.length b) (CRB x))"
  by (metis CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(4) 
      CleanQ_RB_deq_y_possible_def CleanQ_RB_write_head_length_y_def assms)

lemma CleanQ_RB_deq_x_possible_write_head_length_x [simp]:
  assumes "CleanQ_RB_deq_x_possible(CRB x)"
  shows "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_length_x (CleanQ_Buffer.length b) (CRB x))"
  by (metis CleanQ_RB_State.select_convs(4) CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(3) 
      CleanQ_RB_deq_x_possible_def CleanQ_RB_write_head_length_x_def assms)

lemma CleanQ_RB_deq_y_possible_write_head_offset_x [simp]:
  assumes "CleanQ_RB_deq_y_possible(CRB x)"
  shows "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_offset_x (CleanQ_Buffer.offset b) (CRB x))"
  by (metis CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_can_deq_y CleanQ_RB_write_head_x_def assms)

lemma CleanQ_RB_deq_x_possible_write_head_offset_y [simp]:
  assumes "CleanQ_RB_deq_x_possible(CRB x)"
  shows "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_offset_y (CleanQ_Buffer.offset b) (CRB x))"
  by (metis CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_y_can_deq_x CleanQ_RB_write_head_y_def assms)

lemma CleanQ_RB_deq_y_possible_write_head_offset_y [simp]:
  assumes "CleanQ_RB_deq_y_possible(CRB x)"
  shows "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_offset_y (CleanQ_Buffer.offset b) (CRB x))"
  by (metis CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(4) 
      CleanQ_RB_deq_y_possible_def CleanQ_RB_write_head_offset_y_def assms)

lemma CleanQ_RB_deq_x_possible_write_head_offset_x [simp]:
  assumes "CleanQ_RB_deq_x_possible(CRB x)"
  shows "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_offset_x (CleanQ_Buffer.offset b) (CRB x))"
  by (metis CleanQ_RB_State.select_convs(4) CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(3) 
      CleanQ_RB_deq_x_possible_def CleanQ_RB_write_head_offset_x_def assms)

lemma CleanQ_RB_deq_y_possible_write_head_region_x [simp]:
  assumes "CleanQ_RB_deq_y_possible(CRB x)"
  shows "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_region_x (CleanQ_Buffer.region b) (CRB x))"
  by (metis CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_can_deq_y CleanQ_RB_write_head_x_def assms)

lemma CleanQ_RB_deq_x_possible_write_head_region_y [simp]:
  assumes "CleanQ_RB_deq_x_possible(CRB x)"
  shows "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_region_y (CleanQ_Buffer.region b) (CRB x))"
  by (metis CleanQ_RB_write_head_region_y_def CleanQ_RB_write_head_y_can_deq_x CleanQ_RB_write_head_y_def assms)

lemma CleanQ_RB_deq_y_possible_write_head_region_y [simp]:
  assumes "CleanQ_RB_deq_y_possible(CRB x)"
  shows "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_region_y (CleanQ_Buffer.region b) (CRB x))"
  by (metis CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(4) 
      CleanQ_RB_deq_y_possible_def CleanQ_RB_write_head_region_y_def assms)

lemma CleanQ_RB_deq_x_possible_write_head_region_x [simp]:
  assumes "CleanQ_RB_deq_x_possible(CRB x)"
  shows "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_region_x (CleanQ_Buffer.region b) (CRB x))"
  by (metis CleanQ_RB_State.select_convs(4) CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(3) 
      CleanQ_RB_deq_x_possible_def CleanQ_RB_write_head_region_x_def assms)

(*
lemma CleanQ_RB_read_tail_offset [simp]:
  assumes "buf_y x = CleanQ_RB_read_tail_offset_y (CRB x) (buf_y x)" and
          "CleanQ_RB_deq_y_possible (CRB x)"
  shows "buf_y x = CleanQ_RB_read_tail_offset_y (CleanQ_RB_write_head_length_x (CleanQ_Buffer.length b) (CRB x)) (buf_y x)"
  using assms
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x 
      CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_def)  


lemma CleanQ_RB_read_tail_y_length_eq [simp]:
  assumes "buf_y x = CleanQ_RB_read_tail_offset_y (CRB x) (buf_y x) "
  shows "CleanQ_RB_read_tail_length_y (CRB x) (buf_y x) = CleanQ_RB_read_tail_y (CRB x)"
  by (metis CleanQ_RB_read_tail_y_fields_eq assms)

lemma CleanQ_RB_read_tail_x_length_eq [simp]:
  assumes "buf_x x = CleanQ_RB_read_tail_offset_x (CRB x) (buf_x x) "
  shows "CleanQ_RB_read_tail_length_x (CRB x) (buf_x x) = CleanQ_RB_read_tail_x (CRB x)"
  by (metis CleanQ_RB_read_tail_x_fields_eq assms)
*)

lemma CleanQ_RB_read_tail_y_offset_eq [simp]:
  assumes "buf_y x = CleanQ_RB_read_tail_length_y (CRB x) (buf_y x) " and
          "buf_y x = CleanQ_RB_read_tail_region_y (CRB x) (buf_y x)"
  shows "CleanQ_RB_read_tail_offset_y (CRB x) (buf_y x) = CleanQ_RB_read_tail_y (CRB x)"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(3) 
      CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_fields_eq assms(1) assms(2))
  
lemma CleanQ_RB_read_tail_x_offset_eq [simp]:
  assumes "buf_x x = CleanQ_RB_read_tail_length_x (CRB x) (buf_x x) " and
          "buf_x x = CleanQ_RB_read_tail_region_x (CRB x) (buf_x x)"
  shows "CleanQ_RB_read_tail_offset_x (CRB x) (buf_x x) = CleanQ_RB_read_tail_x (CRB x)"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(3) 
      CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_x_fields_eq assms(1) assms(2))

lemma CleanQ_RB_read_head_x_write_length_y [simp]:
  shows "CleanQ_RB_read_head_x (CRB x) = CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_y (CleanQ_Buffer.length b2) (CRB x))"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_read_head_x_write_offset_y [simp]:
  shows "CleanQ_RB_read_head_x (CRB x) = CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_y (CleanQ_Buffer.offset b2) (CRB x))"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_read_head_x_write_region_y [simp]:
  shows "CleanQ_RB_read_head_x (CRB x) = CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_y (CleanQ_Buffer.region b2) (CRB x))"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_read_head_y_write_length_x [simp]:
  shows "CleanQ_RB_read_head_y (CRB x) = CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_x (CleanQ_Buffer.length b2) (CRB x))"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_read_head_y_write_offset_x [simp]:
  shows "CleanQ_RB_read_head_y (CRB x) = CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_x (CleanQ_Buffer.offset b2) (CRB x))"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_read_head_y_write_reigon_x [simp]:
  shows "CleanQ_RB_read_head_y (CRB x) = CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_x (CleanQ_Buffer.region b2) (CRB x))"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_x_def)

(*
lemma CleanQ_RB_read_tail_x_fields_eq :
  shows "CleanQ_RB_read_tail_x rb = 
    CleanQ_RB_read_tail_flags_x rb
    (CleanQ_RB_read_tail_valid_length_x rb 
    (CleanQ_RB_read_tail_valid_offset_x rb 
    (CleanQ_RB_read_tail_length_x rb 
    (CleanQ_RB_read_tail_offset_x rb 
    (CleanQ_RB_read_tail_region_x rb buf)))))"
  unfolding CleanQ_RB_read_tail_region_x_def CleanQ_RB_read_tail_offset_x_def
    CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_valid_offset_x_def
    CleanQ_RB_read_tail_valid_length_x_def CleanQ_RB_read_tail_flags_x_def
    CleanQ_RB_read_tail_x_def 
  by simp

lemma CleanQ_RB_read_tail_y_fields_eq :
  shows "CleanQ_RB_read_tail_y rb = 
    CleanQ_RB_read_tail_flags_y rb
    (CleanQ_RB_read_tail_valid_length_y rb 
    (CleanQ_RB_read_tail_valid_offset_y rb 
    (CleanQ_RB_read_tail_length_y rb 
    (CleanQ_RB_read_tail_offset_y rb 
    (CleanQ_RB_read_tail_region_y rb buf)))))"
  unfolding CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_offset_y_def
    CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_valid_offset_y_def
    CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_flags_y_def
    CleanQ_RB_read_tail_y_def 
  by simp

lemma CleanQ_RB_write_head_x_fields_eq :
  shows "CleanQ_RB_write_head_x buf rb = 
    CleanQ_RB_write_head_flags_x (flags buf) buf
    (CleanQ_RB_write_head_valid_length_x (valid_length buf) buf
    (CleanQ_RB_write_head_valid_offset_x (valid_offset buf) buf
    (CleanQ_RB_write_head_length_x (length buf) buf
    (CleanQ_RB_write_head_offset_x (offset buf) buf
    (CleanQ_RB_write_head_region_x (region buf) buf rb)))))"
  unfolding CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_offset_x_def
    CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_valid_offset_x_def
    CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_flags_x_def
    CleanQ_RB_write_head_x_def
  apply simp
  by (metis rb_write_head_not_none rb_write_head_read_written rb_write_head_same) 

lemma CleanQ_RB_write_head_x_fields2_eq :
  shows "CleanQ_RB_write_head_x buf rb = 
    CleanQ_RB_write_head_x (CleanQ_RB_write_flags_x (flags buf) 
    (CleanQ_RB_write_valid_length_x (valid_length buf) 
    (CleanQ_RB_write_valid_offset_x (valid_offset buf)
    (CleanQ_RB_write_length_x (length buf) 
    (CleanQ_RB_write_offset_x (offset buf) 
    (CleanQ_RB_write_region_x (region buf) buf)))))) rb"
  by (simp add: CleanQ_RB_write_flags_x_def CleanQ_RB_write_length_x_def CleanQ_RB_write_offset_x_def 
      CleanQ_RB_write_region_x_def CleanQ_RB_write_valid_length_x_def CleanQ_RB_write_valid_offset_x_def)
  

lemma CleanQ_RB_write_head_y_fields_eq :
  shows "CleanQ_RB_write_head_y buf rb = 
    CleanQ_RB_write_head_flags_y (flags buf) buf
    (CleanQ_RB_write_head_valid_length_y (valid_length buf) buf
    (CleanQ_RB_write_head_valid_offset_y (valid_offset buf) buf
    (CleanQ_RB_write_head_length_y (length buf) buf
    (CleanQ_RB_write_head_offset_y (offset buf) buf
    (CleanQ_RB_write_head_region_y (region buf) buf rb)))))"
  unfolding CleanQ_RB_write_head_region_y_def CleanQ_RB_write_head_offset_y_def
    CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_valid_offset_y_def
    CleanQ_RB_write_head_valid_length_y_def CleanQ_RB_write_head_flags_y_def
    CleanQ_RB_write_head_y_def
  apply simp
  by (metis rb_write_head_not_none rb_write_head_read_written rb_write_head_same) 

lemma CleanQ_RB_write_head_y_fields2_eq :
  shows "CleanQ_RB_write_head_y buf rb = 
    CleanQ_RB_write_head_y (CleanQ_RB_write_flags_y (flags buf) 
    (CleanQ_RB_write_valid_length_y (valid_length buf) 
    (CleanQ_RB_write_valid_offset_y (valid_offset buf)
    (CleanQ_RB_write_length_y (length buf) 
    (CleanQ_RB_write_offset_y (offset buf) 
    (CleanQ_RB_write_region_y (region buf) buf)))))) rb"
  by (simp add: CleanQ_RB_write_flags_y_def CleanQ_RB_write_length_y_def CleanQ_RB_write_offset_y_def 
      CleanQ_RB_write_region_y_def CleanQ_RB_write_valid_length_y_def CleanQ_RB_write_valid_offset_y_def)
*)

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

lemma CleanQ_RB_write_twice_offset_x :
shows "offset (CleanQ_RB_write_offset_x (offset b) (local_x x)) = offset b"
  by (simp add: CleanQ_RB_write_offset_x_def)

lemma CleanQ_RB_write_twice_offset_y :
shows "offset (CleanQ_RB_write_offset_y (offset b) (local_y x)) = offset b"
  by (simp add: CleanQ_RB_write_offset_y_def)

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
(*
abbreviation "CleanQ_CRB_enq_mult_x b \<equiv> 
            \<lbrace> CleanQ_RB_Invariants \<acute>uni \<acute>CRB  \<rbrace>
            IF CleanQ_RB_enq_x_possible \<acute>CRB \<and> b \<in> rSX \<acute>CRB
            THEN
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_region_x (region b) b \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region b = region (CleanQ_RB_read_head_x \<acute>CRB) 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_offset_x (offset b) b \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region b = region (CleanQ_RB_read_head_x \<acute>CRB) \<and>
                offset b = offset (CleanQ_RB_read_head_x \<acute>CRB) 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_length_x (length b) b \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region b = region (CleanQ_RB_read_head_x \<acute>CRB) \<and>
                offset b = offset (CleanQ_RB_read_head_x \<acute>CRB) \<and>
                length b = length (CleanQ_RB_read_head_x \<acute>CRB) 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_valid_offset_x (valid_offset b) b \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region b = region (CleanQ_RB_read_head_x \<acute>CRB) \<and>
                offset b = offset (CleanQ_RB_read_head_x \<acute>CRB) \<and>
                length b = length (CleanQ_RB_read_head_x \<acute>CRB) \<and>
                valid_offset b = valid_offset (CleanQ_RB_read_head_x \<acute>CRB) 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_valid_length_x (valid_length b) b \<acute>CRB) ;;
               \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region b = region (CleanQ_RB_read_head_x \<acute>CRB) \<and>
                offset b = offset (CleanQ_RB_read_head_x \<acute>CRB) \<and>
                length b = length (CleanQ_RB_read_head_x \<acute>CRB) \<and>
                valid_offset b = valid_offset (CleanQ_RB_read_head_x \<acute>CRB) \<and>
                valid_length b = valid_length (CleanQ_RB_read_head_x \<acute>CRB)
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_flags_x (flags b) b \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_Q \<acute>uni \<acute>CRB b \<rbrace>
                \<acute>CRB := (CleanQ_RB_incr_head_x b \<acute>CRB)
            ELSE 
                \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
                SKIP
            FI"

abbreviation "CleanQ_CRB_enq_mult_x2 b \<equiv> 
            \<lbrace> CleanQ_RB_Invariants \<acute>uni \<acute>CRB  \<rbrace>
            IF CleanQ_RB_enq_x_possible \<acute>CRB \<and> b \<in> rSX \<acute>CRB
            THEN
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<rbrace>
                \<acute>local_x := (CleanQ_RB_write_region_x (region b) \<acute>local_x) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region \<acute>local_x = region b 
              \<rbrace>
                \<acute>local_x := (CleanQ_RB_write_offset_x (offset b) \<acute>local_x) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region \<acute>local_x = region b \<and>
                offset \<acute>local_x = offset b 
              \<rbrace>
                \<acute>local_x := (CleanQ_RB_write_length_x (length b) \<acute>local_x) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region \<acute>local_x = region b \<and>
                offset \<acute>local_x = offset b \<and>
                length \<acute>local_x = length b 
              \<rbrace>
                \<acute>local_x := (CleanQ_RB_write_valid_offset_x (valid_offset b) b) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region \<acute>local_x = region b \<and>
                offset \<acute>local_x = offset b \<and>
                length \<acute>local_x = length b \<and>
                valid_offset \<acute>local_x = valid_offset b 
              \<rbrace>
                \<acute>local_x := (CleanQ_RB_write_valid_length_x (valid_length b) b) ;;
               \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region \<acute>local_x = region b \<and>
                offset \<acute>local_x = offset b \<and>
                length \<acute>local_x = length b \<and>
                valid_offset \<acute>local_x = valid_offset b \<and>
                valid_length \<acute>local_x = valid_length b
               \<rbrace>
                \<acute>local_x := (CleanQ_RB_write_flags_x (flags b) b) ;;
               \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region \<acute>local_x = region b \<and>
                offset \<acute>local_x = offset b \<and>
                length \<acute>local_x = length b \<and>
                valid_offset \<acute>local_x = valid_offset b \<and>
                valid_length \<acute>local_x = valid_length b \<and>
                flags \<acute>local_x = flags b
              \<rbrace>
              \<acute>CRB := (CleanQ_RB_write_head_x \<acute>local_x \<acute>CRB);;
              \<lbrace> CleanQ_RB_enq_x_Q \<acute>uni \<acute>CRB b \<rbrace>
                \<acute>CRB := (CleanQ_RB_incr_head_x b \<acute>CRB)
            ELSE 
                \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
                SKIP
            FI"
*) 

abbreviation "CleanQ_CRB_enq_mult_x b \<equiv> 
            \<lbrace> CleanQ_RB_Invariants \<acute>uni \<acute>CRB  \<rbrace>
            IF CleanQ_RB_enq_x_possible \<acute>CRB \<and> b \<in> rSX \<acute>CRB
            THEN
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_region_x (offset b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region (CleanQ_RB_read_head_x \<acute>CRB) = region b 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_offset_x (offset b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region (CleanQ_RB_read_head_x \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_x \<acute>CRB) = offset b 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_length_x (length b) \<acute>CRB) ;;
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
                \<acute>CRB := (CleanQ_RB_write_head_region_y (offset b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and> 
                region (CleanQ_RB_read_head_y \<acute>CRB) = region b 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_offset_y (offset b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and>  
                region (CleanQ_RB_read_head_y \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_y \<acute>CRB) = offset b 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_length_y (length b) \<acute>CRB) ;;
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
              \<lbrace> CleanQ_RB_deq_x_Q \<acute>uni \<acute>CRB \<acute>buf_x \<rbrace>
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
              \<lbrace> CleanQ_RB_deq_y_Q \<acute>uni \<acute>CRB \<acute>buf_y \<rbrace>
                \<acute>CRB := (CleanQ_RB_incr_tail_y \<acute>buf_y \<acute>CRB)
            ELSE 
                \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
                SKIP
            FI"

(*
abbreviation "CleanQ_CRB_enq_mult_y b \<equiv> 
            \<lbrace> CleanQ_RB_Invariants \<acute>uni \<acute>CRB  \<rbrace>
            IF CleanQ_RB_enq_y_possible \<acute>CRB \<and> b \<in> rSY \<acute>CRB
            THEN
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<rbrace>
                \<acute>local_y := (CleanQ_RB_write_region_y (region b) \<acute>local_y) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and> 
                region \<acute>local_y = region b 
              \<rbrace>
                \<acute>local_y := (CleanQ_RB_write_offset_y (offset b) \<acute>local_y) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and> 
                region \<acute>local_y = region b \<and>
                offset \<acute>local_y = offset b 
              \<rbrace>
                \<acute>local_y := (CleanQ_RB_write_length_y (length b) \<acute>local_y) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and> 
                region \<acute>local_y = region b \<and>
                offset \<acute>local_y = offset b \<and>
                length \<acute>local_y = length b 
              \<rbrace>
                \<acute>local_y := (CleanQ_RB_write_valid_offset_y (valid_offset b) b) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and> 
                region \<acute>local_y = region b \<and>
                offset \<acute>local_y = offset b \<and>
                length \<acute>local_y = length b \<and>
                valid_offset \<acute>local_y = valid_offset b 
              \<rbrace>
                \<acute>local_y := (CleanQ_RB_write_valid_length_y (valid_length b) b) ;;
               \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and> 
                region \<acute>local_y = region b \<and>
                offset \<acute>local_y = offset b \<and>
                length \<acute>local_y = length b \<and>
                valid_offset \<acute>local_y = valid_offset b \<and>
                valid_length \<acute>local_y = valid_length b
               \<rbrace>
                \<acute>local_y := (CleanQ_RB_write_flags_y (flags b) b) ;;
               \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and> 
                region \<acute>local_y = region b \<and>
                offset \<acute>local_y = offset b \<and>
                length \<acute>local_y = length b \<and>
                valid_offset \<acute>local_y = valid_offset b \<and>
                valid_length \<acute>local_y = valid_length b \<and>
                flags \<acute>local_y = flags b
              \<rbrace>
              \<acute>CRB := (CleanQ_RB_write_head_y \<acute>local_y \<acute>CRB);;
              \<lbrace> CleanQ_RB_enq_y_Q \<acute>uni \<acute>CRB b \<rbrace>
                \<acute>CRB := (CleanQ_RB_incr_head_y b \<acute>CRB)
            ELSE 
                \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
                SKIP
            FI"


abbreviation "CleanQ_CRB_enq_mult_y b \<equiv> 
            \<lbrace> CleanQ_RB_Invariants \<acute>uni \<acute>CRB  \<rbrace>
            IF CleanQ_RB_enq_y_possible \<acute>CRB \<and> b \<in> rSY \<acute>CRB
            THEN
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_region_y (region b) b \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and> 
                region b = region (CleanQ_RB_read_head_y \<acute>CRB) 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_offset_y (offset b) b \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and> 
                region b = region (CleanQ_RB_read_head_y \<acute>CRB) \<and>
                offset b = offset (CleanQ_RB_read_head_y \<acute>CRB) 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_length_y (length b) b \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and> 
                region b = region (CleanQ_RB_read_head_y \<acute>CRB) \<and>
                offset b = offset (CleanQ_RB_read_head_y \<acute>CRB) \<and>
                length b = length (CleanQ_RB_read_head_y \<acute>CRB) 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_valid_offset_y (valid_offset b) b \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and> 
                region b = region (CleanQ_RB_read_head_y \<acute>CRB) \<and>
                offset b = offset (CleanQ_RB_read_head_y \<acute>CRB) \<and>
                length b = length (CleanQ_RB_read_head_y \<acute>CRB) \<and>
                valid_offset b = valid_offset (CleanQ_RB_read_head_y \<acute>CRB) 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_valid_length_y (valid_length b) b \<acute>CRB) ;;
               \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and> 
                region b = region (CleanQ_RB_read_head_y \<acute>CRB) \<and>
                offset b = offset (CleanQ_RB_read_head_y \<acute>CRB) \<and>
                length b = length (CleanQ_RB_read_head_y \<acute>CRB) \<and>
                valid_offset b = valid_offset (CleanQ_RB_read_head_y \<acute>CRB) \<and>
                valid_length b = valid_length (CleanQ_RB_read_head_y \<acute>CRB)
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_flags_y (flags b) b \<acute>CRB) ;;
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
                \<acute>buf_x = CleanQ_RB_read_tail_region_x \<acute>CRB \<acute>buf_x \<rbrace>
                \<acute>buf_x := (CleanQ_RB_read_tail_offset_x \<acute>CRB \<acute>buf_x) ;;
              \<lbrace> CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_offset_x \<acute>CRB (CleanQ_RB_read_tail_region_x \<acute>CRB \<acute>buf_x) \<rbrace>
                \<acute>buf_x := (CleanQ_RB_read_tail_length_x \<acute>CRB \<acute>buf_x) ;;
              \<lbrace> CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_length_x \<acute>CRB
                        (CleanQ_RB_read_tail_offset_x \<acute>CRB 
                        (CleanQ_RB_read_tail_region_x \<acute>CRB \<acute>buf_x))\<rbrace>
                \<acute>buf_x := (CleanQ_RB_read_tail_valid_offset_x \<acute>CRB \<acute>buf_x) ;;
              \<lbrace> CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<and>
                \<acute>buf_x =(CleanQ_RB_read_tail_valid_offset_x \<acute>CRB 
                        (CleanQ_RB_read_tail_length_x \<acute>CRB
                        (CleanQ_RB_read_tail_offset_x \<acute>CRB 
                        (CleanQ_RB_read_tail_region_x \<acute>CRB \<acute>buf_x))))\<rbrace>
                \<acute>buf_x := (CleanQ_RB_read_tail_valid_length_x \<acute>CRB \<acute>buf_x) ;;
              \<lbrace> CleanQ_RB_deq_x_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<and>
                \<acute>buf_x = CleanQ_RB_read_tail_valid_length_x \<acute>CRB
                        (CleanQ_RB_read_tail_valid_offset_x \<acute>CRB 
                        (CleanQ_RB_read_tail_length_x \<acute>CRB
                        (CleanQ_RB_read_tail_offset_x \<acute>CRB 
                        (CleanQ_RB_read_tail_region_x \<acute>CRB \<acute>buf_x))))\<rbrace>
                \<acute>buf_x := (CleanQ_RB_read_tail_flags_x \<acute>CRB \<acute>buf_x) ;;
              \<lbrace> CleanQ_RB_deq_x_Q \<acute>uni \<acute>CRB \<acute>buf_x \<rbrace>
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
                \<acute>buf_y = CleanQ_RB_read_tail_offset_y \<acute>CRB (CleanQ_RB_read_tail_region_y \<acute>CRB \<acute>buf_y) 
              \<rbrace>
                \<acute>buf_y := (CleanQ_RB_read_tail_length_y \<acute>CRB \<acute>buf_y) ;;
              \<lbrace> CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_y \<acute>CRB) \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_length_y \<acute>CRB
                        (CleanQ_RB_read_tail_offset_y \<acute>CRB 
                        (CleanQ_RB_read_tail_region_y \<acute>CRB \<acute>buf_y))\<rbrace>
                \<acute>buf_y := (CleanQ_RB_read_tail_valid_offset_y \<acute>CRB \<acute>buf_y) ;;
              \<lbrace> CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_y \<acute>CRB) \<and>
                \<acute>buf_y =(CleanQ_RB_read_tail_valid_offset_y \<acute>CRB 
                        (CleanQ_RB_read_tail_length_y \<acute>CRB
                        (CleanQ_RB_read_tail_offset_y \<acute>CRB 
                        (CleanQ_RB_read_tail_region_y \<acute>CRB \<acute>buf_y))))\<rbrace>
                \<acute>buf_y := (CleanQ_RB_read_tail_valid_length_y \<acute>CRB \<acute>buf_y) ;;
              \<lbrace> CleanQ_RB_deq_y_P \<acute>uni \<acute>CRB (CleanQ_RB_read_tail_y \<acute>CRB) \<and>
                \<acute>buf_y = CleanQ_RB_read_tail_valid_length_y \<acute>CRB
                        (CleanQ_RB_read_tail_valid_offset_y \<acute>CRB 
                        (CleanQ_RB_read_tail_length_y \<acute>CRB
                        (CleanQ_RB_read_tail_offset_y \<acute>CRB 
                        (CleanQ_RB_read_tail_region_y \<acute>CRB \<acute>buf_y))))\<rbrace>
                \<acute>buf_y := (CleanQ_RB_read_tail_flags_y \<acute>CRB \<acute>buf_y) ;;
              \<lbrace> CleanQ_RB_deq_y_Q \<acute>uni \<acute>CRB \<acute>buf_y \<rbrace>
                \<acute>CRB := (CleanQ_RB_incr_tail_y \<acute>buf_y \<acute>CRB)
            ELSE 
                \<lbrace>  CleanQ_RB_Invariants \<acute>uni \<acute>CRB \<rbrace>
                SKIP
            FI"
*)
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
  apply(oghoare, auto)
  apply (simp add: CleanQ_RB_enq_x_def CleanQ_RB_enq_y_possible_def)
  using CleanQ_RB_deq_y_enq_y_possible CleanQ_RB_enq_y_possible_def by blast
  
  
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
   apply(oghoare, auto)
   by(simp_all add: CleanQ_RB_deq_x_no_change CleanQ_RB_deq_y_possible_def)

  
  
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
  apply (simp add: CleanQ_RB_deq_x_no_change CleanQ_RB_deq_y_possible_def)
  apply (simp add: CleanQ_RB_Invariants_def CleanQ_RB_deq_y_possible_def CleanQ_RB_enq_x_possible_def I4_rb_valid_def)
  by (simp add: CleanQ_RB_deq_x_no_change CleanQ_RB_deq_y_possible_def)

  
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
  apply(auto)
  by (simp_all add: CleanQ_RB_deq_y_possible_def)

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
  apply(oghoare, auto) (* 202 subgoals. Auto after this takes really really long*)
  sorry


end 