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




(* #################################################################################### *)
section \<open>CRB Proofs in Complex\<close>
(* #################################################################################### *)

text \<open>
  So far, we have shown that the ring buffer model is correct with regards to the 
  sequential execution. We now show that this holds also for concurrent execution
  using Owicky-Gries style proofs in the Complex framework.
\<close>

(*<*) 
theory CleanQ_CRBModel_Complx
  imports CleanQ_CRBModel
          "../Complx/OG_Syntax"
          "../Complx/OG_Hoare"
begin
(*>*)  


(* ==================================================================================== *)
subsection \<open>CleanQ Abstract Concurrent Ring Buffer Model State\<close>
(* ==================================================================================== *)

text \<open>
  Previously we only defined that the ring contains \emph{a buffer} without specifying
  the representation of this buffer. We now represent the buffer as a record, which 
  closely resembles the the struct of the SimpleQ C implementation. 
\<close>

record CleanQ_Buffer =
  region :: nat
  offset :: nat
  length :: nat
  valid_offset :: nat 
  valid_length :: nat
  flags :: nat 


text \<open>
  We use the exact same model as with the abstract ringbuffer but now initialize the 
  generic type using our \verb+CleanQ_Buffer+ record above. This is important, as
  updates to the buffer record are no-longer. 
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
subsubsection \<open>Redefining Writing/Reading a buffer\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  In reality, a struct cannot be written or read atomically--unless its smaller than a 
  machine word, which is not the case for our buffer representation. Therefore, reading
  or writing a struct, or in our case the \verb+CleanQ_Buffer+ is not atomic, and must
  be represented as a sequence of atomic steps. We therefore define read and write 
  operations for buffer fields accordingly.  
\<close>

paragraph \<open>Reading a Buffer\<close>

text \<open>
  For each of the record fields, we define a read operation that reads the content 
  of the ring buffer at the tail position and then updates the field in a (local) 
  buffer record passed to the function. We define this operation symmetrically for both
  sides X and Y.
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


text \<open>
  We can now show that we have equality in doing all the reads separately, as opposed
  to do them individually.
\<close>

lemma CleanQ_RB_read_tail_x_fields_eq :
  "CleanQ_RB_read_tail_valid_offset_x rb 
    (CleanQ_RB_read_tail_valid_length_x rb
      (CleanQ_RB_read_tail_flags_x rb 
        (CleanQ_RB_read_tail_length_x rb 
          (CleanQ_RB_read_tail_offset_x rb 
            (CleanQ_RB_read_tail_region_x rb buf))))) 
   = CleanQ_RB_read_tail_x rb"
  unfolding CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_region_x_def
    CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_x_def 
    CleanQ_RB_read_tail_valid_offset_x_def CleanQ_RB_read_tail_valid_length_x_def
    CleanQ_RB_read_tail_flags_x_def
  by simp

lemma CleanQ_RB_read_tail_y_fields_eq :
  "CleanQ_RB_read_tail_valid_offset_y rb
    (CleanQ_RB_read_tail_valid_length_y rb
      (CleanQ_RB_read_tail_flags_y rb
        (CleanQ_RB_read_tail_length_y rb 
          (CleanQ_RB_read_tail_offset_y rb
            (CleanQ_RB_read_tail_region_y rb buf))))) 
   = CleanQ_RB_read_tail_y rb"
  unfolding CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_region_y_def
    CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def 
    CleanQ_RB_read_tail_valid_offset_y_def CleanQ_RB_read_tail_valid_length_y_def
    CleanQ_RB_read_tail_flags_y_def
  by simp


text \<open>
  The read operations do commute. We just show this with an example, doing this for all
  pairs is similar. 
\<close>

lemma CleanQ_RB_read_tail_x_fields_commute1:
  "CleanQ_RB_read_tail_length_x rb (CleanQ_RB_read_tail_offset_x rb buf) = 
   CleanQ_RB_read_tail_offset_x rb (CleanQ_RB_read_tail_length_x rb buf)"
  by (simp add: CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_length_x_def)

lemma CleanQ_RB_read_tail_y_fields_commute1:
  "CleanQ_RB_read_tail_length_y rb (CleanQ_RB_read_tail_offset_y rb buf) = 
   CleanQ_RB_read_tail_offset_y rb (CleanQ_RB_read_tail_length_y rb buf)"
  by (simp add: CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_length_y_def)


paragraph \<open>Writing a Buffer\<close>

text \<open>
  Analogue to the read operation, we define the same functions to update the record
  fields in the ring buffer with the value.
\<close>

definition CleanQ_RB_write_head_region_x :: 
  "CleanQ_Buffer \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_region_x b rb = 
      rb \<lparr> rTXY := rb_write_head ((rb_read_head (rTXY rb))\<lparr> region := region b \<rparr>) 
                                 (rTXY rb) \<rparr>"

definition CleanQ_RB_write_head_region_y :: 
  "CleanQ_Buffer \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_region_y b rb = 
      rb \<lparr> rTYX := rb_write_head ((rb_read_head (rTYX rb))\<lparr> region := region b \<rparr>) 
                                 (rTYX rb) \<rparr>"

definition CleanQ_RB_write_head_offset_x :: 
  "CleanQ_Buffer \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_offset_x b rb = 
      rb \<lparr> rTXY := rb_write_head ((rb_read_head (rTXY rb))\<lparr> offset := offset b \<rparr>) 
                                 (rTXY rb) \<rparr>"

definition CleanQ_RB_write_head_offset_y :: 
  "CleanQ_Buffer \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_offset_y b rb = 
      rb \<lparr> rTYX := rb_write_head ((rb_read_head (rTYX rb))\<lparr> offset := offset b \<rparr>) 
                                 (rTYX rb) \<rparr>"

definition CleanQ_RB_write_head_length_x :: 
  "CleanQ_Buffer \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_length_x b rb = 
      rb \<lparr> rTXY := rb_write_head ((rb_read_head (rTXY rb))\<lparr> length := length b \<rparr>) 
                                 (rTXY rb) \<rparr>"

definition CleanQ_RB_write_head_length_y :: 
  "CleanQ_Buffer \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_length_y b rb = 
      rb \<lparr> rTYX := rb_write_head ((rb_read_head (rTYX rb))\<lparr> length := length b \<rparr>)
                                 (rTYX rb) \<rparr>"

definition CleanQ_RB_write_head_valid_offset_x :: 
  "CleanQ_Buffer \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_valid_offset_x b rb = 
      rb \<lparr> rTXY := rb_write_head ((rb_read_head (rTXY rb))\<lparr> valid_offset := valid_offset b \<rparr>) 
                                 (rTXY rb) \<rparr>"

definition CleanQ_RB_write_head_valid_offset_y :: 
  "CleanQ_Buffer \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_valid_offset_y b rb = 
      rb \<lparr> rTYX := rb_write_head ((rb_read_head (rTYX rb))\<lparr> valid_offset := valid_offset b \<rparr>) 
                                 (rTYX rb) \<rparr>"

definition CleanQ_RB_write_head_valid_length_x :: 
  "CleanQ_Buffer \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_valid_length_x b rb = 
      rb \<lparr> rTXY := rb_write_head ((rb_read_head (rTXY rb))\<lparr> valid_length := valid_length b \<rparr>) 
                                 (rTXY rb) \<rparr>"

definition CleanQ_RB_write_head_valid_length_y :: 
  "CleanQ_Buffer \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_valid_length_y b rb = 
      rb \<lparr> rTYX := rb_write_head ((rb_read_head (rTYX rb))\<lparr> valid_length := valid_length b \<rparr>) 
                                 (rTYX rb) \<rparr>"

definition CleanQ_RB_write_head_flags_x :: 
  "CleanQ_Buffer \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_flags_x b rb = 
      rb \<lparr> rTXY := rb_write_head ((rb_read_head (rTXY rb))\<lparr> flags := flags b \<rparr>) 
                                 (rTXY rb) \<rparr>"

definition CleanQ_RB_write_head_flags_y :: 
  "CleanQ_Buffer \<Rightarrow> CleanQ_Buffer CleanQ_RB_State \<Rightarrow> CleanQ_Buffer CleanQ_RB_State" 
  where "CleanQ_RB_write_head_flags_y b rb = 
      rb \<lparr> rTYX := rb_write_head ((rb_read_head (rTYX rb))\<lparr> flags := flags b \<rparr>) 
                                 (rTYX rb) \<rparr>"


text \<open>
  We can now show that writing all fields in the record is equivalent of writing the 
  head of the ring. We first show the equivalence when we update all fields in a 
  buffer record, this is the same as the buffer. 
\<close>

lemma CleanQ_Buffer_eq[simp]: 
  "b \<lparr>region := region buf, offset := offset buf,  length := length buf, 
      valid_offset := valid_offset buf,  valid_length := valid_length buf,           
      flags := flags buf\<rparr> = (buf::CleanQ_Buffer)"
  by(auto)


text \<open>
  Using this lemma, we can now show that writing all fields is equivalent to updating 
  the entire buffer record.
\<close>

lemma CleanQ_RB_write_head_x_fields_eq :
  "CleanQ_RB_write_head_flags_x buf
    (CleanQ_RB_write_head_valid_length_x buf
      (CleanQ_RB_write_head_valid_offset_x buf
        (CleanQ_RB_write_head_length_x buf
          (CleanQ_RB_write_head_offset_x buf
            (CleanQ_RB_write_head_region_x buf rb))))) 
   = CleanQ_RB_write_head_x buf rb"
  unfolding CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_region_x_def
    CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_def 
    CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_valid_length_x_def
    CleanQ_RB_write_head_flags_x_def 
  by(simp add:rb_write_head_def rb_read_head_def)

lemma CleanQ_RB_write_head_y_fields_eq :
  "CleanQ_RB_write_head_flags_y buf
    (CleanQ_RB_write_head_valid_length_y buf
      (CleanQ_RB_write_head_valid_offset_y buf
        (CleanQ_RB_write_head_length_y buf
          (CleanQ_RB_write_head_offset_y buf
            (CleanQ_RB_write_head_region_y buf rb))))) 
   = CleanQ_RB_write_head_y buf rb"
  unfolding CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_region_y_def
    CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_def 
    CleanQ_RB_write_head_valid_offset_y_def CleanQ_RB_write_head_valid_length_y_def
    CleanQ_RB_write_head_flags_y_def 
  by(simp add:rb_write_head_def rb_read_head_def)
  

text \<open>
  The read operations do commute. We just show this with an example, doing this for all
  pairs is similar. 
\<close>

lemma CleanQ_RB_write_head_x_fields_commute1:
  "CleanQ_RB_write_head_length_x buf (CleanQ_RB_write_head_offset_x buf rb) = 
   CleanQ_RB_write_head_offset_x buf (CleanQ_RB_write_head_length_x buf rb)"
  unfolding CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_offset_x_def
            rb_write_head_def rb_read_head_def
  by (simp, metis (no_types) CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) 
                             CleanQ_Buffer.update_convs(3))

lemma CleanQ_RB_write_head_y_fields_commute1:
  "CleanQ_RB_write_head_length_y buf (CleanQ_RB_write_head_offset_y buf rb) = 
   CleanQ_RB_write_head_offset_y buf (CleanQ_RB_write_head_length_y buf rb)"
  unfolding CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_offset_y_def
            rb_write_head_def rb_read_head_def
  by (simp, metis (no_types) CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) 
                             CleanQ_Buffer.update_convs(3))


(* ==================================================================================== *)
subsection \<open>Lemmas to Help with the Interference Proofs\<close>
(* ==================================================================================== *)

text \<open>
  We now prove lemmas which cover possible interference pairs in the proof. We generally
  add those to the simpset, as they are structured in a suitable way.
\<close>


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Reading Tail, Writing Head\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We now read the tail back when we write the record fields at the head. The 
  result is basically not changed. We do this for both sides symmetrically.
\<close>

paragraph \<open>Read Tail Y, Write Head X\<close>

lemma CleanQ_RB_read_tail_y_write_head_flags_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> 
  CleanQ_RB_read_tail_y (CleanQ_RB_write_head_flags_x f rb) = CleanQ_RB_read_tail_y rb "
  by (simp add: CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def 
                CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_read_tail_y_write_head_region_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> 
  CleanQ_RB_read_tail_y (CleanQ_RB_write_head_region_x f rb) = CleanQ_RB_read_tail_y rb "
  by (simp add: CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def 
                CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_read_tail_y_write_head_offset_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> 
  CleanQ_RB_read_tail_y (CleanQ_RB_write_head_offset_x f rb) = CleanQ_RB_read_tail_y rb "
  by (simp add: CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def 
                CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_read_tail_y_write_head_length_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> 
  CleanQ_RB_read_tail_y (CleanQ_RB_write_head_length_x f rb) = CleanQ_RB_read_tail_y rb "
  by (simp add: CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def 
                CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_read_tail_y_write_head_valid_length_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> 
  CleanQ_RB_read_tail_y (CleanQ_RB_write_head_valid_length_x f rb) = CleanQ_RB_read_tail_y rb "
  by (simp add: CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def 
                CleanQ_RB_write_head_valid_length_x_def)

lemma CleanQ_RB_read_tail_y_write_head_valid_offset_x:
  "CleanQ_RB_deq_y_possible rb \<Longrightarrow> 
  CleanQ_RB_read_tail_y (CleanQ_RB_write_head_valid_offset_x f rb) = CleanQ_RB_read_tail_y rb "
  by (simp add: CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def 
                CleanQ_RB_write_head_valid_offset_x_def)

lemmas CleanQ_RB_read_tail_y_write_head[simp] = 
     CleanQ_RB_read_tail_y_write_head_flags_x
     CleanQ_RB_read_tail_y_write_head_region_x
     CleanQ_RB_read_tail_y_write_head_offset_x
     CleanQ_RB_read_tail_y_write_head_length_x
     CleanQ_RB_read_tail_y_write_head_valid_length_x
     CleanQ_RB_read_tail_y_write_head_valid_offset_x


paragraph \<open>Read Tail X, Write Head Y\<close>

lemma CleanQ_RB_read_tail_x_write_head_flags_x:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> 
  CleanQ_RB_read_tail_x (CleanQ_RB_write_head_flags_y f rb) = CleanQ_RB_read_tail_x rb "
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_x_def 
                CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_read_tail_x_write_head_region_x:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> 
  CleanQ_RB_read_tail_x (CleanQ_RB_write_head_region_y f rb) = CleanQ_RB_read_tail_x rb "
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_x_def 
                CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_read_tail_x_write_head_offset_x:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> 
  CleanQ_RB_read_tail_x (CleanQ_RB_write_head_offset_y f rb) = CleanQ_RB_read_tail_x rb "
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_x_def 
                CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_read_tail_x_write_head_length_x:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> 
  CleanQ_RB_read_tail_x (CleanQ_RB_write_head_length_y f rb) = CleanQ_RB_read_tail_x rb "
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_x_def 
                CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_read_tail_x_write_head_valid_length_x:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> 
  CleanQ_RB_read_tail_x (CleanQ_RB_write_head_valid_length_y f rb) = CleanQ_RB_read_tail_x rb "
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_x_def 
                CleanQ_RB_write_head_valid_length_y_def)

lemma CleanQ_RB_read_tail_x_write_head_valid_offset_x:
  "CleanQ_RB_deq_x_possible rb \<Longrightarrow> 
  CleanQ_RB_read_tail_x (CleanQ_RB_write_head_valid_offset_y f rb) = CleanQ_RB_read_tail_x rb "
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_x_def 
                CleanQ_RB_write_head_valid_offset_y_def)

lemmas CleanQ_RB_read_tail_x_write_head[simp] = 
     CleanQ_RB_read_tail_x_write_head_flags_x
     CleanQ_RB_read_tail_x_write_head_region_x
     CleanQ_RB_read_tail_x_write_head_offset_x
     CleanQ_RB_read_tail_x_write_head_length_x
     CleanQ_RB_read_tail_x_write_head_valid_length_x
     CleanQ_RB_read_tail_x_write_head_valid_offset_x

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Reading Head, Writing  Head\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We now read the head back when we write the record fields at the head. The 
  result is basically not changed. We do this for both sides symmetrically. 
  It is not possible that those two operations interfere, so those proofs are 
  trivial.
\<close>

paragraph \<open>Read Head X, Write Head Y\<close>

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


paragraph \<open>Read Head Y, Write Head X\<close>

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


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Reading Head, Writing Tail\<close>
(* ------------------------------------------------------------------------------------ *)

paragraph \<open>Read Head X, Write Tail Y\<close>
paragraph \<open>Read Head Y, Write Tail X\<close>


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Reading Tail, Writing Tail\<close>
(* ------------------------------------------------------------------------------------ *)

paragraph \<open>Read Tail X, Write Tail Y\<close>
paragraph \<open>Read Tail Y, Write Tail X\<close>


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Reading Fields, Update Buffer Records\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  Reading back the buffer element which which has been written to yields the very same
  buffer element, except the field that has been updated. We now formulate lemmas that
  show that the other fields remain unchanged. 
\<close>

paragraph \<open>Length Head X Unchanged, Update Other Fields Head X\<close>

lemma CleanQ_RB_write_head_offset_x_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_x x rb)) 
      = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_region_x_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_x x rb)) 
      = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_flags_x_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_x x rb)) 
      = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_x x rb)) 
      = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_x x rb)) 
      = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_x_def)

lemmas CleanQ_RB_write_head_x_read_x_length_unchanged_simps[simp] = 
    CleanQ_RB_write_head_offset_x_read_x_length_unchanged
    CleanQ_RB_write_head_region_x_read_x_length_unchanged
    CleanQ_RB_write_head_flags_x_read_x_length_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_x_length_unchanged
    CleanQ_RB_write_head_valid_length_x_read_x_length_unchanged


paragraph \<open>Length Head Y Unchanged, Update Other Fields Head X\<close>

lemma CleanQ_RB_write_head_offset_x_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_x x rb)) 
      = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_region_x_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_x x rb)) 
      = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_flags_x_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_x x rb)) 
      = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_x x rb)) 
      = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_x x rb)) 
      = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_x_def)

lemmas CleanQ_RB_write_head_x_read_y_length_unchanged_simps[simp] = 
    CleanQ_RB_write_head_offset_x_read_y_length_unchanged
    CleanQ_RB_write_head_region_x_read_y_length_unchanged
    CleanQ_RB_write_head_flags_x_read_y_length_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_y_length_unchanged
    CleanQ_RB_write_head_valid_length_x_read_y_length_unchanged


paragraph \<open>Length Head Y Unchanged, Update Other Fields Head Y\<close>

lemma CleanQ_RB_write_head_offset_y_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_y x rb)) 
      = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_region_y_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_y x rb)) 
      = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_flags_y_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_y x rb)) 
      = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_y x rb)) 
      = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_y_length_unchanged:
  "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_y x rb)) 
      = length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_y_length_unchanged_simps[simp] = 
    CleanQ_RB_write_head_offset_y_read_y_length_unchanged
    CleanQ_RB_write_head_region_y_read_y_length_unchanged
    CleanQ_RB_write_head_flags_y_read_y_length_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_y_length_unchanged
    CleanQ_RB_write_head_valid_length_y_read_y_length_unchanged


paragraph \<open>Length Head X Unchanged, Update Other Fields Head Y\<close>

lemma CleanQ_RB_write_head_offset_y_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_y x rb)) 
      = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_region_y_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_y x rb)) 
      = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_flags_y_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_y x rb)) 
      = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_y x rb)) 
      = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_x_length_unchanged:
  "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_y x rb)) 
      = length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_x_length_unchanged_simps[simp] = 
    CleanQ_RB_write_head_offset_y_read_x_length_unchanged
    CleanQ_RB_write_head_region_y_read_x_length_unchanged
    CleanQ_RB_write_head_flags_y_read_x_length_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_x_length_unchanged
    CleanQ_RB_write_head_valid_length_y_read_x_length_unchanged


paragraph \<open>Offset Head X Unchanged, Update Other Fields Head X\<close>

lemma CleanQ_RB_write_head_length_x_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_x x rb)) 
      = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_region_x_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_x x rb)) 
      = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_flags_x_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_x x rb)) 
      = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_x x rb)) 
      = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_x x rb)) 
    = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_x_def)
 
lemmas CleanQ_RB_write_head_x_read_x_offset_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_x_offset_unchanged
    CleanQ_RB_write_head_region_x_read_x_offset_unchanged
    CleanQ_RB_write_head_flags_x_read_x_offset_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_x_offset_unchanged
    CleanQ_RB_write_head_valid_length_x_read_x_offset_unchanged


paragraph \<open>Offset Head Y Unchanged, Update Other Fields Head X\<close>

lemma CleanQ_RB_write_head_length_x_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_x x rb)) 
      = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_region_x_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_x x rb)) 
      = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_flags_x_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_x x rb)) 
      = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_x x rb)) 
      = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_x x rb)) 
      = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_x_def)

lemmas CleanQ_RB_write_head_x_read_y_offset_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_y_offset_unchanged
    CleanQ_RB_write_head_region_x_read_y_offset_unchanged
    CleanQ_RB_write_head_flags_x_read_y_offset_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_y_offset_unchanged
    CleanQ_RB_write_head_valid_length_x_read_y_offset_unchanged


paragraph \<open>Offset Head Y Unchanged, Update Other Fields Head Y\<close>

lemma CleanQ_RB_write_head_length_y_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_y x rb)) 
      = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_region_y_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_y x rb)) 
      = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_flags_y_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_y x rb)) 
      = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_y x rb)) 
      = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_y_offset_unchanged:
  "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_y x rb)) 
      = offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_y_offset_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_y_offset_unchanged
    CleanQ_RB_write_head_region_y_read_y_offset_unchanged
    CleanQ_RB_write_head_flags_y_read_y_offset_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_y_offset_unchanged
    CleanQ_RB_write_head_valid_length_y_read_y_offset_unchanged


paragraph \<open>Offset Head X Unchanged, Update Other Fields Head Y\<close>

lemma CleanQ_RB_write_head_length_y_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_y x rb)) 
      = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_region_y_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_y x rb)) 
      = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_flags_y_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_y x rb)) 
      = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_y x rb)) 
      = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_x_offset_unchanged:
  "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_y x rb)) 
      = offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_x_offset_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_x_offset_unchanged
    CleanQ_RB_write_head_region_y_read_x_offset_unchanged
    CleanQ_RB_write_head_flags_y_read_x_offset_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_x_offset_unchanged
    CleanQ_RB_write_head_valid_length_y_read_x_offset_unchanged


paragraph \<open>Flags Head X Unchanged, Update Other Fields Head X\<close>

lemma CleanQ_RB_write_head_length_x_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_x x rb)) 
    = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_region_x_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_x x rb)) 
    = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_offset_x_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_x x rb)) 
    = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_x x rb)) 
    = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_x x rb)) 
    = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_x_def)
  
lemmas CleanQ_RB_write_head_x_read_x_flags_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_x_flags_unchanged
    CleanQ_RB_write_head_region_x_read_x_flags_unchanged
    CleanQ_RB_write_head_offset_x_read_x_flags_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_x_flags_unchanged
    CleanQ_RB_write_head_valid_length_x_read_x_flags_unchanged

paragraph \<open>Flags Head Y Unchanged, Update Other Fields Head X\<close>

lemma CleanQ_RB_write_head_length_x_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_x x rb)) 
    = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_region_x_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_x x rb)) 
    = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_offset_x_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_x x rb)) 
    = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_x x rb)) 
    = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_x x rb)) 
    = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_x_def)

lemmas CleanQ_RB_write_head_x_read_y_flags_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_y_flags_unchanged
    CleanQ_RB_write_head_region_x_read_y_flags_unchanged
    CleanQ_RB_write_head_offset_x_read_y_flags_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_y_flags_unchanged
    CleanQ_RB_write_head_valid_length_x_read_y_flags_unchanged


paragraph \<open>Flags Head Y Unchanged, Update Other Fields Head Y\<close>

lemma CleanQ_RB_write_head_length_y_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_y x rb)) 
    = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_region_y_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_y x rb)) 
    = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_offset_y_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_y x rb)) 
    = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_y x rb)) 
    = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_y_flags_unchanged:
  "flags (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_y x rb)) 
    = flags (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_y_flags_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_y_flags_unchanged
    CleanQ_RB_write_head_region_y_read_y_flags_unchanged
    CleanQ_RB_write_head_offset_y_read_y_flags_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_y_flags_unchanged
    CleanQ_RB_write_head_valid_length_y_read_y_flags_unchanged


paragraph \<open>Flags Head X Unchanged, Update Other Fields Head Y\<close>

lemma CleanQ_RB_write_head_length_y_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_y x rb)) 
    = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_region_y_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_y x rb)) 
    = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_offset_y_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_y x rb)) 
    = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_y x rb))
    = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_x_flags_unchanged:
  "flags (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_y x rb)) 
    = flags (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_x_flags_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_x_flags_unchanged
    CleanQ_RB_write_head_region_y_read_x_flags_unchanged
    CleanQ_RB_write_head_offset_y_read_x_flags_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_x_flags_unchanged
    CleanQ_RB_write_head_valid_length_y_read_x_flags_unchanged


paragraph \<open>Region Head X Unchanged, Update Other Fields Head X\<close>

lemma CleanQ_RB_write_head_length_x_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_x x rb)) 
    = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_flags_x_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_x x rb)) 
    = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_offset_x_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_x x rb)) 
    = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_x x rb)) 
    = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_x x rb)) 
    = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_x_def)
  
lemmas CleanQ_RB_write_head_x_read_x_region_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_x_region_unchanged
    CleanQ_RB_write_head_flags_x_read_x_region_unchanged
    CleanQ_RB_write_head_offset_x_read_x_region_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_x_region_unchanged
    CleanQ_RB_write_head_valid_length_x_read_x_region_unchanged


paragraph \<open>Region Head Y Unchanged, Update Other Fields Head X\<close>

lemma CleanQ_RB_write_head_length_x_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_x x rb)) 
    = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_flags_x_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_x x rb)) 
    = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_offset_x_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_x x rb)) 
    = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_x x rb)) 
    = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_x x rb)) 
    = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_x_def)

lemmas CleanQ_RB_write_head_x_read_y_region_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_y_region_unchanged
    CleanQ_RB_write_head_flags_x_read_y_region_unchanged
    CleanQ_RB_write_head_offset_x_read_y_region_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_y_region_unchanged
    CleanQ_RB_write_head_valid_length_x_read_y_region_unchanged


paragraph \<open>Region Head Y Unchanged, Update Other Fields Head Y\<close>

lemma CleanQ_RB_write_head_length_y_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_y x rb)) 
    = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_flags_y_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_y x rb)) 
    = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_offset_y_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_y x rb)) 
    = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_y x rb)) 
    = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_y_region_unchanged:
  "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_y x rb)) 
    = region (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_y_region_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_y_region_unchanged
    CleanQ_RB_write_head_flags_y_read_y_region_unchanged
    CleanQ_RB_write_head_offset_y_read_y_region_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_y_region_unchanged
    CleanQ_RB_write_head_valid_length_y_read_y_region_unchanged


paragraph \<open>Region Head X Unchanged, Update Other Fields Head Y\<close>

lemma CleanQ_RB_write_head_length_y_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_y x rb)) 
    = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_flags_y_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_y x rb)) 
    = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_offset_y_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_y x rb)) 
    = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_y x rb)) 
    = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_x_region_unchanged:
  "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_y x rb)) 
    = region (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_x_region_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_x_region_unchanged
    CleanQ_RB_write_head_flags_y_read_x_region_unchanged
    CleanQ_RB_write_head_offset_y_read_x_region_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_x_region_unchanged
    CleanQ_RB_write_head_valid_length_y_read_x_region_unchanged


paragraph \<open>Valid Offset Head X Unchanged, Update Other Fields Head X\<close>

lemma CleanQ_RB_write_head_length_x_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_x x rb)) 
    = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_flags_x_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_x x rb)) 
    = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_offset_x_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_x x rb)) 
    = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_region_x_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_x x rb)) 
    = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_x x rb)) 
    = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_x_def)
 
lemmas CleanQ_RB_write_head_x_read_x_valid_offset_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_x_valid_offset_unchanged
    CleanQ_RB_write_head_flags_x_read_x_valid_offset_unchanged
    CleanQ_RB_write_head_offset_x_read_x_valid_offset_unchanged
    CleanQ_RB_write_head_region_x_read_x_valid_offset_unchanged
    CleanQ_RB_write_head_valid_length_x_read_x_valid_offset_unchanged


paragraph \<open>Valid Offset Head Y Unchanged, Update Other Fields Head X\<close>

lemma CleanQ_RB_write_head_length_x_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_x x rb)) 
    = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_flags_x_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_x x rb)) 
    = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_offset_x_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_x x rb)) 
    = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_region_x_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_x x rb)) 
    = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_valid_length_x_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_x x rb)) 
    = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_x_def)

lemmas CleanQ_RB_write_head_x_read_y_valid_offset_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_y_valid_offset_unchanged
    CleanQ_RB_write_head_flags_x_read_y_valid_offset_unchanged
    CleanQ_RB_write_head_offset_x_read_y_valid_offset_unchanged
    CleanQ_RB_write_head_region_x_read_y_valid_offset_unchanged
    CleanQ_RB_write_head_valid_length_x_read_y_valid_offset_unchanged


paragraph \<open>Valid Offset Head Y Unchanged, Update Other Fields Head Y\<close>

lemma CleanQ_RB_write_head_length_y_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_y x rb)) 
    = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_flags_y_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_y x rb)) 
    = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_offset_y_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_y x rb)) 
    = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_region_y_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_y x rb)) 
    = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_y_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_y x rb)) 
    = valid_offset (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_y_valid_offset_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_y_valid_offset_unchanged
    CleanQ_RB_write_head_flags_y_read_y_valid_offset_unchanged
    CleanQ_RB_write_head_offset_y_read_y_valid_offset_unchanged
    CleanQ_RB_write_head_region_y_read_y_valid_offset_unchanged
    CleanQ_RB_write_head_valid_length_y_read_y_valid_offset_unchanged


paragraph \<open>Valid Offset Head X Unchanged, Update Other Fields Head Y\<close>

lemma CleanQ_RB_write_head_length_y_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_y x rb)) 
    = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_flags_y_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_y x rb)) 
    = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_offset_y_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_y x rb)) 
    = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_region_y_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_y x rb)) 
    = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_valid_length_y_read_x_valid_offset_unchanged:
  "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_y x rb)) 
    = valid_offset (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_write_head_y_read_x_valid_offset_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_x_valid_offset_unchanged
    CleanQ_RB_write_head_flags_y_read_x_valid_offset_unchanged
    CleanQ_RB_write_head_offset_y_read_x_valid_offset_unchanged
    CleanQ_RB_write_head_region_y_read_x_valid_offset_unchanged
    CleanQ_RB_write_head_valid_length_y_read_x_valid_offset_unchanged


paragraph \<open>Valid Length Head X Unchanged, Update Other Fields Head X\<close>

lemma CleanQ_RB_write_head_length_x_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_x x rb)) 
    = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_flags_x_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_x x rb)) 
    = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_offset_x_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_x x rb)) 
    = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_region_x_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_x x rb)) 
    = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_x x rb)) 
    = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_x_def)

lemmas CleanQ_RB_write_head_x_read_x_valid_length_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_x_valid_length_unchanged
    CleanQ_RB_write_head_flags_x_read_x_valid_length_unchanged
    CleanQ_RB_write_head_offset_x_read_x_valid_length_unchanged
    CleanQ_RB_write_head_region_x_read_x_valid_length_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_x_valid_length_unchanged


paragraph \<open>Valid Length Head Y Unchanged, Update Other Fields Head X\<close>

lemma CleanQ_RB_write_head_length_x_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_x x rb)) 
    = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_flags_x_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_x x rb)) 
    = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_offset_x_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_x x rb)) 
    = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_region_x_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_x x rb)) 
    = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_x x rb)) 
    = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_x_def)

lemmas CleanQ_RB_write_head_x_read_y_valid_length_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_x_read_y_valid_length_unchanged
    CleanQ_RB_write_head_flags_x_read_y_valid_length_unchanged
    CleanQ_RB_write_head_offset_x_read_y_valid_length_unchanged
    CleanQ_RB_write_head_region_x_read_y_valid_length_unchanged
    CleanQ_RB_write_head_valid_offset_x_read_y_valid_length_unchanged


paragraph \<open>Valid Length Head Y Unchanged, Update Other Fields Head Y\<close>

lemma CleanQ_RB_write_head_length_y_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_y x rb)) 
    = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_flags_y_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_y x rb)) 
    = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_offset_y_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_y x rb)) 
    = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_region_y_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_y x rb)) 
    = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_y_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_y x rb)) 
    = valid_length (CleanQ_RB_read_head_y rb)"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_y_def)

lemmas CleanQ_RB_write_head_y_read_y_valid_length_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_y_valid_length_unchanged
    CleanQ_RB_write_head_flags_y_read_y_valid_length_unchanged
    CleanQ_RB_write_head_offset_y_read_y_valid_length_unchanged
    CleanQ_RB_write_head_region_y_read_y_valid_length_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_y_valid_length_unchanged


paragraph \<open>Valid Length Head X Unchanged, Update Other Fields Head Y\<close>

lemma CleanQ_RB_write_head_length_y_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_y x rb)) 
    = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_flags_y_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_y x rb)) 
    = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_offset_y_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_y x rb)) 
    = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_region_y_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_y x rb)) 
    = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_read_x_valid_length_unchanged:
  "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_y x rb)) 
    = valid_length (CleanQ_RB_read_head_x rb)"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemmas CleanQ_RB_write_head_y_read_x_valid_length_unchanged_simps[simp] = 
    CleanQ_RB_write_head_length_y_read_x_valid_length_unchanged
    CleanQ_RB_write_head_flags_y_read_x_valid_length_unchanged
    CleanQ_RB_write_head_offset_y_read_x_valid_length_unchanged
    CleanQ_RB_write_head_region_y_read_x_valid_length_unchanged
    CleanQ_RB_write_head_valid_offset_y_read_x_valid_length_unchanged


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Write Head Fields Preserves Invariant\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  Writing the buffer fields in the ring does not change the state of the w.r.t. the 
  buffer ownership and thus the Invariant is preserved. We show this for all updates 
  to the head buffer element. 
\<close>

paragraph \<open>Write Head X Fields Preserve Invariant\<close>

lemma CleanQ_RB_write_head_x_offset_inv:
  "CleanQ_RB_Invariants K rb 
    \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_offset_x x rb)"
  by (metis CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_Invariant 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_x_length_inv:
  "CleanQ_RB_Invariants K rb 
    \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_length_x x rb)"
  by (metis CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_Invariant 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_x_region_inv:
  "CleanQ_RB_Invariants K rb 
    \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_region_x x rb)"
  by (metis CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_Invariant 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_x_valid_length_inv:
  "CleanQ_RB_Invariants K rb 
    \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_valid_length_x x rb)"
  by (metis CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_Invariant 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_x_valid_offset_inv:
  "CleanQ_RB_Invariants K rb 
    \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_valid_offset_x x rb)"
  by (metis CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_Invariant 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_x_flags_inv:
  "CleanQ_RB_Invariants K rb 
    \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_flags_x x rb)"
  by (metis CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_Invariant 
            CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_write_head_x_invariant[simp] = 
   CleanQ_RB_write_head_x_offset_inv
   CleanQ_RB_write_head_x_length_inv
   CleanQ_RB_write_head_x_region_inv
   CleanQ_RB_write_head_x_valid_length_inv
   CleanQ_RB_write_head_x_valid_offset_inv
   CleanQ_RB_write_head_x_flags_inv


paragraph \<open>Write Head Y Fields Preserve Invariant\<close>

lemma CleanQ_RB_write_head_y_offset_inv:
  "CleanQ_RB_Invariants K rb 
    \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_offset_y x rb)"
  by (metis CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_y_Invariant 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_y_length_inv:
  "CleanQ_RB_Invariants K rb 
    \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_length_y x rb)"
  by (metis CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_Invariant 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_y_region_inv:
  "CleanQ_RB_Invariants K rb 
    \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_region_y x rb)"
  by (metis CleanQ_RB_write_head_region_y_def CleanQ_RB_write_head_y_Invariant 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_y_valid_length_inv:
  "CleanQ_RB_Invariants K rb 
    \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_valid_length_y x rb)"
  by (metis CleanQ_RB_write_head_valid_length_y_def CleanQ_RB_write_head_y_Invariant 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_y_valid_offset_inv:
  "CleanQ_RB_Invariants K rb 
    \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_valid_offset_y x rb)"
  by (metis CleanQ_RB_write_head_valid_offset_y_def CleanQ_RB_write_head_y_Invariant 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_y_flags_inv:
  "CleanQ_RB_Invariants K rb 
    \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_flags_y x rb)"
  by (metis CleanQ_RB_write_head_flags_y_def CleanQ_RB_write_head_y_Invariant 
            CleanQ_RB_write_head_y_def)

lemmas CleanQ_RB_write_head_y_invariant[simp] = 
   CleanQ_RB_write_head_y_offset_inv
   CleanQ_RB_write_head_y_length_inv
   CleanQ_RB_write_head_y_region_inv
   CleanQ_RB_write_head_y_valid_length_inv
   CleanQ_RB_write_head_y_valid_offset_inv
   CleanQ_RB_write_head_y_flags_inv


paragraph \<open>Enqueue and Dequeue Preserves Inveraint\<close>

lemma CleanQ_RB_deq_x_invariant:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> CleanQ_RB_deq_x_possible rb 
      \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_deq_x rb)"
  using CleanQ_RB_deq_x_all_inv by blast

lemma CleanQ_RB_deq_y_invariant:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> CleanQ_RB_deq_y_possible rb 
      \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_deq_y rb)"
  using CleanQ_RB_deq_y_all_inv by blast

lemma CleanQ_RB_enq_x_invariant:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> CleanQ_RB_enq_x_possible rb \<Longrightarrow> b \<in> rSX rb
      \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_enq_x b rb)"
  by (meson CleanQ_RB_enq_x_inv_all)
  
lemma CleanQ_RB_enq_y_invariant:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> CleanQ_RB_enq_y_possible rb \<Longrightarrow> b \<in> rSY rb
      \<Longrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_enq_y b rb)"
  by (meson CleanQ_RB_enq_y_inv_all)

lemmas CleanQ_RB_enq_deq_inv_simps[simp] = 
    CleanQ_RB_deq_x_invariant
    CleanQ_RB_deq_y_invariant
    CleanQ_RB_enq_x_invariant
    CleanQ_RB_enq_y_invariant

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Preserving the Enq/Deq Possible Predicate\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  Writing the buffer fields does not change the state of the predicates whether an 
  enqueue or dequeue is possible.
\<close>


paragraph \<open>Enqueue X Possible, Write Head X\<close>

lemma CleanQ_RB_write_head_length_x_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_length_x x rb) 
    = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_can_enq_x 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_offset_x_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_offset_x x rb) 
    = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_can_enq_x 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_region_x_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_region_x x rb) 
    = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_can_enq_x 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_flags_x_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_flags_x x rb) 
    = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_can_enq_x 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_length_x_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_valid_length_x x rb) 
    = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_can_enq_x 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_valid_offset_x x rb) 
    = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_can_enq_x 
            CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_write_head_x_enq_x_possible[simp] = 
   CleanQ_RB_write_head_length_x_enq_x_possible
   CleanQ_RB_write_head_offset_x_enq_x_possible
   CleanQ_RB_write_head_region_x_enq_x_possible
   CleanQ_RB_write_head_flags_x_enq_x_possible
   CleanQ_RB_write_head_valid_length_x_enq_x_possible
   CleanQ_RB_write_head_valid_offset_x_enq_x_possible


paragraph \<open>Enqueue Y Possible, Write Head Y\<close>

lemma CleanQ_RB_write_head_length_y_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_length_y x rb) 
    = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_can_enq_y 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_offset_y_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_offset_y x rb) 
    = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_y_can_enq_y 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_region_y_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_region_y x rb) 
    = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_region_y_def CleanQ_RB_write_head_y_can_enq_y  
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_flags_y_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_flags_y x rb) 
    = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_flags_y_def CleanQ_RB_write_head_y_can_enq_y 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_length_y_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_valid_length_y x rb) 
    = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_valid_length_y_def CleanQ_RB_write_head_y_can_enq_y 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_valid_offset_y x rb) 
    = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_valid_offset_y_def CleanQ_RB_write_head_y_can_enq_y 
            CleanQ_RB_write_head_y_def)

lemmas CleanQ_RB_write_head_y_enq_y_possible[simp] = 
   CleanQ_RB_write_head_length_y_enq_y_possible
   CleanQ_RB_write_head_offset_y_enq_y_possible
   CleanQ_RB_write_head_region_y_enq_y_possible
   CleanQ_RB_write_head_flags_y_enq_y_possible
   CleanQ_RB_write_head_valid_length_y_enq_y_possible
   CleanQ_RB_write_head_valid_offset_y_enq_y_possible


paragraph \<open>Enqueue X Possible, Write Head Y\<close>

lemma CleanQ_RB_write_head_length_y_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_length_y x rb) 
    = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_can_enq_x 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_offset_y_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_offset_y x rb) 
    = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_y_can_enq_x 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_region_y_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_region_y x rb) 
    = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_region_y_def CleanQ_RB_write_head_y_can_enq_x 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_flags_y_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_flags_y x rb) 
    = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_flags_y_def CleanQ_RB_write_head_y_can_enq_x 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_length_y_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_valid_length_y x rb) 
    = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_valid_length_y_def CleanQ_RB_write_head_y_can_enq_x 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_enq_x_possible:
  "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_valid_offset_y x rb) 
    = CleanQ_RB_enq_x_possible rb"
  by (metis CleanQ_RB_write_head_valid_offset_y_def CleanQ_RB_write_head_y_can_enq_x 
            CleanQ_RB_write_head_y_def)

lemmas CleanQ_RB_write_head_y_enq_x_possible[simp] = 
   CleanQ_RB_write_head_length_y_enq_x_possible
   CleanQ_RB_write_head_offset_y_enq_x_possible
   CleanQ_RB_write_head_region_y_enq_x_possible
   CleanQ_RB_write_head_flags_y_enq_x_possible
   CleanQ_RB_write_head_valid_length_y_enq_x_possible
   CleanQ_RB_write_head_valid_offset_y_enq_x_possible


paragraph \<open>Enqueue Y Possible, Write Head X\<close>

lemma CleanQ_RB_write_head_length_x_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_length_x x rb) 
    = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_can_enq_y 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_offset_x_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_offset_x x rb) 
    = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_can_enq_y 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_region_x_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_region_x x rb) 
    = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_can_enq_y 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_flags_x_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_flags_x x rb) 
    = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_can_enq_y 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_length_x_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_valid_length_x x rb) 
    = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_can_enq_y 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_enq_y_possible:
  "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_valid_offset_x x rb) 
    = CleanQ_RB_enq_y_possible rb"
  by (metis CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_can_enq_y 
            CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_write_head_x_enq_y_possible[simp] = 
   CleanQ_RB_write_head_length_x_enq_y_possible
   CleanQ_RB_write_head_offset_x_enq_y_possible
   CleanQ_RB_write_head_region_x_enq_y_possible
   CleanQ_RB_write_head_flags_x_enq_y_possible
   CleanQ_RB_write_head_valid_length_x_enq_y_possible
   CleanQ_RB_write_head_valid_offset_x_enq_y_possible


paragraph \<open>Dequeue X Possible, Write Head X\<close>

lemma CleanQ_RB_write_head_length_x_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_length_x x rb) 
    = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_can_deq_x 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_offset_x_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_offset_x x rb) 
    = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_can_deq_x 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_region_x_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_region_x x rb) 
    = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_can_deq_x 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_flags_x_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_flags_x x rb) 
    = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_can_deq_x 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_length_x_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_valid_length_x x rb) 
    = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_can_deq_x 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_valid_offset_x x rb) 
    = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_can_deq_x 
            CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_write_head_x_deq_x_possible[simp] = 
   CleanQ_RB_write_head_length_x_deq_x_possible
   CleanQ_RB_write_head_offset_x_deq_x_possible
   CleanQ_RB_write_head_region_x_deq_x_possible
   CleanQ_RB_write_head_flags_x_deq_x_possible
   CleanQ_RB_write_head_valid_length_x_deq_x_possible
   CleanQ_RB_write_head_valid_offset_x_deq_x_possible


paragraph \<open>Dequeue Y Possible, Write Head Y\<close>

lemma CleanQ_RB_write_head_length_y_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_length_y x rb) 
    = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_can_deq_y 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_offset_y_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_offset_y x rb) 
    = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_y_can_deq_y 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_region_y_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_region_y x rb) 
    = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_region_y_def CleanQ_RB_write_head_y_can_deq_y 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_flags_y_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_flags_y x rb) 
    = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_flags_y_def CleanQ_RB_write_head_y_can_deq_y 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_length_y_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_valid_length_y x rb) 
    = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_valid_length_y_def CleanQ_RB_write_head_y_can_deq_y 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_valid_offset_y x rb) 
    = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_valid_offset_y_def CleanQ_RB_write_head_y_can_deq_y 
            CleanQ_RB_write_head_y_def)

lemmas CleanQ_RB_write_head_y_deq_y_possible[simp] = 
   CleanQ_RB_write_head_length_y_deq_y_possible
   CleanQ_RB_write_head_offset_y_deq_y_possible
   CleanQ_RB_write_head_region_y_deq_y_possible
   CleanQ_RB_write_head_flags_y_deq_y_possible
   CleanQ_RB_write_head_valid_length_y_deq_y_possible
   CleanQ_RB_write_head_valid_offset_y_deq_y_possible


paragraph \<open>Dequeue X Possible, Write Head Y\<close>

lemma CleanQ_RB_write_head_length_y_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_length_y x rb) 
    = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_length_y_def CleanQ_RB_write_head_y_can_deq_x 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_offset_y_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_offset_y x rb) 
    = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_offset_y_def CleanQ_RB_write_head_y_can_deq_x 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_region_y_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_region_y x rb) 
    = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_region_y_def CleanQ_RB_write_head_y_can_deq_x 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_flags_y_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_flags_y x rb) 
    = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_flags_y_def CleanQ_RB_write_head_y_can_deq_x 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_length_y_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_valid_length_y x rb) 
    = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_valid_length_y_def CleanQ_RB_write_head_y_can_deq_x 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_deq_x_possible:
  "CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_valid_offset_y x rb) 
    = CleanQ_RB_deq_x_possible rb"
  by (metis CleanQ_RB_write_head_valid_offset_y_def CleanQ_RB_write_head_y_can_deq_x 
            CleanQ_RB_write_head_y_def)

lemmas CleanQ_RB_write_head_y_deq_x_possible[simp] = 
   CleanQ_RB_write_head_length_y_deq_x_possible
   CleanQ_RB_write_head_offset_y_deq_x_possible
   CleanQ_RB_write_head_region_y_deq_x_possible
   CleanQ_RB_write_head_flags_y_deq_x_possible
   CleanQ_RB_write_head_valid_length_y_deq_x_possible
   CleanQ_RB_write_head_valid_offset_y_deq_x_possible

paragraph \<open>Dequeue Y Possible, Write Head X\<close>

lemma CleanQ_RB_write_head_length_x_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_length_x x rb) 
    = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_can_deq_y 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_offset_x_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_offset_x x rb) 
    = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_can_deq_y 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_region_x_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_region_x x rb) 
    = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_can_deq_y 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_flags_x_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_flags_x x rb) 
    = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_can_deq_y 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_length_x_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_valid_length_x x rb) 
    = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_can_deq_y 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_deq_y_possible:
  "CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_valid_offset_x x rb) 
    = CleanQ_RB_deq_y_possible rb"
  by (metis CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_can_deq_y 
            CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_write_head_x_deq_y_possible[simp] = 
   CleanQ_RB_write_head_length_x_deq_y_possible
   CleanQ_RB_write_head_offset_x_deq_y_possible
   CleanQ_RB_write_head_region_x_deq_y_possible
   CleanQ_RB_write_head_flags_x_deq_y_possible
   CleanQ_RB_write_head_valid_length_x_deq_y_possible
   CleanQ_RB_write_head_valid_offset_x_deq_y_possible


paragraph \<open>Full Enqueue/Dequeue Preserves Enqueue/Dequeue Possible\<close>

text \<open>
  Enqueue and dequeue of a buffer on one side, does not change whether the other side
  can enqeuue or dequeue respectively. 
\<close>

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





(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Writing the Head Preserves SX and SY\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  Simply updating a field of a buffer in the ring does not transfer the ownership as the
  head is not part of the owning set. Thus SX and SY is not changed. 
\<close>

paragraph \<open>Write Head X Preserves SX\<close>

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


paragraph \<open>Write Head Y Preserves SX\<close>

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


paragraph \<open>Write Head Y Preserves SY\<close>

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


paragraph \<open>Write Head Y Preserves SY\<close>

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


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Nested Reading of Tail Element\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  Reading the buffer fields in a nested fashion does not change the result, its the 
  same as if read is carried out single handedly.
\<close>

paragraph \<open>Nested Reading Valid Length X\<close>

lemma CleanQ_RB_read_tail_region_x_valid_length_x:
 "b = CleanQ_RB_read_tail_region_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_region_x rb (CleanQ_RB_read_tail_valid_length_x rb b) 
          = CleanQ_RB_read_tail_valid_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(5) 
            CleanQ_RB_read_tail_region_x_def CleanQ_RB_read_tail_valid_length_x_def)

lemma CleanQ_RB_read_tail_offset_x_valid_length_x:
  "b = CleanQ_RB_read_tail_offset_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_x rb (CleanQ_RB_read_tail_valid_length_x rb b) 
          = CleanQ_RB_read_tail_valid_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(5) 
            CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_valid_length_x_def)

lemma CleanQ_RB_read_tail_flags_x_valid_length_x:
  "b = CleanQ_RB_read_tail_flags_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_x rb (CleanQ_RB_read_tail_valid_length_x rb b) 
          = CleanQ_RB_read_tail_valid_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(5) CleanQ_Buffer.update_convs(6) 
            CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_valid_length_x_def)

lemma CleanQ_RB_read_tail_length_x_valid_length_x:
  "b = CleanQ_RB_read_tail_length_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_length_x rb (CleanQ_RB_read_tail_valid_length_x rb b) 
          = CleanQ_RB_read_tail_valid_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(5) 
            CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_valid_length_x_def)

lemma CleanQ_RB_read_tail_valid_offset_x_valid_length_x:
  "b = CleanQ_RB_read_tail_valid_offset_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x rb (CleanQ_RB_read_tail_valid_length_x rb b) 
          = CleanQ_RB_read_tail_valid_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(5) 
            CleanQ_RB_read_tail_valid_length_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemma CleanQ_RB_read_tail_valid_length_x_valid_length_x:
  "CleanQ_RB_read_tail_valid_length_x rb (CleanQ_RB_read_tail_valid_length_x rb b) 
    = CleanQ_RB_read_tail_valid_length_x rb b"
  by (simp add: CleanQ_RB_read_tail_valid_length_x_def)

lemmas CleanQ_RB_read_tail_x_simps[simp] = 
  CleanQ_RB_read_tail_region_x_valid_length_x
  CleanQ_RB_read_tail_length_x_valid_length_x
  CleanQ_RB_read_tail_flags_x_valid_length_x
  CleanQ_RB_read_tail_offset_x_valid_length_x
  CleanQ_RB_read_tail_valid_offset_x_valid_length_x
  CleanQ_RB_read_tail_valid_length_x_valid_length_x


paragraph \<open>Nested Reading Valid Length Y\<close>

lemma CleanQ_RB_read_tail_region_y_valid_length_y:
 "b = CleanQ_RB_read_tail_region_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_region_y rb (CleanQ_RB_read_tail_valid_length_y rb b) 
          = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) 
            CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_region_y_def 
            CleanQ_RB_read_tail_valid_length_y_def)

lemma CleanQ_RB_read_tail_offset_y_valid_length_y:
  "b = CleanQ_RB_read_tail_offset_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_y rb (CleanQ_RB_read_tail_valid_length_y rb b) 
          = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) 
            CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_offset_y_def 
            CleanQ_RB_read_tail_valid_length_y_def)

lemma CleanQ_RB_read_tail_flags_y_valid_length_y:
  "b = CleanQ_RB_read_tail_flags_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_y rb (CleanQ_RB_read_tail_valid_length_y rb b) 
          = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(5) 
            CleanQ_Buffer.update_convs(6) CleanQ_RB_read_tail_flags_y_def 
            CleanQ_RB_read_tail_valid_length_y_def)

lemma CleanQ_RB_read_tail_length_y_valid_length_y:
  "b = CleanQ_RB_read_tail_length_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_length_y rb (CleanQ_RB_read_tail_valid_length_y rb b) 
          = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) 
            CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_length_y_def 
            CleanQ_RB_read_tail_valid_length_y_def)

lemma CleanQ_RB_read_tail_valid_offset_y_valid_length_y:
  "b = CleanQ_RB_read_tail_valid_offset_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y rb (CleanQ_RB_read_tail_valid_length_y rb b) 
          = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) 
            CleanQ_Buffer.update_convs(5) CleanQ_RB_read_tail_valid_length_y_def 
            CleanQ_RB_read_tail_valid_offset_y_def)

lemma CleanQ_RB_read_tail_valid_length_y_valid_length_y:
  "CleanQ_RB_read_tail_valid_length_y rb (CleanQ_RB_read_tail_valid_length_y rb b)
       = CleanQ_RB_read_tail_valid_length_y rb b"
  by (simp add: CleanQ_RB_read_tail_valid_length_y_def)

lemmas CleanQ_RB_read_tail_valid_length_y_simps[simp] = 
  CleanQ_RB_read_tail_region_y_valid_length_y
  CleanQ_RB_read_tail_length_y_valid_length_y
  CleanQ_RB_read_tail_flags_y_valid_length_y
  CleanQ_RB_read_tail_offset_y_valid_length_y
  CleanQ_RB_read_tail_valid_offset_y_valid_length_y
  CleanQ_RB_read_tail_valid_length_y_valid_length_y


paragraph \<open>Nested Reading Valid Length X\<close>

lemma CleanQ_RB_read_tail_region_x_valid_offset_x:
 "b = CleanQ_RB_read_tail_region_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_region_x rb (CleanQ_RB_read_tail_valid_offset_x rb b) 
          = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(4) 
            CleanQ_RB_read_tail_region_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemma CleanQ_RB_read_tail_offset_x_valid_offset_x:
  "b = CleanQ_RB_read_tail_offset_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_x rb (CleanQ_RB_read_tail_valid_offset_x rb b) 
          = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(4) 
            CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemma CleanQ_RB_read_tail_flags_x_valid_offset_x:
  "b = CleanQ_RB_read_tail_flags_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_x rb (CleanQ_RB_read_tail_valid_offset_x rb b) 
          = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(6) 
            CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemma CleanQ_RB_read_tail_length_x_valid_offset_x:
  "b = CleanQ_RB_read_tail_length_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_length_x rb (CleanQ_RB_read_tail_valid_offset_x rb b) 
          = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(4) 
            CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemma CleanQ_RB_read_tail_valid_length_x_valid_offset_x:
  "b = CleanQ_RB_read_tail_valid_length_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x rb (CleanQ_RB_read_tail_valid_offset_x rb b) 
          = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(5) 
            CleanQ_RB_read_tail_valid_length_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemma CleanQ_RB_read_tail_valid_offset_x_valid_offset_x:
  "CleanQ_RB_read_tail_valid_offset_x rb (CleanQ_RB_read_tail_valid_offset_x rb b) 
    = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (simp add: CleanQ_RB_read_tail_valid_offset_x_def)

lemmas CleanQ_RB_read_tail_valid_offset_x_simps[simp] = 
  CleanQ_RB_read_tail_region_x_valid_offset_x
  CleanQ_RB_read_tail_length_x_valid_offset_x
  CleanQ_RB_read_tail_flags_x_valid_offset_x
  CleanQ_RB_read_tail_offset_x_valid_offset_x
  CleanQ_RB_read_tail_valid_length_x_valid_offset_x
  CleanQ_RB_read_tail_valid_offset_x_valid_offset_x


paragraph \<open>Nested Reading Valid Offset Y\<close>

lemma CleanQ_RB_read_tail_region_y_valid_offset_y:
 "b = CleanQ_RB_read_tail_region_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_region_y rb (CleanQ_RB_read_tail_valid_offset_y rb b) 
          = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(4) 
            CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemma CleanQ_RB_read_tail_offset_y_valid_offset_y:
  "b = CleanQ_RB_read_tail_offset_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_y rb (CleanQ_RB_read_tail_valid_offset_y rb b) 
          = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(4) 
            CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemma CleanQ_RB_read_tail_flags_y_valid_offset_y:
  "b = CleanQ_RB_read_tail_flags_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_y rb (CleanQ_RB_read_tail_valid_offset_y rb b) 
          = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(6) 
            CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemma CleanQ_RB_read_tail_length_y_valid_offset_y:
  "b = CleanQ_RB_read_tail_length_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_length_y rb (CleanQ_RB_read_tail_valid_offset_y rb b) 
          = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(4) 
            CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemma CleanQ_RB_read_tail_valid_length_y_valid_offset_y:
  "b = CleanQ_RB_read_tail_valid_length_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y rb (CleanQ_RB_read_tail_valid_offset_y rb b) 
          = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(5) 
            CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemma CleanQ_RB_read_tail_valid_offset_y_valid_offset_y:
  "CleanQ_RB_read_tail_valid_offset_y rb (CleanQ_RB_read_tail_valid_offset_y rb b) 
    = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (simp add: CleanQ_RB_read_tail_valid_offset_y_def)

lemmas CleanQ_RB_read_tail_valid_offset_y_simps[simp] = 
  CleanQ_RB_read_tail_region_y_valid_offset_y
  CleanQ_RB_read_tail_length_y_valid_offset_y
  CleanQ_RB_read_tail_flags_y_valid_offset_y
  CleanQ_RB_read_tail_offset_y_valid_offset_y
  CleanQ_RB_read_tail_valid_offset_y_valid_offset_y
  CleanQ_RB_read_tail_valid_length_y_valid_offset_y


paragraph \<open>Nested Reading Tail Y\<close>

lemma CleanQ_RB_read_tail_region_y_length_y:
 "b = CleanQ_RB_read_tail_region_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_region_y rb (CleanQ_RB_read_tail_length_y rb b) 
          = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(3) 
            CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_region_y_def)

lemma CleanQ_RB_read_tail_offset_y_length_y:
  "b = CleanQ_RB_read_tail_offset_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_y rb (CleanQ_RB_read_tail_length_y rb b) 
          = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(3) 
            CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_offset_y_def)

lemma CleanQ_RB_read_tail_flags_y_length_y:
  "b = CleanQ_RB_read_tail_flags_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_y rb (CleanQ_RB_read_tail_length_y rb b) 
          = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(6) 
            CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_length_y_def)

lemma CleanQ_RB_read_tail_valid_offset_y_length_y:
  "b = CleanQ_RB_read_tail_valid_offset_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y rb (CleanQ_RB_read_tail_length_y rb b) 
          = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_Buffer.cases_scheme CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(4) 
            CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemma CleanQ_RB_read_tail_valid_length_y_length_y:
  "b = CleanQ_RB_read_tail_valid_length_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y rb (CleanQ_RB_read_tail_length_y rb b) 
          = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(5) 
            CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_valid_length_y_def)

lemma CleanQ_RB_read_tail_length_y_length_y:
  "CleanQ_RB_read_tail_length_y rb (CleanQ_RB_read_tail_length_y rb b) 
    = CleanQ_RB_read_tail_length_y rb b"
  by (simp add: CleanQ_RB_read_tail_length_y_def)

lemmas CleanQ_RB_read_tail_length_y_simps[simp] = 
  CleanQ_RB_read_tail_region_y_length_y
  CleanQ_RB_read_tail_length_y_length_y
  CleanQ_RB_read_tail_flags_y_length_y
  CleanQ_RB_read_tail_offset_y_length_y
  CleanQ_RB_read_tail_valid_offset_y_length_y
  CleanQ_RB_read_tail_valid_length_y_length_y


paragraph \<open>Nested Reading Tail X\<close>

lemma CleanQ_RB_read_tail_region_x_length_x:
 "b = CleanQ_RB_read_tail_region_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_region_x rb (CleanQ_RB_read_tail_length_x rb b) 
          = CleanQ_RB_read_tail_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(3) 
            CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_region_x_def)

lemma CleanQ_RB_read_tail_offset_x_length_x:
  "b = CleanQ_RB_read_tail_offset_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_x rb (CleanQ_RB_read_tail_length_x rb b) 
          = CleanQ_RB_read_tail_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(3) 
              CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_offset_x_def)

lemma CleanQ_RB_read_tail_flags_x_length_x:
  "b = CleanQ_RB_read_tail_flags_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_x rb (CleanQ_RB_read_tail_length_x rb b) 
          = CleanQ_RB_read_tail_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(6) 
              CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_length_x_def)

lemma CleanQ_RB_read_tail_valid_offset_x_length_x:
  "b = CleanQ_RB_read_tail_valid_offset_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x rb (CleanQ_RB_read_tail_length_x rb b) 
          = CleanQ_RB_read_tail_length_x rb b"
  by (metis CleanQ_Buffer.cases_scheme CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(4) 
            CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemma CleanQ_RB_read_tail_valid_length_x_length_x:
  "b = CleanQ_RB_read_tail_valid_length_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x rb (CleanQ_RB_read_tail_length_x rb b) 
          = CleanQ_RB_read_tail_length_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(5) 
            CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_valid_length_x_def)

lemma CleanQ_RB_read_tail_length_x_length_x:
  "CleanQ_RB_read_tail_length_x rb (CleanQ_RB_read_tail_length_x rb b) 
    = CleanQ_RB_read_tail_length_x rb b"
  by (simp add: CleanQ_RB_read_tail_length_x_def)

lemmas CleanQ_RB_read_tail_length_x_simps[simp] = 
  CleanQ_RB_read_tail_region_x_length_x
  CleanQ_RB_read_tail_length_x_length_x
  CleanQ_RB_read_tail_flags_x_length_x
  CleanQ_RB_read_tail_offset_x_length_x
  CleanQ_RB_read_tail_valid_offset_x_length_x
  CleanQ_RB_read_tail_valid_length_x_length_x

paragraph \<open>Nested Reading Offset Y\<close>

lemma CleanQ_RB_read_tail_region_y_offset_y:
 "b = CleanQ_RB_read_tail_region_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_region_y rb (CleanQ_RB_read_tail_offset_y rb b) 
          = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_Buffer.simps(8) CleanQ_Buffer.simps(9) CleanQ_Buffer.surjective 
            CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_region_y_def)

lemma CleanQ_RB_read_tail_offset_y_offset_y:
  "CleanQ_RB_read_tail_offset_y rb (CleanQ_RB_read_tail_offset_y rb b) 
    = CleanQ_RB_read_tail_offset_y rb b"
  by(simp add:CleanQ_RB_read_tail_offset_y_def)

lemma CleanQ_RB_read_tail_flags_y_offset_y:
  "b = CleanQ_RB_read_tail_flags_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_y rb (CleanQ_RB_read_tail_offset_y rb b) 
        = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_Buffer.simps(13) CleanQ_Buffer.simps(9) CleanQ_Buffer.surjective 
            CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_offset_y_def)
  
lemma CleanQ_RB_read_tail_length_y_offset_y:
  "b = CleanQ_RB_read_tail_length_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_length_y rb (CleanQ_RB_read_tail_offset_y rb b) 
          = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_Buffer.cases_scheme CleanQ_Buffer.simps(10) CleanQ_Buffer.simps(9) 
            CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_offset_y_def)

lemma CleanQ_RB_read_tail_valid_length_y_offset_y:
  "b = CleanQ_RB_read_tail_valid_length_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y rb (CleanQ_RB_read_tail_offset_y rb b) 
          = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(5) 
            CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_valid_length_y_def)

lemma CleanQ_RB_read_tail_valid_offset_y_offset_y:
  "b = CleanQ_RB_read_tail_valid_offset_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y rb (CleanQ_RB_read_tail_offset_y rb b) 
          = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(4) 
            CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemmas CleanQ_RB_read_tail_offset_y_simps[simp] = 
    CleanQ_RB_read_tail_region_y_offset_y
    CleanQ_RB_read_tail_length_y_offset_y
    CleanQ_RB_read_tail_flags_y_offset_y
    CleanQ_RB_read_tail_offset_y_offset_y
    CleanQ_RB_read_tail_valid_length_y_offset_y
    CleanQ_RB_read_tail_valid_offset_y_offset_y


paragraph \<open>Nested Reading Offset X\<close>

lemma CleanQ_RB_read_tail_region_x_offset_x:
 "b = CleanQ_RB_read_tail_region_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_region_x rb (CleanQ_RB_read_tail_offset_x rb b) 
          = CleanQ_RB_read_tail_offset_x rb b"
  by (metis CleanQ_Buffer.simps(8) CleanQ_Buffer.simps(9) CleanQ_Buffer.surjective 
            CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_region_x_def)

lemma CleanQ_RB_read_tail_offset_x_offset_x:
  "CleanQ_RB_read_tail_offset_x rb (CleanQ_RB_read_tail_offset_x rb b) 
    = CleanQ_RB_read_tail_offset_x rb b"
  by(simp add:CleanQ_RB_read_tail_offset_x_def)

lemma CleanQ_RB_read_tail_flags_x_offset_x:
  "b = CleanQ_RB_read_tail_flags_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_x rb (CleanQ_RB_read_tail_offset_x rb b) 
          = CleanQ_RB_read_tail_offset_x rb b"
  by (metis CleanQ_Buffer.simps(13) CleanQ_Buffer.simps(9) CleanQ_Buffer.surjective 
            CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_offset_x_def)
  
lemma CleanQ_RB_read_tail_length_x_offset_x:
  "b = CleanQ_RB_read_tail_length_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_length_x rb (CleanQ_RB_read_tail_offset_x rb b) 
          = CleanQ_RB_read_tail_offset_x rb b"
  by (metis CleanQ_Buffer.cases_scheme CleanQ_Buffer.simps(10) CleanQ_Buffer.simps(9) 
            CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_offset_x_def)

lemma CleanQ_RB_read_tail_valid_length_x_offset_x:
  "b = CleanQ_RB_read_tail_valid_length_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x rb (CleanQ_RB_read_tail_offset_x rb b) 
          = CleanQ_RB_read_tail_offset_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(5) 
            CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_valid_length_x_def)

lemma CleanQ_RB_read_tail_valid_offset_x_offset_x:
  "b = CleanQ_RB_read_tail_valid_offset_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x rb (CleanQ_RB_read_tail_offset_x rb b) 
          = CleanQ_RB_read_tail_offset_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(4) 
            CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemmas CleanQ_RB_read_tail_offset_x_simps[simp] = 
    CleanQ_RB_read_tail_region_x_offset_x
    CleanQ_RB_read_tail_length_x_offset_x
    CleanQ_RB_read_tail_flags_x_offset_x
    CleanQ_RB_read_tail_offset_x_offset_x
    CleanQ_RB_read_tail_valid_length_x_offset_x
    CleanQ_RB_read_tail_valid_offset_x_offset_x


paragraph \<open>Nested Reading Region Y\<close>

lemma CleanQ_RB_read_tail_region_y_region_y:
 "CleanQ_RB_read_tail_region_y rb (CleanQ_RB_read_tail_region_y rb b) 
    = CleanQ_RB_read_tail_region_y rb b"
  by(simp add:CleanQ_RB_read_tail_region_y_def)

lemma CleanQ_RB_read_tail_offset_y_region_y:
  "b = CleanQ_RB_read_tail_offset_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_y rb (CleanQ_RB_read_tail_region_y rb b) 
          = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_Buffer.cases_scheme CleanQ_Buffer.simps(8) CleanQ_Buffer.simps(9) 
            CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_region_y_def)

lemma CleanQ_RB_read_tail_flags_y_region_y:
  "b = CleanQ_RB_read_tail_flags_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_y rb (CleanQ_RB_read_tail_region_y rb b) 
          = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_Buffer.simps(13) CleanQ_Buffer.simps(8) CleanQ_Buffer.surjective 
            CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_region_y_def)
  
lemma CleanQ_RB_read_tail_length_y_region_y:
  "b = CleanQ_RB_read_tail_length_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_length_y rb (CleanQ_RB_read_tail_region_y rb b) 
          = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(3) 
              CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_region_y_def)

lemma CleanQ_RB_read_tail_valid_length_y_region_y:
  "b = CleanQ_RB_read_tail_valid_length_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y rb (CleanQ_RB_read_tail_region_y rb b) 
          = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(5) 
            CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_valid_length_y_def)

lemma CleanQ_RB_read_tail_valid_offset_y_region_y:
  "b = CleanQ_RB_read_tail_valid_offset_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y rb (CleanQ_RB_read_tail_region_y rb b) 
          = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(4) 
            CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemmas CleanQ_RB_read_tail_region_y_simps[simp] = 
  CleanQ_RB_read_tail_region_y_region_y
  CleanQ_RB_read_tail_length_y_region_y
  CleanQ_RB_read_tail_flags_y_region_y
  CleanQ_RB_read_tail_offset_y_region_y
  CleanQ_RB_read_tail_valid_length_y_region_y
  CleanQ_RB_read_tail_valid_offset_y_region_y

paragraph \<open>Nested Reading Region X\<close>

lemma CleanQ_RB_read_tail_region_x_region_x:
 "CleanQ_RB_read_tail_region_x rb (CleanQ_RB_read_tail_region_x rb b) 
    = CleanQ_RB_read_tail_region_x rb b"
  by(simp add:CleanQ_RB_read_tail_region_x_def)

lemma CleanQ_RB_read_tail_offset_x_region_x:
  "b = CleanQ_RB_read_tail_offset_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_x rb (CleanQ_RB_read_tail_region_x rb b) 
          = CleanQ_RB_read_tail_region_x rb b"
  by (metis CleanQ_Buffer.cases_scheme CleanQ_Buffer.simps(8) CleanQ_Buffer.simps(9) 
            CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_region_x_def)

lemma CleanQ_RB_read_tail_flags_x_region_x:
  "b = CleanQ_RB_read_tail_flags_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_x rb (CleanQ_RB_read_tail_region_x rb b) 
          = CleanQ_RB_read_tail_region_x rb b"
  by (metis CleanQ_Buffer.simps(13) CleanQ_Buffer.simps(8) CleanQ_Buffer.surjective 
            CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_region_x_def)
  
lemma CleanQ_RB_read_tail_length_x_region_x:
  "b = CleanQ_RB_read_tail_length_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_length_x rb (CleanQ_RB_read_tail_region_x rb b) 
          = CleanQ_RB_read_tail_region_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(3) 
            CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_region_x_def)

lemma CleanQ_RB_read_tail_valid_length_x_region_x:
  "b = CleanQ_RB_read_tail_valid_length_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x rb (CleanQ_RB_read_tail_region_x rb b) 
          = CleanQ_RB_read_tail_region_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(5) 
            CleanQ_RB_read_tail_region_x_def CleanQ_RB_read_tail_valid_length_x_def)

lemma CleanQ_RB_read_tail_valid_offset_x_region_x:
  "b = CleanQ_RB_read_tail_valid_offset_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x rb (CleanQ_RB_read_tail_region_x rb b) 
          = CleanQ_RB_read_tail_region_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(4) 
            CleanQ_RB_read_tail_region_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemmas CleanQ_RB_read_tail_region_x_simps[simp] = 
  CleanQ_RB_read_tail_region_x_region_x
  CleanQ_RB_read_tail_length_x_region_x
  CleanQ_RB_read_tail_flags_x_region_x
  CleanQ_RB_read_tail_offset_x_region_x
  CleanQ_RB_read_tail_valid_length_x_region_x
  CleanQ_RB_read_tail_valid_offset_x_region_x


paragraph \<open>Nested Reading Flags Y\<close>

lemma CleanQ_RB_read_tail_flags_y_flags_y:
 "CleanQ_RB_read_tail_flags_y rb (CleanQ_RB_read_tail_flags_y rb b) 
    = CleanQ_RB_read_tail_flags_y rb b"
  by(simp add:CleanQ_RB_read_tail_flags_y_def)

lemma CleanQ_RB_read_tail_offset_y_flags_y:
  "b = CleanQ_RB_read_tail_offset_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_y rb (CleanQ_RB_read_tail_flags_y rb b) 
          = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(6) 
            CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_offset_y_def)

lemma CleanQ_RB_read_tail_region_y_flags_y:
  "b = CleanQ_RB_read_tail_region_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_region_y rb (CleanQ_RB_read_tail_flags_y rb b) 
          = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(6) 
            CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_region_y_def)
  
lemma CleanQ_RB_read_tail_length_y_flags_y:
  "b = CleanQ_RB_read_tail_length_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_length_y rb (CleanQ_RB_read_tail_flags_y rb b) 
          = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(6) 
            CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_length_y_def)

lemma CleanQ_RB_read_tail_valid_length_y_flags_y:
  "b = CleanQ_RB_read_tail_valid_length_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y rb (CleanQ_RB_read_tail_flags_y rb b) 
          = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(5) CleanQ_Buffer.update_convs(6) 
            CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_valid_length_y_def)

lemma CleanQ_RB_read_tail_valid_offset_y_flags_y:
  "b = CleanQ_RB_read_tail_valid_offset_y rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y rb (CleanQ_RB_read_tail_flags_y rb b) 
          = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(6) 
            CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_valid_offset_y_def)

lemmas CleanQ_RB_read_tail_flags_y_simps[simp] = 
  CleanQ_RB_read_tail_flags_y_flags_y
  CleanQ_RB_read_tail_length_y_flags_y
  CleanQ_RB_read_tail_region_y_flags_y
  CleanQ_RB_read_tail_offset_y_flags_y
  CleanQ_RB_read_tail_valid_length_y_flags_y
  CleanQ_RB_read_tail_valid_offset_y_flags_y


paragraph \<open>Nested Reading Flags X\<close>

lemma CleanQ_RB_read_tail_flags_x_flags_x:
 "CleanQ_RB_read_tail_flags_x rb (CleanQ_RB_read_tail_flags_x rb b) 
    = CleanQ_RB_read_tail_flags_x rb b"
  by(simp add:CleanQ_RB_read_tail_flags_x_def)

lemma CleanQ_RB_read_tail_offset_x_flags_x:
  "b = CleanQ_RB_read_tail_offset_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_x rb (CleanQ_RB_read_tail_flags_x rb b) 
          = CleanQ_RB_read_tail_flags_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(2) CleanQ_Buffer.update_convs(6) 
            CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_offset_x_def)

lemma CleanQ_RB_read_tail_region_x_flags_x:
  "b = CleanQ_RB_read_tail_region_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_region_x rb (CleanQ_RB_read_tail_flags_x rb b) 
          = CleanQ_RB_read_tail_flags_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(1) CleanQ_Buffer.update_convs(6) 
            CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_region_x_def)
  
lemma CleanQ_RB_read_tail_length_x_flags_x:
  "b = CleanQ_RB_read_tail_length_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_length_x rb (CleanQ_RB_read_tail_flags_x rb b) 
          = CleanQ_RB_read_tail_flags_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(3) CleanQ_Buffer.update_convs(6) 
            CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_length_x_def)

lemma CleanQ_RB_read_tail_valid_length_x_flags_x:
  "b = CleanQ_RB_read_tail_valid_length_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x rb (CleanQ_RB_read_tail_flags_x rb b) 
          = CleanQ_RB_read_tail_flags_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(5) CleanQ_Buffer.update_convs(6) 
            CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_valid_length_x_def)

lemma CleanQ_RB_read_tail_valid_offset_x_flags_x:
  "b = CleanQ_RB_read_tail_valid_offset_x rb b 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x rb (CleanQ_RB_read_tail_flags_x rb b) 
          = CleanQ_RB_read_tail_flags_x rb b"
  by (metis CleanQ_Buffer.surjective CleanQ_Buffer.update_convs(4) CleanQ_Buffer.update_convs(6) 
            CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_valid_offset_x_def)

lemmas CleanQ_RB_read_tail_flags_x_simps[simp] = 
  CleanQ_RB_read_tail_flags_x_flags_x
  CleanQ_RB_read_tail_length_x_flags_x
  CleanQ_RB_read_tail_region_x_flags_x
  CleanQ_RB_read_tail_offset_x_flags_x
  CleanQ_RB_read_tail_valid_length_x_flags_x
  CleanQ_RB_read_tail_valid_offset_x_flags_x


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Reading Tail Unchanged, Writing Head Other\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  Writing the head element of one side does not change the tail element on the other, 
  if there is already an element to be dequeued. 
\<close>

paragraph \<open>Read Tail Region Y Unchanged, Writes Head X\<close>

lemma CleanQ_RB_read_tail_region_y_write_flags_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_region_y (CleanQ_RB_write_head_flags_x f rb) b 
          = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_flags_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_region_y_write_region_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_region_y (CleanQ_RB_write_head_region_x f rb) b
          = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_region_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_region_y_write_offset_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_region_y (CleanQ_RB_write_head_offset_x f rb) b
          = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_offset_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_region_y_write_length_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_region_y (CleanQ_RB_write_head_length_x f rb) b
          = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_length_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_region_y_write_valid_offset_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_region_y (CleanQ_RB_write_head_valid_offset_x f rb) b
          = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_offset_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_region_y_write_valid_length_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_region_y (CleanQ_RB_write_head_valid_length_x f rb) b
          = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_length_x_def 
            CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_read_tail_region_y_write_x[simp] = 
     CleanQ_RB_read_tail_region_y_write_flags_x
     CleanQ_RB_read_tail_region_y_write_region_x
     CleanQ_RB_read_tail_region_y_write_offset_x
     CleanQ_RB_read_tail_region_y_write_length_x
     CleanQ_RB_read_tail_region_y_write_valid_offset_x
     CleanQ_RB_read_tail_region_y_write_valid_length_x


paragraph \<open>Read Tail Offset Y Unchanged, Writes Head X\<close>

lemma CleanQ_RB_read_tail_offset_y_write_flags_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_y (CleanQ_RB_write_head_flags_x f rb) b
          = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_flags_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_offset_y_write_region_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_y (CleanQ_RB_write_head_region_x f rb) b
          = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_region_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_offset_y_write_offset_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_y (CleanQ_RB_write_head_offset_x f rb) b
          = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_offset_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_offset_y_write_length_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_y (CleanQ_RB_write_head_length_x f rb) b
          = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_length_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_offset_y_write_valid_offset_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_y (CleanQ_RB_write_head_valid_offset_x f rb) b
          = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_offset_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_offset_y_write_valid_length_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_y (CleanQ_RB_write_head_valid_length_x f rb) b
          = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_length_x_def 
            CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_read_tail_offset_y_write_x[simp] = 
     CleanQ_RB_read_tail_offset_y_write_flags_x
     CleanQ_RB_read_tail_offset_y_write_region_x
     CleanQ_RB_read_tail_offset_y_write_offset_x
     CleanQ_RB_read_tail_offset_y_write_length_x
     CleanQ_RB_read_tail_offset_y_write_valid_offset_x
     CleanQ_RB_read_tail_offset_y_write_valid_length_x


paragraph \<open>Read Tail Length  Y Unchanged, Writes Head X\<close>

lemma CleanQ_RB_read_tail_length_y_write_flags_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_length_y (CleanQ_RB_write_head_flags_x f rb) b
          = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_flags_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_length_y_write_region_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_length_y (CleanQ_RB_write_head_region_x f rb) b
          = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_region_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_length_y_write_offset_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_length_y (CleanQ_RB_write_head_offset_x f rb) b
          = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_offset_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_length_y_write_length_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_length_y (CleanQ_RB_write_head_length_x f rb) b
          = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_length_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_length_y_write_valid_offset_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_length_y (CleanQ_RB_write_head_valid_offset_x f rb) b
          = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_offset_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_length_y_write_valid_length_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_length_y (CleanQ_RB_write_head_valid_length_x f rb) b
          = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_length_x_def 
            CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_read_tail_length_y_write_x[simp] = 
     CleanQ_RB_read_tail_length_y_write_flags_x
     CleanQ_RB_read_tail_length_y_write_region_x
     CleanQ_RB_read_tail_length_y_write_offset_x
     CleanQ_RB_read_tail_length_y_write_length_x
     CleanQ_RB_read_tail_length_y_write_valid_offset_x
     CleanQ_RB_read_tail_length_y_write_valid_length_x


paragraph \<open>Read Tail Flags Y Unchanged, Writes Head X\<close>

lemma CleanQ_RB_read_tail_flags_y_write_flags_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_y (CleanQ_RB_write_head_flags_x f rb) b
          = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_flags_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_flags_y_write_region_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_y (CleanQ_RB_write_head_region_x f rb) b
          = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_region_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_flags_y_write_offset_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_y (CleanQ_RB_write_head_offset_x f rb) b
          = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_offset_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_flags_y_write_length_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_y (CleanQ_RB_write_head_length_x f rb) b
          = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_length_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_flags_y_write_valid_offset_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_y (CleanQ_RB_write_head_valid_offset_x f rb) b
          = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_offset_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_flags_y_write_valid_length_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_y (CleanQ_RB_write_head_valid_length_x f rb) b
          = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_length_x_def 
            CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_read_tail_flags_y_write_x[simp] = 
     CleanQ_RB_read_tail_flags_y_write_flags_x
     CleanQ_RB_read_tail_flags_y_write_region_x
     CleanQ_RB_read_tail_flags_y_write_offset_x
     CleanQ_RB_read_tail_flags_y_write_length_x
     CleanQ_RB_read_tail_flags_y_write_valid_offset_x
     CleanQ_RB_read_tail_flags_y_write_valid_length_x


paragraph \<open>Read Tail Valid Offset Y Unchanged, Writes Head X\<close>

lemma CleanQ_RB_read_tail_valid_offset_y_write_flags_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y (CleanQ_RB_write_head_flags_x f rb) b
          = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_y_def 
            CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x 
            CleanQ_RB_write_head_flags_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_offset_y_write_region_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y (CleanQ_RB_write_head_region_x f rb) b
          = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_y_def 
            CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x 
            CleanQ_RB_write_head_region_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_offset_y_write_offset_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y (CleanQ_RB_write_head_offset_x f rb) b
          = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_y_def 
            CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x 
            CleanQ_RB_write_head_offset_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_offset_y_write_length_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y (CleanQ_RB_write_head_length_x f rb) b
          = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_y_def 
            CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x 
            CleanQ_RB_write_head_length_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_offset_y_write_valid_offset_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y (CleanQ_RB_write_head_valid_offset_x f rb) b
          = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_y_def 
            CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x 
            CleanQ_RB_write_head_valid_offset_x_def CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_offset_y_write_valid_length_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y (CleanQ_RB_write_head_valid_length_x f rb) b
          = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_y_def 
            CleanQ_RB_read_tail_y_def CleanQ_RB_read_tail_y_write_head_x 
            CleanQ_RB_write_head_valid_length_x_def CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_read_tail_valid_offset_y_write_x[simp] = 
     CleanQ_RB_read_tail_valid_offset_y_write_flags_x
     CleanQ_RB_read_tail_valid_offset_y_write_region_x
     CleanQ_RB_read_tail_valid_offset_y_write_offset_x
     CleanQ_RB_read_tail_valid_offset_y_write_length_x
     CleanQ_RB_read_tail_valid_offset_y_write_valid_offset_x
     CleanQ_RB_read_tail_valid_offset_y_write_valid_length_x


paragraph \<open>Read Tail Valid Length Y Unchanged, Writes Head X\<close>

lemma CleanQ_RB_read_tail_valid_length_y_write_flags_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y (CleanQ_RB_write_head_flags_x f rb) b
          = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_flags_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_length_y_write_region_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y (CleanQ_RB_write_head_region_x f rb) b
          = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_region_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_length_y_write_offset_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y (CleanQ_RB_write_head_offset_x f rb) b
          = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_offset_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_length_y_write_length_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y (CleanQ_RB_write_head_length_x f rb) b
          = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_length_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_length_y_write_valid_offset_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y (CleanQ_RB_write_head_valid_offset_x f rb) b
          = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_offset_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_read_tail_valid_length_y_write_valid_length_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y (CleanQ_RB_write_head_valid_length_x f rb) b
          = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_write_head_x CleanQ_RB_write_head_valid_length_x_def 
            CleanQ_RB_write_head_x_def)

lemmas CleanQ_RB_read_tail_valid_length_y_write_x[simp] = 
     CleanQ_RB_read_tail_valid_length_y_write_flags_x
     CleanQ_RB_read_tail_valid_length_y_write_region_x
     CleanQ_RB_read_tail_valid_length_y_write_offset_x
     CleanQ_RB_read_tail_valid_length_y_write_length_x
     CleanQ_RB_read_tail_valid_length_y_write_valid_offset_x
     CleanQ_RB_read_tail_valid_length_y_write_valid_length_x



paragraph \<open>Read Tail Valid Length X Unchanged, Writes Head Y\<close>

lemma CleanQ_RB_read_tail_valid_length_x_write_flags_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x (CleanQ_RB_write_head_flags_y f rb) b 
          = CleanQ_RB_read_tail_valid_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_length_x_def 
                CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_read_tail_valid_length_x_write_region_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x (CleanQ_RB_write_head_region_y f rb) b 
          = CleanQ_RB_read_tail_valid_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_length_x_def 
                CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_read_tail_valid_length_x_write_offset_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x (CleanQ_RB_write_head_offset_y f rb) b 
          = CleanQ_RB_read_tail_valid_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_length_x_def 
                CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_read_tail_valid_length_x_write_length_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x (CleanQ_RB_write_head_length_y f rb) b 
          = CleanQ_RB_read_tail_valid_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_length_x_def 
                CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_read_tail_valid_length_x_write_valid_offset_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x (CleanQ_RB_write_head_valid_offset_y f rb) b 
          = CleanQ_RB_read_tail_valid_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_length_x_def 
                CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_read_tail_valid_length_x_write_valid_length_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x (CleanQ_RB_write_head_valid_length_y f rb) b 
          = CleanQ_RB_read_tail_valid_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_length_x_def 
                CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_read_tail_valid_length_x_write_y[simp] = 
     CleanQ_RB_read_tail_valid_length_x_write_flags_y
     CleanQ_RB_read_tail_valid_length_x_write_region_y
     CleanQ_RB_read_tail_valid_length_x_write_offset_y
     CleanQ_RB_read_tail_valid_length_x_write_length_y
     CleanQ_RB_read_tail_valid_length_x_write_valid_offset_y
     CleanQ_RB_read_tail_valid_length_x_write_valid_length_y


paragraph \<open>Read Tail Valid Offset X Unchanged, Writes Head Y\<close>

lemma CleanQ_RB_read_tail_valid_offset_x_write_flags_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x (CleanQ_RB_write_head_flags_y f rb) b 
          = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_offset_x_def 
                CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_read_tail_valid_offset_x_write_region_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x (CleanQ_RB_write_head_region_y f rb) b 
          = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_offset_x_def 
                CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_read_tail_valid_offset_x_write_offset_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x (CleanQ_RB_write_head_offset_y f rb) b 
          = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_offset_x_def 
                CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_read_tail_valid_offset_x_write_length_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x (CleanQ_RB_write_head_length_y f rb) b 
          = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_offset_x_def 
                CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_read_tail_valid_offset_x_write_valid_offset_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x (CleanQ_RB_write_head_valid_offset_y f rb) b 
          = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_offset_x_def 
                CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_read_tail_valid_offset_x_write_valid_length_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x (CleanQ_RB_write_head_valid_length_y f rb) b 
          = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_valid_offset_x_def 
                CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_read_tail_valid_offset_x_write_y[simp] = 
     CleanQ_RB_read_tail_valid_offset_x_write_flags_y
     CleanQ_RB_read_tail_valid_offset_x_write_region_y
     CleanQ_RB_read_tail_valid_offset_x_write_offset_y
     CleanQ_RB_read_tail_valid_offset_x_write_length_y
     CleanQ_RB_read_tail_valid_offset_x_write_valid_offset_y
     CleanQ_RB_read_tail_valid_offset_x_write_valid_length_y

paragraph \<open>Read Tail Flags X Unchanged, Writes Head Y\<close>

lemma CleanQ_RB_read_tail_flags_x_write_flags_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_x (CleanQ_RB_write_head_flags_y f rb) b 
          = CleanQ_RB_read_tail_flags_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_flags_x_def 
                CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_read_tail_flags_x_write_region_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_x (CleanQ_RB_write_head_region_y f rb) b 
          = CleanQ_RB_read_tail_flags_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_flags_x_def 
                CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_read_tail_flags_x_write_offset_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_x (CleanQ_RB_write_head_offset_y f rb) b 
          = CleanQ_RB_read_tail_flags_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_flags_x_def 
                CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_read_tail_flags_x_write_length_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_x (CleanQ_RB_write_head_length_y f rb) b 
          = CleanQ_RB_read_tail_flags_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_flags_x_def 
                CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_read_tail_flags_x_write_valid_offset_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_x (CleanQ_RB_write_head_valid_offset_y f rb) b 
          = CleanQ_RB_read_tail_flags_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_flags_x_def 
                CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_read_tail_flags_x_write_valid_length_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_x (CleanQ_RB_write_head_valid_length_y f rb) b 
          = CleanQ_RB_read_tail_flags_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_flags_x_def 
                CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_read_tail_flags_x_write_y[simp] = 
     CleanQ_RB_read_tail_flags_x_write_flags_y
     CleanQ_RB_read_tail_flags_x_write_region_y
     CleanQ_RB_read_tail_flags_x_write_offset_y
     CleanQ_RB_read_tail_flags_x_write_length_y
     CleanQ_RB_read_tail_flags_x_write_valid_offset_y
     CleanQ_RB_read_tail_flags_x_write_valid_length_y

paragraph \<open>Read Tail Offset X Unchanged, Writes Head Y\<close>

lemma CleanQ_RB_read_tail_offset_x_write_flags_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_x (CleanQ_RB_write_head_flags_y f rb) b 
          = CleanQ_RB_read_tail_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_offset_x_def 
                CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_read_tail_offset_x_write_region_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_x (CleanQ_RB_write_head_region_y f rb) b 
          = CleanQ_RB_read_tail_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_offset_x_def 
                CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_read_tail_offset_x_write_offset_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_x (CleanQ_RB_write_head_offset_y f rb) b 
          = CleanQ_RB_read_tail_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_offset_x_def 
                CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_read_tail_offset_x_write_length_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_x (CleanQ_RB_write_head_length_y f rb) b 
          = CleanQ_RB_read_tail_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_offset_x_def 
                CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_read_tail_offset_x_write_valid_offset_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_x (CleanQ_RB_write_head_valid_offset_y f rb) b 
          = CleanQ_RB_read_tail_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_offset_x_def 
                CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_read_tail_offset_x_write_valid_length_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_x (CleanQ_RB_write_head_valid_length_y f rb) b 
            = CleanQ_RB_read_tail_offset_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_offset_x_def 
                CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_read_tail_offset_x_write_y[simp] = 
     CleanQ_RB_read_tail_offset_x_write_flags_y
     CleanQ_RB_read_tail_offset_x_write_region_y
     CleanQ_RB_read_tail_offset_x_write_offset_y
     CleanQ_RB_read_tail_offset_x_write_length_y
     CleanQ_RB_read_tail_offset_x_write_valid_offset_y
     CleanQ_RB_read_tail_offset_x_write_valid_length_y

paragraph \<open>Read Tail Length X Unchanged, Writes Head Y\<close>

lemma CleanQ_RB_read_tail_length_x_write_flags_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_length_x (CleanQ_RB_write_head_flags_y f rb) b 
          = CleanQ_RB_read_tail_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_length_x_def 
                CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_read_tail_length_x_write_region_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_length_x (CleanQ_RB_write_head_region_y f rb) b 
          = CleanQ_RB_read_tail_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_length_x_def 
                CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_read_tail_length_x_write_offset_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_length_x (CleanQ_RB_write_head_offset_y f rb) b 
          = CleanQ_RB_read_tail_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_length_x_def 
                CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_read_tail_length_x_write_length_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_length_x (CleanQ_RB_write_head_length_y f rb) b 
          = CleanQ_RB_read_tail_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_length_x_def 
                CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_read_tail_length_x_write_valid_offset_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_length_x (CleanQ_RB_write_head_valid_offset_y f rb) b 
          = CleanQ_RB_read_tail_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_length_x_def 
                CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_read_tail_length_x_write_valid_length_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_length_x (CleanQ_RB_write_head_valid_length_y f rb) b 
          = CleanQ_RB_read_tail_length_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_length_x_def 
                CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_read_tail_length_x_write_y[simp] = 
     CleanQ_RB_read_tail_length_x_write_flags_y
     CleanQ_RB_read_tail_length_x_write_region_y
     CleanQ_RB_read_tail_length_x_write_offset_y
     CleanQ_RB_read_tail_length_x_write_length_y
     CleanQ_RB_read_tail_length_x_write_valid_offset_y
     CleanQ_RB_read_tail_length_x_write_valid_length_y


paragraph \<open>Read Tail Region X Unchanged, Writes Head Y\<close>

lemma CleanQ_RB_read_tail_region_x_write_flags_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_region_x (CleanQ_RB_write_head_flags_y f rb) b 
          = CleanQ_RB_read_tail_region_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_region_x_def 
                CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_read_tail_region_x_write_region_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_region_x (CleanQ_RB_write_head_region_y f rb) b 
          = CleanQ_RB_read_tail_region_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_region_x_def 
                CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_read_tail_region_x_write_offset_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_region_x (CleanQ_RB_write_head_offset_y f rb) b 
          = CleanQ_RB_read_tail_region_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_region_x_def 
                CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_read_tail_region_x_write_length_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_region_x (CleanQ_RB_write_head_length_y f rb) b 
          = CleanQ_RB_read_tail_region_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_region_x_def 
                CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_read_tail_region_x_write_valid_offset_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_region_x (CleanQ_RB_write_head_valid_offset_y f rb) b 
          = CleanQ_RB_read_tail_region_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_region_x_def 
                CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_read_tail_region_x_write_valid_length_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_region_x (CleanQ_RB_write_head_valid_length_y f rb) b 
          = CleanQ_RB_read_tail_region_x rb b"
  by (simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_read_tail_region_x_def 
                CleanQ_RB_write_head_valid_length_y_def)

lemmas CleanQ_RB_read_tail_region_x_write_y[simp] = 
     CleanQ_RB_read_tail_region_x_write_flags_y
     CleanQ_RB_read_tail_region_x_write_region_y
     CleanQ_RB_read_tail_region_x_write_offset_y
     CleanQ_RB_read_tail_region_x_write_length_y
     CleanQ_RB_read_tail_region_x_write_valid_offset_y
     CleanQ_RB_read_tail_region_x_write_valid_length_y


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Reading Tail, Writing Head\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  Not just writing a single element preserves reading the tail field, this is also the
  case when we do a full enqueue or dequeue operation. We show this for both operations
  and sides.
\<close>

paragraph \<open>Read Tail  Y, Enqueue X\<close>


lemma CleanQ_RB_read_tail_region_y_enq_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_region_y (CleanQ_RB_enq_x b2 rb) b 
          = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_enq_x)

lemma CleanQ_RB_read_tail_offset_y_enq_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_y (CleanQ_RB_enq_x b2 rb) b 
          = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_enq_x)

lemma CleanQ_RB_read_tail_length_y_enq_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_length_y (CleanQ_RB_enq_x b2 rb) b 
          = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_enq_x)

lemma CleanQ_RB_read_tail_flags_y_enq_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_y (CleanQ_RB_enq_x b2 rb) b 
          = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_enq_x)

lemma CleanQ_RB_read_tail_valid_offset_y_enq_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y (CleanQ_RB_enq_x b2 rb) b 
          = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_enq_x)

lemma CleanQ_RB_read_tail_valid_length_y_enq_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y (CleanQ_RB_enq_x b2 rb) b 
          = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_enq_x)

lemmas CleanQ_RB_read_tail__y_enq_x_simps[simp] = 
     CleanQ_RB_read_tail_region_y_enq_x
     CleanQ_RB_read_tail_offset_y_enq_x
     CleanQ_RB_read_tail_length_y_enq_x
     CleanQ_RB_read_tail_flags_y_enq_x
     CleanQ_RB_read_tail_valid_offset_y_enq_x
     CleanQ_RB_read_tail_valid_length_y_enq_x


paragraph \<open>Read Tail X, Enqueue YX\<close>

lemma CleanQ_RB_read_tail_region_x_enq_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_region_x (CleanQ_RB_enq_y b2 rb) b 
          = CleanQ_RB_read_tail_region_x rb b"
  by (metis CleanQ_RB_read_tail_region_x_def CleanQ_RB_read_tail_x_def 
            CleanQ_RB_read_tail_x_enq_y)

lemma CleanQ_RB_read_tail_offset_x_enq_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_x (CleanQ_RB_enq_y b2 rb) b 
          = CleanQ_RB_read_tail_offset_x rb b"
  by (metis CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_x_def 
            CleanQ_RB_read_tail_x_enq_y)

lemma CleanQ_RB_read_tail_length_x_enq_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_length_x (CleanQ_RB_enq_y b2 rb) b 
          = CleanQ_RB_read_tail_length_x rb b"
  by (metis CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_x_def 
            CleanQ_RB_read_tail_x_enq_y)

lemma CleanQ_RB_read_tail_flags_x_enq_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_x (CleanQ_RB_enq_y b2 rb) b 
          = CleanQ_RB_read_tail_flags_x rb b"
  by (metis CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_x_def 
            CleanQ_RB_read_tail_x_enq_y)

lemma CleanQ_RB_read_tail_valid_offset_x_enq_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x (CleanQ_RB_enq_y b2 rb) b 
          = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_x_def CleanQ_RB_read_tail_x_def 
            CleanQ_RB_read_tail_x_enq_y)

lemma CleanQ_RB_read_tail_valid_length_x_enq_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x (CleanQ_RB_enq_y b2 rb) b 
          = CleanQ_RB_read_tail_valid_length_x rb b"
  by (metis CleanQ_RB_read_tail_valid_length_x_def CleanQ_RB_read_tail_x_def 
            CleanQ_RB_read_tail_x_enq_y)

lemmas CleanQ_RB_read_tail_x_enq_y_simps[simp] = 
     CleanQ_RB_read_tail_region_x_enq_y
     CleanQ_RB_read_tail_offset_x_enq_y
     CleanQ_RB_read_tail_length_x_enq_y
     CleanQ_RB_read_tail_flags_x_enq_y
     CleanQ_RB_read_tail_valid_offset_x_enq_y
     CleanQ_RB_read_tail_valid_length_x_enq_y


paragraph \<open>Read Tail Y, Deqeueue X\<close>

lemma CleanQ_RB_read_tail_region_y_deq_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_region_y (CleanQ_RB_deq_x  rb) b 
          = CleanQ_RB_read_tail_region_y rb b"
  by (metis CleanQ_RB_read_tail_region_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_deq_x)

lemma CleanQ_RB_read_tail_offset_y_deq_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_y (CleanQ_RB_deq_x  rb) b 
          = CleanQ_RB_read_tail_offset_y rb b"
  by (metis CleanQ_RB_read_tail_offset_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_deq_x)

lemma CleanQ_RB_read_tail_length_y_deq_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_length_y (CleanQ_RB_deq_x rb) b 
        = CleanQ_RB_read_tail_length_y rb b"
  by (metis CleanQ_RB_read_tail_length_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_deq_x)

lemma CleanQ_RB_read_tail_flags_y_deq_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_y (CleanQ_RB_deq_x  rb) b 
        = CleanQ_RB_read_tail_flags_y rb b"
  by (metis CleanQ_RB_read_tail_flags_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_deq_x)

lemma CleanQ_RB_read_tail_valid_offset_y_deq_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_y (CleanQ_RB_deq_x rb) b
          = CleanQ_RB_read_tail_valid_offset_y rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_deq_x)

lemma CleanQ_RB_read_tail_valid_length_y_deq_x:
  "CleanQ_RB_deq_y_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_y (CleanQ_RB_deq_x rb) b 
          = CleanQ_RB_read_tail_valid_length_y rb b"
  by (metis CleanQ_RB_read_tail_valid_length_y_def CleanQ_RB_read_tail_y_def 
            CleanQ_RB_read_tail_y_deq_x)

lemmas CleanQ_RB_read_tail__y_deq_x_simps[simp] = 
     CleanQ_RB_read_tail_region_y_deq_x
     CleanQ_RB_read_tail_offset_y_deq_x
     CleanQ_RB_read_tail_length_y_deq_x
     CleanQ_RB_read_tail_flags_y_deq_x
     CleanQ_RB_read_tail_valid_offset_y_deq_x
     CleanQ_RB_read_tail_valid_length_y_deq_x


paragraph \<open>Read Tail X, Dequeue Y\<close>

lemma CleanQ_RB_read_tail_region_x_deq_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_region_x (CleanQ_RB_deq_y rb) b 
          = CleanQ_RB_read_tail_region_x rb b"
  by (metis CleanQ_RB_read_tail_region_x_def CleanQ_RB_read_tail_x_def 
            CleanQ_RB_read_tail_x_deq_y)

lemma CleanQ_RB_read_tail_offset_x_deq_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_offset_x (CleanQ_RB_deq_y rb) b 
          = CleanQ_RB_read_tail_offset_x rb b"
  by (metis CleanQ_RB_read_tail_offset_x_def CleanQ_RB_read_tail_x_def 
            CleanQ_RB_read_tail_x_deq_y)

lemma CleanQ_RB_read_tail_length_x_deq_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_length_x (CleanQ_RB_deq_y rb) b 
          = CleanQ_RB_read_tail_length_x rb b"
  by (metis CleanQ_RB_read_tail_length_x_def CleanQ_RB_read_tail_x_def 
            CleanQ_RB_read_tail_x_deq_y)

lemma CleanQ_RB_read_tail_flags_x_deq_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_flags_x (CleanQ_RB_deq_y rb) b 
          = CleanQ_RB_read_tail_flags_x rb b"
  by (metis CleanQ_RB_read_tail_flags_x_def CleanQ_RB_read_tail_x_def 
            CleanQ_RB_read_tail_x_deq_y)

lemma CleanQ_RB_read_tail_valid_offset_x_deq_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_offset_x (CleanQ_RB_deq_y rb) b 
          = CleanQ_RB_read_tail_valid_offset_x rb b"
  by (metis CleanQ_RB_read_tail_valid_offset_x_def CleanQ_RB_read_tail_x_def 
            CleanQ_RB_read_tail_x_deq_y)

lemma CleanQ_RB_read_tail_valid_length_x_deq_y:
  "CleanQ_RB_deq_x_possible rb 
    \<Longrightarrow> CleanQ_RB_read_tail_valid_length_x (CleanQ_RB_deq_y  rb) b 
          = CleanQ_RB_read_tail_valid_length_x rb b"
  by (metis CleanQ_RB_read_tail_valid_length_x_def CleanQ_RB_read_tail_x_def 
            CleanQ_RB_read_tail_x_deq_y)

lemmas CleanQ_RB_read_tail_x_deq_y_simps[simp] = 
     CleanQ_RB_read_tail_region_x_deq_y
     CleanQ_RB_read_tail_offset_x_deq_y
     CleanQ_RB_read_tail_length_x_deq_y
     CleanQ_RB_read_tail_flags_x_deq_y
     CleanQ_RB_read_tail_valid_offset_x_deq_y
     CleanQ_RB_read_tail_valid_length_x_deq_y


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Writing Head, Head Not None\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  Whenever an element of the ring buffer is written, the head element is not None.
  We show this for all fields.
\<close>

paragraph \<open>Write Head X, Head is Not None\<close>

lemma CleanQ_RB_write_head_flags_x_not_none:
  "\<not>CleanQ_RB_head_none_x (CleanQ_RB_write_head_flags_x v rb)"
  by (metis CleanQ_RB_head_write_x_not_none CleanQ_RB_write_head_flags_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_flags_x_not_none2:
  "CleanQ_RB_head_none_x (CleanQ_RB_write_head_flags_y v rb) = CleanQ_RB_head_none_x rb"
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_flags_y_def)

lemma CleanQ_RB_write_head_offset_x_not_none:
  "\<not>CleanQ_RB_head_none_x (CleanQ_RB_write_head_offset_x v rb)"
  by (metis CleanQ_RB_head_write_x_not_none CleanQ_RB_write_head_offset_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_offset_x_not_none2:
  "CleanQ_RB_head_none_x (CleanQ_RB_write_head_offset_y v rb) = CleanQ_RB_head_none_x rb"
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_length_x_not_none:
  "\<not>CleanQ_RB_head_none_x (CleanQ_RB_write_head_length_x v rb)"
  by (metis CleanQ_RB_head_write_x_not_none CleanQ_RB_write_head_length_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_length_x_not_none2:
  "CleanQ_RB_head_none_x (CleanQ_RB_write_head_length_y v rb) = CleanQ_RB_head_none_x rb"
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_region_x_not_none:
  "\<not>CleanQ_RB_head_none_x (CleanQ_RB_write_head_region_x v rb)"
  by (metis CleanQ_RB_head_write_x_not_none CleanQ_RB_write_head_region_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_region_x_not_none2:
  "CleanQ_RB_head_none_x (CleanQ_RB_write_head_region_y v rb) = CleanQ_RB_head_none_x rb"
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_valid_offset_x_not_none:
  "\<not>CleanQ_RB_head_none_x (CleanQ_RB_write_head_valid_offset_x v rb)"
  by (metis CleanQ_RB_head_write_x_not_none CleanQ_RB_write_head_valid_offset_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_offset_x_not_none2:
  "CleanQ_RB_head_none_x (CleanQ_RB_write_head_valid_offset_y v rb) 
    = CleanQ_RB_head_none_x rb"
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_valid_offset_y_def)

lemma CleanQ_RB_write_head_valid_length_x_not_none:
  "\<not>CleanQ_RB_head_none_x (CleanQ_RB_write_head_valid_length_x v rb)"
  by (metis CleanQ_RB_head_write_x_not_none CleanQ_RB_write_head_valid_length_x_def 
            CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_valid_length_x_not_none2:
  "CleanQ_RB_head_none_x (CleanQ_RB_write_head_valid_length_y v rb) 
    = CleanQ_RB_head_none_x rb"
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

paragraph \<open>Write Head Y, Head is Not None\<close>

lemma CleanQ_RB_write_head_flags_y_not_none:
  "\<not>CleanQ_RB_head_none_y (CleanQ_RB_write_head_flags_y v rb)"
  by (metis CleanQ_RB_head_write_y_not_none CleanQ_RB_write_head_flags_y_def 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_flags_y_not_none2:
  "CleanQ_RB_head_none_y (CleanQ_RB_write_head_flags_x v rb) = CleanQ_RB_head_none_y rb"
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_flags_x_def)

lemma CleanQ_RB_write_head_offset_y_not_none:
  "\<not>CleanQ_RB_head_none_y (CleanQ_RB_write_head_offset_y v rb)"
  by (metis CleanQ_RB_head_write_y_not_none CleanQ_RB_write_head_offset_y_def 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_offset_y_not_none2:
  "CleanQ_RB_head_none_y (CleanQ_RB_write_head_offset_x v rb) = CleanQ_RB_head_none_y rb"
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_length_y_not_none:
  "\<not>CleanQ_RB_head_none_y (CleanQ_RB_write_head_length_y v rb)"
  by (metis CleanQ_RB_head_write_y_not_none CleanQ_RB_write_head_length_y_def 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_length_y_not_none2:
  "CleanQ_RB_head_none_y (CleanQ_RB_write_head_length_x v rb) = CleanQ_RB_head_none_y rb"
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_region_y_not_none:
  "\<not>CleanQ_RB_head_none_y (CleanQ_RB_write_head_region_y v rb)"
  by (metis CleanQ_RB_head_write_y_not_none CleanQ_RB_write_head_region_y_def 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_region_y_not_none2:
  "CleanQ_RB_head_none_y (CleanQ_RB_write_head_region_x v rb) = CleanQ_RB_head_none_y rb"
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_valid_offset_y_not_none:
  "\<not>CleanQ_RB_head_none_y (CleanQ_RB_write_head_valid_offset_y v rb)"
  by (metis CleanQ_RB_head_write_y_not_none CleanQ_RB_write_head_valid_offset_y_def 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_offset_y_not_none2:
  "CleanQ_RB_head_none_y (CleanQ_RB_write_head_valid_offset_x v rb)
     = CleanQ_RB_head_none_y rb"
  by (simp add: CleanQ_RB_head_none_y_def CleanQ_RB_write_head_valid_offset_x_def)

lemma CleanQ_RB_write_head_valid_length_y_not_none:
  "\<not>CleanQ_RB_head_none_y (CleanQ_RB_write_head_valid_length_y v rb)"
  by (metis CleanQ_RB_head_write_y_not_none CleanQ_RB_write_head_valid_length_y_def 
            CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_valid_length_y_not_none2:
  "CleanQ_RB_head_none_y (CleanQ_RB_write_head_valid_length_x v rb) 
    = CleanQ_RB_head_none_y rb "
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


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>TODO: Sort here\<close>
(* ------------------------------------------------------------------------------------ *)

paragraph \<open>Write head behaves as expected for X\<close>

lemma CleanQ_RB_write_head_flags_x_eq:
  assumes reg: "region (CleanQ_RB_read_head_x (CRB x)) = region b2" and
          off: "offset (CleanQ_RB_read_head_x (CRB x)) = offset b2 " and
          len: "length (CleanQ_RB_read_head_x (CRB x)) = length b2" and
          vao: "valid_offset (CleanQ_RB_read_head_x (CRB x)) = valid_offset b2" and
          val:"valid_length (CleanQ_RB_read_head_x (CRB x)) = valid_length b2"
  shows "b2 = CleanQ_RB_read_head_x (CleanQ_RB_write_head_flags_x ( b2) (CRB x))"
  using assms unfolding CleanQ_RB_write_head_flags_x_def CleanQ_RB_read_head_x_def
  by(auto)

lemma CleanQ_RB_write_head_region_x_eq :
  shows "region (CleanQ_RB_read_head_x (CleanQ_RB_write_head_region_x ( b2) (CRB x))) = region b2"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_region_x_def)

lemma CleanQ_RB_write_head_offset_x_eq :
  shows "offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_offset_x ( b2) (CRB x))) = offset b2"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_offset_x_def)

lemma CleanQ_RB_write_head_length_x_eq :
  shows "length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_length_x ( b2) (CRB x))) = length b2"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_length_x_def)

lemma CleanQ_RB_write_head_valid_length_x_eq :
  shows "valid_length (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_length_x ( b2) (CRB x))) = valid_length b2"
  by (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_valid_length_x_def)
  

lemma CleanQ_RB_write_head_valid_offset_x_eq :
  shows "valid_offset (CleanQ_RB_read_head_x (CleanQ_RB_write_head_valid_offset_x ( b2) (CRB x))) = valid_offset b2"
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
  shows "b2 = CleanQ_RB_read_head_y (CleanQ_RB_write_head_flags_y ( b2) (CRB x))"
  using assms unfolding CleanQ_RB_write_head_flags_y_def CleanQ_RB_read_head_y_def
  by(auto)

lemma CleanQ_RB_write_head_region_y_eq :
  shows "region (CleanQ_RB_read_head_y (CleanQ_RB_write_head_region_y ( b2) (CRB y))) = region b2"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_region_y_def)

lemma CleanQ_RB_write_head_offset_y_eq :
  shows "offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_offset_y ( b2) (CRB y))) = offset b2"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_offset_y_def)

lemma CleanQ_RB_write_head_length_y_eq :
  shows "length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_length_y ( b2) (CRB y))) = length b2"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_length_y_def)

lemma CleanQ_RB_write_head_valid_length_y_eq :
  shows "valid_length (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_length_y ( b2) (CRB y))) = valid_length b2"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_length_y_def)
  
lemma CleanQ_RB_write_head_valid_offset_y_eq :
  shows "valid_offset (CleanQ_RB_read_head_y (CleanQ_RB_write_head_valid_offset_y ( b2) (CRB y))) = valid_offset b2"
  by (simp add: CleanQ_RB_read_head_y_def CleanQ_RB_write_head_valid_offset_y_def)

lemmas CleanQ_RB_write_head_y_eq[simp] = 
  CleanQ_RB_write_head_region_y_eq
  CleanQ_RB_write_head_offset_y_eq 
  CleanQ_RB_write_head_length_y_eq
  CleanQ_RB_write_head_valid_offset_y_eq
  CleanQ_RB_write_head_valid_length_y_eq
  CleanQ_RB_write_head_flags_y_eq



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
                \<acute>CRB := (CleanQ_RB_write_head_region_x ( b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region (CleanQ_RB_read_head_x \<acute>CRB) = region b 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_offset_x ( b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region (CleanQ_RB_read_head_x \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_x \<acute>CRB) = offset b 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_length_x ( b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region (CleanQ_RB_read_head_x \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_x \<acute>CRB) = offset b \<and>
                length (CleanQ_RB_read_head_x \<acute>CRB) = length b
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_valid_offset_x ( b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region (CleanQ_RB_read_head_x \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_x \<acute>CRB) = offset b \<and>
                length (CleanQ_RB_read_head_x \<acute>CRB) = length b \<and>
                valid_offset (CleanQ_RB_read_head_x \<acute>CRB) = valid_offset b
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_valid_length_x ( b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_x_P \<acute>uni \<acute>CRB b \<and> 
                region (CleanQ_RB_read_head_x \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_x \<acute>CRB) = offset b \<and>
                length (CleanQ_RB_read_head_x \<acute>CRB) = length b \<and>
                valid_offset (CleanQ_RB_read_head_x \<acute>CRB) = valid_offset b \<and>
                valid_length (CleanQ_RB_read_head_x \<acute>CRB) = valid_length b
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_flags_x ( b) \<acute>CRB) ;;
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
                \<acute>CRB := (CleanQ_RB_write_head_region_y ( b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and> 
                region (CleanQ_RB_read_head_y \<acute>CRB) = region b 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_offset_y ( b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and>  
                region (CleanQ_RB_read_head_y \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_y \<acute>CRB) = offset b 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_length_y ( b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and>  
                region (CleanQ_RB_read_head_y \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_y \<acute>CRB) = offset b \<and>
                length (CleanQ_RB_read_head_y \<acute>CRB) = length b 
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_valid_offset_y ( b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and>  
                region (CleanQ_RB_read_head_y \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_y \<acute>CRB) = offset b \<and>
                length (CleanQ_RB_read_head_y \<acute>CRB) = length b \<and> 
                valid_offset (CleanQ_RB_read_head_y \<acute>CRB) = valid_offset b
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_valid_length_y ( b) \<acute>CRB) ;;
              \<lbrace> CleanQ_RB_enq_y_P \<acute>uni \<acute>CRB b \<and>  
                region (CleanQ_RB_read_head_y \<acute>CRB) = region b \<and>
                offset (CleanQ_RB_read_head_y \<acute>CRB) = offset b \<and>
                length (CleanQ_RB_read_head_y \<acute>CRB) = length b \<and> 
                valid_offset (CleanQ_RB_read_head_y \<acute>CRB) = valid_offset b \<and>
                valid_length (CleanQ_RB_read_head_y \<acute>CRB) = valid_length b
              \<rbrace>
                \<acute>CRB := (CleanQ_RB_write_head_flags_y ( b) \<acute>CRB) ;;
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
  by(oghoare, auto)
  

lemma  CleanQ_RB_incr_tail_y_hoare:
   "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub> 
    \<lbrace>  CleanQ_RB_deq_y_Q K \<acute>CRB b \<rbrace> 
      \<acute>CRB := (CleanQ_RB_incr_tail_y b \<acute>CRB)
    \<lbrace> CleanQ_RB_deq_y_R K \<acute> CRB b  \<rbrace>,\<lbrace>True\<rbrace>" 
  by(oghoare, auto)

 
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
  by(oghoare, auto)
  
  
  
lemma CleanQ_RB_deq_y_hoare : 
   "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/ F\<^esub>   
    \<lbrace>  CleanQ_RB_deq_y_P K \<acute>CRB (CleanQ_RB_read_tail_x \<acute>CRB) \<rbrace> 
      \<acute>buf_y := (CleanQ_RB_read_tail_y \<acute>CRB) ;;
    \<lbrace> CleanQ_RB_deq_y_Q K \<acute>CRB \<acute>buf_y  \<rbrace>
      \<acute>CRB := (CleanQ_RB_incr_tail_y \<acute>buf_y \<acute>CRB)
    \<lbrace> CleanQ_RB_deq_y_R K \<acute>CRB \<acute>buf_y \<rbrace>, \<lbrace>True\<rbrace>"
  by(oghoare, auto)
  

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Concurrency proofs helper lemmas\<close>
(* ------------------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Concurrency proofs\<close>
(* ------------------------------------------------------------------------------------ *)

lemma CleanQ_RB_read_concurent:
     "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/{True}\<^esub>   
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
  by(oghoare, auto)

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
  by(oghoare, auto) (* 106 subgoals *)
    


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Helper lemmas specifically for last concurrency proof\<close>
(* ------------------------------------------------------------------------------------ *)


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
  apply(auto)[100]
  apply(auto)[200]
  apply(auto)[200]
  apply(auto)
  done

end 