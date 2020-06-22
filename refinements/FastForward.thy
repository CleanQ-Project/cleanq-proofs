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

theory FastForward
imports "AutoCorres.AutoCorres"
begin

external_file "ffq_queue.c"

install_C_file "ffq_queue.c"
(* autocorres "ffq_queue.c" *)

context ffq_queue begin

(* C parser output. *)
thm ffq_dequeue_body_def
thm ffq_enqueue_body_def
thm ffq_init_tx_body_def
thm ffq_init_pair_body_def

(* Dereference a pointer *)
abbreviation "deref s x \<equiv> h_val (hrs_mem (t_hrs_' (globals s))) x"

abbreviation "valid_buf rid offset len valid_data valid_len flags \<equiv> rid \<noteq> 0 \<and> len \<noteq> 0"

definition FFQ_DEFAULT_SIZE :: word16
  where
    "FFQ_DEFAULT_SIZE = 64"

definition FFQ_SLOT_EMPTY :: word32
  where
    "FFQ_SLOT_EMPTY = -1"

definition FFQ_SLOT_FULL :: word32
  where
    "FFQ_SLOT_FULL = 1"

definition slot_empty :: "ffq_slot_C \<Rightarrow> bool"
where
  "slot_empty s \<equiv> (empty_C s = FFQ_SLOT_EMPTY)"

definition slot_full :: "ffq_slot_C \<Rightarrow> bool"
where
  "slot_full s \<equiv> (empty_C s = FFQ_SLOT_FULL)"

(* Check if the queue is empty *)
definition queue_empty :: "('b globals_scheme, 'c) state_scheme \<Rightarrow> (ffq_queue_C ptr) \<Rightarrow> bool"
  where
    "queue_empty s q \<equiv> \<forall>a\<in>set (array_addrs ((slots_C (deref s q)) :: (ffq_slot_C ptr)) (unat FFQ_DEFAULT_SIZE)) . slot_empty (deref s a)"

(* Check if the queue is full *)
definition queue_full :: "('b globals_scheme, 'c) state_scheme \<Rightarrow> (ffq_queue_C ptr) \<Rightarrow> bool"
  where
    "queue_full s q \<equiv> \<forall>a\<in>set (array_addrs ((slots_C (deref s q)) :: (ffq_slot_C ptr)) (unat FFQ_DEFAULT_SIZE)) . slot_full (deref s a)"

(* Queue is in a valid state i.e. setup correctly  *)
definition queue_valid_state :: "('b globals_scheme, 'c) state_scheme \<Rightarrow> (ffq_queue_C ptr) \<Rightarrow> bool"
  where
    "queue_valid_state s q \<equiv> \<forall>a\<in>set (array_addrs ((slots_C (deref s q)) :: (ffq_slot_C ptr)) (unat FFQ_DEFAULT_SIZE)) . 
     slot_full (deref s a) | slot_empty (deref s a) \<and> 
     pos_C (deref s q) \<ge> 0 \<and> pos_C (deref s q) \<le> FFQ_DEFAULT_SIZE \<and>
     c_guard (slots_C (deref s q)) \<and>
     (direction_C (deref s q) = FFQ_DIRECTION_SEND \<or> direction_C (deref s q) = FFQ_DIRECTION_RECV)"

definition next_pos :: "word16 \<Rightarrow> word16 \<Rightarrow> word16"
  where
    "next_pos pos q_size = (if ((pos+1) = ucast(q_size)) then 0 else (pos+1))"

definition slot_at_pos :: "(ffq_queue_C) \<Rightarrow> word16 \<Rightarrow> ffq_slot_C ptr"
  where
    "slot_at_pos q pos \<equiv> (slots_C q)  +\<^sub>p (unat pos)"

lemma ffq_dequeue_spec:
  shows
   (*- The queue is in a valid state
     - save pos for later
     - provided values are unequal null i.e. valid
     - the direction of the queue is recv *)
  "\<forall>t. \<Gamma> \<turnstile> \<lbrace>t. queue_valid_state t q \<and> 
            pos = pos_C (deref t q) \<and>
            c_guard q \<and> c_guard rid \<and> c_guard offset \<and> c_guard len \<and> c_guard valid_data \<and> c_guard valid_len \<and> c_guard flags \<and>
            direction_C (deref t q) = FFQ_DIRECTION_RECV
          \<rbrace>
       \<acute>ret__int :== PROC ffq_dequeue(q, rid, offset, len, valid_data, valid_len, flags)
   \<lbrace>t. queue_valid_state t q \<and>
    (empty_C (deref t (slot_at_pos (deref t q) pos)) = FFQ_SLOT_FULL) \<and>
     (\<acute>ret__int \<noteq> 0 \<longrightarrow> (pos_C (deref t q)) = pos) \<and> 
     (\<acute>ret__int = 0 \<and> pos_c (deref t q) = (next_pos pos FFQ_DEFAULT_SIZE)) \<and>
     valid_buf (deref t rid) (deref t offset) (deref t len) (deref t valid_data) (deref t valid_len) (deref t flags)
   \<rbrace>"
   (* Regardless of error or not
      - queue is in a valid state
      - slot at pos is marked as empty
      First defined what happens on error (ret_int != 0) 
      -pos did not change
      On Success
      - pos was increased modulo size
      - the return values are a valid buffer *)
  oops


lemma ffq_enqueue_spec:
  shows
   (* -Queue is in a valid state 
      - the values provided are valid 
      - we save the position pos to talk about it later
      - the direction of the queue is send *)
  "\<forall>t. \<Gamma> \<turnstile> \<lbrace>t. queue_valid_state t q  \<and>
            valid_buf rid offset len valid_data valid_len flags \<and> 
            pos = pos_C (deref t q) \<and>
            c_guard q \<and> 
            direction_C (deref t q) = FFQ_DIRECTION_SEND \<rbrace>
       \<acute>ret__int :== PROC ffq_enqueue(q, rid, offset, len, valid_data, valid_len, flags)
   \<lbrace>t. queue_valid_state t q \<and>
    ((\<acute>ret__int \<noteq> 0 \<and> (pos_C (deref t q)) = pos) \<or> (\<acute>ret__int = 0 \<and> pos_c (deref t q) = (next_pos pos FFQ_DEFAULT_SIZE)))\<and>
    (\<acute>ret__int = 0 \<longrightarrow> rid_C (deref t (slot_at_pos (deref t q) pos)) = rid \<and> 
                       offset_C (deref t (slot_at_pos (deref t q) pos)) = offset \<and>
                       len_C (deref t (slot_at_pos (deref t q) pos)) = len \<and>
                       valid_data_C (deref t (slot_at_pos (deref t q) pos)) = valid_data \<and>
                       valid_len_C (deref t (slot_at_pos (deref t q) pos)) = valid_len \<and>
                       flags_C (deref t (slot_at_pos (deref t q) pos)) = flags) \<and>
    (empty_C (deref t (slot_at_pos (deref t q) pos)) = FFQ_SLOT_FULL)
   \<rbrace>"
   (* Regardless of error or not
      - queue is in a valid state
      - slot at pos is marked as full
      First defined what happens on error (ret_int != 0) 
      -pos did not change
      On Success
      - pos was increased modulo size
      - the slot previously pointed to by pos has now the values provided *)
  oops
  

lemma init_rx_state_spec: 
  shows
  "\<forall>t. \<Gamma> \<turnstile> \<lbrace>t. (\<forall>a\<in>set (array_addrs (buf :: ffq_slot_C ptr) (unat FFQ_DEFAULT_SIZE)). c_guard a)
          \<and> c_guard q \<and> c_guard buf \<rbrace>
       \<acute>ret__int :== PROC ffq_init_rx(q, buf)
   \<lbrace>t. (queue_empty t q) \<and> slots_C (deref t q) = buf \<and> pos_C (deref t q) = 0 \<and> direction_C (deref t q) = FFQ_DIRECTION_RECV 
    \<and> size_C (deref t q) = FFQ_DEFAULT_SIZE \<rbrace>"
  apply(vcg)
  oops

lemma init_tx_state_spec: 
  shows
  "\<forall>t. \<Gamma> \<turnstile> \<lbrace>t. (\<forall>a\<in>set (array_addrs (buf :: ffq_slot_C ptr) (unat FFQ_DEFAULT_SIZE)). c_guard a)
          \<and> c_guard q \<and> c_guard buf \<rbrace>
       \<acute>ret__int :== PROC ffq_init_tx(q, buf)
   \<lbrace>t. (queue_empty t q) \<and> slots_C (deref t q) = buf \<and> pos_C (deref t q) = 0 \<and> direction_C (deref t q) = FFQ_DIRECTION_SEND
    \<and> size_C (deref t q) = FFQ_DEFAULT_SIZE \<rbrace>"
  apply vcg
  oops

end
end
