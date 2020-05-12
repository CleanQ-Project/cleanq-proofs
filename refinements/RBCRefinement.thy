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



theory RBCRefinement
imports
  "../../autocorres/AutoCorres"
  ModularIntervals  
begin

(* Assumes right path to autocorres*)
external_file "ffq_queue.c"

install_C_file "ffq_queue.c"
(* autocorres "ffq_queue.c" *)

text \<open>definition of a buffer as in the c code but in isabelle.
      Only rid, offset and len matter for the isabelle part\<close>
record 'a buf =
  rid :: 'a
  offset :: 'a
  len :: 'a

text \<open>Only rid offset and len matter to the buffer definition itself\<close>
definition buf_eq :: "'a buf \<Rightarrow> 'a buf \<Rightarrow> bool"
  where "buf_eq a b \<equiv> (rid a = rid b) \<and> (offset a = offset b) \<and> (len a = len b)"

(* Redefine Abstract RB for the time beeing since there seem to be overlapping theory names etc. 
   when both are imported*)

definition dir_rx :: nat
  where "dir_rx = 1"

definition dir_tx :: nat
  where "dir_tx = 2"

text \<open>Single queue. corresponds to ffq_queue.\<close>
record 'a abstractRB =
  ring :: "nat \<Rightarrow> 'a"
  pos :: nat
  direction :: nat
  size :: nat

text \<open>A queue pair. corresponds to ffq_qp.\<close>
record 'a abstractQP =
  rx :: "'a abstractRB"
  tx :: "'a abstractRB"

text \<open>The full state. corresponds to the whole program state.\<close>
record 'a abstractState =
  client :: "'a abstractQP"
  server :: "'a abstractQP"
  SX :: "'a set"
  SY :: "'a set"

record 'a concretState =
  cclient :: "ffq_qp_C"
  cserver :: "ffq_qp_C"
  cSX :: "'a set"
  cSY :: "'a set"

(* to reuse \<ominus> notation *)
(* Need modular intervals to specify ring buffer properties *)
locale modulus = nonzero_modulus +
  assumes fixN: "N = 64"
begin

(* Dereference a pointer *)
abbreviation "deref s x \<equiv> h_val (hrs_mem (t_hrs_' (globals s))) x"

definition pos_tx_queue :: "(('b globals_scheme, 'c) state_scheme) \<Rightarrow> ffq_qp_C \<Rightarrow> word16"
  where "pos_tx_queue state qp = pos_C (deref state (txq_C qp))"

definition pos_rx_queue :: "(('b globals_scheme, 'c) state_scheme) \<Rightarrow> ffq_qp_C \<Rightarrow> word16"
  where "pos_rx_queue state qp = pos_C (deref state (rxq_C qp))"

definition slot_at_pos :: "(('b globals_scheme, 'c) state_scheme) \<Rightarrow> (ffq_queue_C) \<Rightarrow> nat \<Rightarrow> word32 buf"
  where
    "slot_at_pos st q po \<equiv> \<lparr> rid = rid_C (deref st ((slots_C q)  +\<^sub>p (po))),
                             offset = offset_C (deref st ((slots_C q)  +\<^sub>p (po))),
                             len = len_C (deref st ((slots_C q)  +\<^sub>p (po)))\<rparr>"


definition queue_lift :: "(('b globals_scheme, 'c) state_scheme) \<Rightarrow> ffq_queue_C \<Rightarrow> (word32 buf) abstractRB"
  where "queue_lift st conc = \<lparr> ring = (slot_at_pos st conc), 
                             pos = (unat (pos_C conc)),
                             direction = unat ((direction_C conc)), 
                             size = unat ((size_C conc)) \<rparr>"

definition qp_lift :: "(('b globals_scheme, 'c) state_scheme) \<Rightarrow> ffq_qp_C \<Rightarrow> (word32 buf) abstractQP"
  where "qp_lift st conc = \<lparr> rx = queue_lift st (deref st (rxq_C conc)), tx = queue_lift st (deref st (txq_C conc))\<rparr>"

definition slice :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
  where "slice buf s e = [buf ((s+i) mod N). i <- [0..< e \<ominus> s]]"

definition slice_xy :: "'a abstractState \<Rightarrow> 'a list"
  where "slice_xy st = slice (ring (tx (client st))) (pos (rx (server st))) (pos (tx (client st)))"

definition slice_yx :: "'a abstractState \<Rightarrow> 'a list"
  where "slice_yx st = slice (ring (tx (server st))) (pos (rx (client st))) (pos (tx (server st)))"

text \<open>The union of all sets is constant.\<close>
fun I1_img :: "'a abstractState \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1_img rb S \<longleftrightarrow> ((SX rb) \<union> (SY rb) \<union> (set (slice_xy rb)) \<union> (set (slice_yx rb))) = S"

text \<open>All pairwise intersections are empty.\<close>
fun I2_img :: "'a abstractState \<Rightarrow> bool"
  where "I2_img rb \<longleftrightarrow>
    SX rb \<inter> SY rb = {} \<and> SX rb \<inter> set (slice_xy rb) = {} \<and> SX rb \<inter> set (slice_yx rb) = {} \<and> 
    SY rb \<inter> set (slice_xy rb) = {} \<and> SY rb \<inter> set (slice_yx rb) = {} \<and> 
    set (slice_xy rb) \<inter> set (slice_yx rb) = {}"

text \<open>Elements in the ring buffers are distinct.\<close>
fun I3_img :: "'a abstractState \<Rightarrow> bool"
  where "I3_img rb \<longleftrightarrow> distinct ((slice_xy rb)@(slice_yx rb))"


text \<open>client TX = server RX and client RX = server TX.\<close>
fun I4 :: "'a abstractState \<Rightarrow> bool"
  where "I4 st \<longleftrightarrow> (ring (tx (client st))) = (ring (rx (server st))) \<and>
                   (ring (tx (server st))) = (ring (rx (client st)))"

text \<open>Ring buffer state is valid (and everything stays that way)\<close>
fun I5 :: "'a abstractState \<Rightarrow> bool"
  where "I5 st \<longleftrightarrow> (direction (tx (client st))) = dir_tx \<and>
                   (direction (tx (server st))) = dir_tx \<and>
                   (direction (rx (client st))) = dir_rx \<and>
                   (direction (rx (server st))) = dir_rx \<and>
                   size (tx (server st)) = N \<and>
                   size (tx (client st)) = N \<and>
                   size (rx (server st)) = N \<and>
                   size (rx (client st)) = N \<and>
                   pos (tx (server st)) < N \<and>
                   pos (tx (client st)) < N \<and>
                   pos (rx (server st)) < N \<and>
                   pos (rx (client st)) < N "


(*Can you get rid of (word32 buf)? *)
(* TODO distinctness of ring buffer elements *)
definition sr_abstract_concret :: "(word32 buf) set \<Rightarrow> (('b globals_scheme, 'c) state_scheme) \<Rightarrow> ((word32 buf) abstractState \<times> (word32 buf) concretState) set"
  where "sr_abstract_concret SK glob = {(st_ab, st_c). (SX st_ab, SY st_ab, client st_ab, server st_ab) = 
                                    (cSX st_c, cSY st_c, qp_lift glob (cclient st_c), 
                                     qp_lift glob (cserver st_c)) \<and> I1_img st_ab SK \<and> I2_img st_ab \<and> 
                                     I3_img st_ab \<and> I4 st_ab \<and> I5 st_ab}"
end

