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



theory ListRBRefinement imports 
  SetListRefinement
  "../Refinements"
  ModularIntervals
begin

text \<open>State definiton.\<close>

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


(* Need modular intervals to specify ring buffer properties *)
locale modulus = nonzero_modulus +
  assumes fixN: "N = 64"
begin


definition slice :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
  where "slice buf s e = [buf ((s+i) mod N). i <- [0..< e \<ominus> s]]"

definition slice_xy :: "'a abstractState \<Rightarrow> 'a list"
  where "slice_xy st = slice (ring (tx (client st))) (pos (rx (server st))) (pos (tx (client st)))"

definition slice_yx :: "'a abstractState \<Rightarrow> 'a list"
  where "slice_yx st = slice (ring (tx (server st))) (pos (rx (client st))) (pos (tx (server st)))"

text \<open>The union of all sets is constant.\<close>
fun I1_img :: "'a abstractState \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1_img rb K \<longleftrightarrow> ((SX rb) \<union> (SY rb) \<union> (set (slice_xy rb)) \<union> (set (slice_yx rb))) = K"

text \<open>All pairwise intersections are empty.\<close>
fun I2_img :: "'a abstractState \<Rightarrow> bool"
  where "I2_img rb \<longleftrightarrow>
    SX rb \<inter> SY rb = {} \<and> SX rb \<inter> set (slice_xy rb) = {} \<and> SX rb \<inter> set (slice_yx rb) = {} \<and> 
    SY rb \<inter> set (slice_xy rb) = {} \<and> SY rb \<inter> set (slice_yx rb) = {} \<and> 
    set (slice_xy rb) \<inter> set (slice_yx rb) = {}"

text \<open>client TX = server RX and client RX = server TX.\<close>
fun I4 :: "'a abstractState \<Rightarrow> bool"
  where "I4 st \<longleftrightarrow> (ring (tx (client st))) = (ring (rx (server st))) \<and>
                   (ring (tx (server st))) = (ring (rx (client st)))"

text \<open>Ring buffer state is valid\<close>
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

(*Don't think there is an ordering invariant since there are only 2 pointers into the ring buffer *)

text \<open>The full state. corresponds to the whole program state.\<close>
definition sr_list_rb :: "'a set \<Rightarrow> ('a ListRB \<times> 'a abstractState) set"
  where "sr_list_rb K = {(list, state). (lSX list, lTXY list, lSY list, lTYX list) = 
                         (SX state, slice_xy state, SY state, slice_yx state) \<and>
                         I1_img state K \<and> I2_img state \<and> I3 list \<and> 
                         I4 state \<and> I5 state}"

definition id_state :: "'a set \<Rightarrow> ('a ListRB \<times> 'a abstractState) set"
  where "id_state = sr_list_rb"

end