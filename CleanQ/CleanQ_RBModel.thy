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



section \<open>CleanQ Abstract Ring Buffer Model\<close>

text \<open>
  We define the CleanQ set model in the the following Isabelle theory: 
\<close>

theory CleanQ_RBModel 
(*<*) imports  
    "CleanQ_ModularIntervals"
begin
(*>*)

(* ==================================================================================== *)
subsection \<open>CleanQ Abstract Ring Buffer Model State\<close>
(* ==================================================================================== *)

text \<open>
  The third refinement is trying to get as close to the C implementation as possible.
  The two transfer queues are modeled as \verb+CleanQ_RB+. Two of these are combined
  to a \verb+CleanQ_QP+ which consists of an RX and TX queue. The full state of the
  system is compromised of two queue pairs and modeled in the \verb+CleanQ_RB_State+
  recrod. Ther are two queue pairs; one for the client and the other one for the server.
  The TX queue ring buffer of the client is the RX queue ring buffer of the server and 
  the RX queue ring buffer of the client is the TX queue ring buffer of the sever. While
  these are the same, each of these queue records has their own position in the ring buffer.
  In total there are 4 position pointers in to the two Ring buffers. The SX and TX
  sets are still the same as in the abstract model since we can not make any statement
  about the sets owned by each of the sides. 
\<close>

definition dir_rx :: nat
  where "dir_rx = 1"

definition dir_tx :: nat
  where "dir_tx = 2"

text \<open>Single queue. corresponds to \verb+ffq_queue+.\<close>
record 'a CleanQ_RB =
  ring :: "nat \<Rightarrow> 'a"
  pos :: nat
  direction :: nat
  size :: nat

text \<open>A queue pair. corresponds to \verb+ffq_qp+.\<close>
record 'a CleanQ_QP =
  rx :: "'a CleanQ_RB"
  tx :: "'a CleanQ_RB"

text \<open>The full state. corresponds to the whole program state.\<close>
record 'a CleanQ_RB_State =
  qTXY :: "'a CleanQ_QP"
  qTYX :: "'a CleanQ_QP"
  SX :: "'a set"
  SY :: "'a set"


(* Need modular intervals to specify ring buffer properties *)
(*<*)
locale modulus = nonzero_modulus +
  assumes fixN: "N = 64"
begin
(*>*)
(* ==================================================================================== *)
subsection \<open>CleanQ Abstract Ring Buffer Model Invariants\<close>
(* ==================================================================================== *)

text \<open>Helper definitions to define invariants.\<close>
text \<open>Get a list of all the entries between two positions in the ring buffer. We extract
      an interval from a to b in a ring buffer i.e. if we want to extract from entry 5 to 
      1 in a ring of size 6, this will return the entries 5,6, and 1. \<close>
definition slice :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
  where "slice buf s e = [buf ((s+i) mod N). i <- [0..< e \<ominus> s]]"

text \<open>Get a list of the entries fro the XY direction.\<close>
definition slice_xy :: "'a CleanQ_RB_State \<Rightarrow> 'a list"
  where "slice_xy st = slice (ring (tx (qTXY st))) (pos (rx (qTYX st))) (pos (tx (qTXY st)))"

text \<open>Get a list of the entries fro the YX direction.\<close>
definition slice_yx :: "'a CleanQ_RB_State \<Rightarrow> 'a list"
  where "slice_yx st = slice (ring (tx (qTYX st))) (pos (rx (qTXY st))) (pos (tx (qTYX st)))"

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Images of the previously defined invariants\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>Definition of I1 on the Ring buffer model: The union of all sets is constant.\<close>
fun I1_img :: "'a CleanQ_RB_State \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1_img rb K \<longleftrightarrow> ((SX rb) \<union> (SY rb) \<union> (set (slice_xy rb)) \<union> (set (slice_yx rb))) = K"

text \<open>Definition of I2 on the Ring buffer model: No Double Presenc.\<close>
fun I2_img :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I2_img rb \<longleftrightarrow>
    SX rb \<inter> SY rb = {} \<and> SX rb \<inter> set (slice_xy rb) = {} \<and> SX rb \<inter> set (slice_yx rb) = {} \<and> 
    SY rb \<inter> set (slice_xy rb) = {} \<and> SY rb \<inter> set (slice_yx rb) = {} \<and> 
    set (slice_xy rb) \<inter> set (slice_yx rb) = {}"

text \<open>Definition of I3 on the Ring buffer model: No duplicates in list.\<close>
fun I3_img :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I3_img rb \<longleftrightarrow> distinct ((slice_xy rb) @ (slice_yx rb))"


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I4: The ring buffers are the same\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  In order for the model to work with the C code, there needs to be shared state
  similar to the C code. For an IPC queue there are normally two shared memory
  regions which are used as ring buffers. In this proof the client TX ring buffer
  is the same as the server RX ring buffer and the server TX ring buffer is the
  same as the client RX ring buffer.
\<close>
fun I4 :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I4 st \<longleftrightarrow> (ring (tx (qTXY st))) = (ring (rx (qTYX st))) \<and>
                   (ring (tx (qTYX st))) = (ring (rx (qTXY st)))"

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I5: Ring buffers are in a valid state\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  A queue pair is in a valid state if the RX and TX queues have the right direction,
  The sizes of the ring buffers are fixed to some N and the position pointers are
  less than that N. This needs to be true for both queue pairs in \verb+CleanQ_RB_State+. 
\<close>
fun I5 :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I5 st \<longleftrightarrow> (direction (tx (qTXY st))) = dir_tx \<and>
                   (direction (tx (qTYX st))) = dir_tx \<and>
                   (direction (rx (qTXY st))) = dir_rx \<and>
                   (direction (rx (qTYX st))) = dir_rx \<and>
                   size (tx (qTYX st)) = N \<and>
                   size (tx (qTXY st)) = N \<and>
                   size (rx (qTYX st)) = N \<and>
                   size (rx (qTXY st)) = N \<and>
                   pos (tx (qTYX st)) < N \<and>
                   pos (tx (qTXY st)) < N \<and>
                   pos (rx (qTYX st)) < N \<and>
                   pos (rx (qTXY st)) < N "

(*Don't think there is an ordering invariant since there are only 2 pointers into the ring buffer *)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>CleanQ List Invariants\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We combine all invariants for the abstract CleanQ list model and define the predicate 
  \verb+CleanQ_List_Invariants+.
\<close>

fun CleanQ_RB_Invariants :: "'a set \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> bool"
  where "CleanQ_RB_Invariants K rb \<longleftrightarrow> I1_img rb K \<and> I2_img rb \<and> I3_img rb \<and> I4 rb \<and> I5 rb"

end (*Modulus end *)

end