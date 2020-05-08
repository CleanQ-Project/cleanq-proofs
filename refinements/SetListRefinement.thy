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



theory SetListRefinement imports 
  "../Refinements"
begin

text \<open>State definiton.\<close>
record 'a ListRB =
  lSX  :: "'a set"
  lSY  :: "'a set"
  lTXY :: "'a list"
  lTYX :: "'a list"

record 'a SetRB =
  SX  :: "'a set"
  SY  :: "'a set"
  TXY :: "'a set"
  TYX :: "'a set"

text \<open>The union of all sets is constant.\<close>
fun I1 :: "'a SetRB \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1 rb K \<longleftrightarrow> ((SX rb) \<union> (SY rb) \<union> (TXY rb) \<union> (TYX rb)) = K"

text \<open>All pairwise intersections are empty.\<close>
fun I2 :: "'a SetRB \<Rightarrow> bool"
  where "I2 rb \<longleftrightarrow>
    SX rb \<inter> SY rb = {} \<and> SX rb \<inter> TXY rb = {} \<and> SX rb \<inter> TYX rb = {} \<and> 
    SY rb \<inter> TXY rb = {} \<and> SY rb \<inter> TYX rb = {} \<and> 
    TXY rb \<inter> TYX rb = {}"

fun I3 :: "'a ListRB \<Rightarrow> bool"
  where "I3 st_list \<longleftrightarrow> distinct (lTXY st_list) \<and> distinct (lTYX st_list)"

definition sr_set_list_enq :: "'a set \<Rightarrow> ('a SetRB \<times> 'a ListRB) set"
  where "sr_set_list_enq K = {(st_ab, st_list). (SX st_ab, TXY st_ab, SY st_ab, TYX st_ab) = 
                              (lSX st_list, set (lTXY st_list), lSY st_list, set (lTYX st_list)) 
                              \<and> I1 st_ab K \<and> I2 st_ab \<and> I3 st_list}"
(*                            \<and> buf \<in> (lSX st_list) \<and> distinct ((lTXY st_list) @ [buf])}" *)


definition sr_set_list_deq :: "'a set \<Rightarrow> ('a SetRB \<times> 'a ListRB) set"
  where "sr_set_list_deq K = {(st_ab, st_list). (SX st_ab, TXY st_ab, SY st_ab, TYX st_ab) = 
                                  (lSX st_list, set (lTXY st_list), lSY st_list, set (lTYX st_list)) 
                                  \<and> I1 st_ab K \<and> I2 st_ab \<and> I3 st_list }"
(*                                \<and> buf \<notin> (lSX st_list) \<and> hd (lTXY st_list) = buf}" *)

definition fr_id :: "'a \<Rightarrow> 'a set \<Rightarrow> ('a SetRB \<times> 'a ListRB) set"
  where "fr_id = sr_set_list_enq "

definition listRB_enqueuex :: "'a \<Rightarrow> 'a ListRB \<Rightarrow> 'a ListRB"
  where "listRB_enqueuex b st_list =  \<lparr> lSX = (lSX st_list)-{b}, lSY = (lSY st_list),
                                      lTXY = (lTXY st_list) @ [b], lTYX = (lTYX st_list)\<rparr>" 

definition setRB_enqueuex :: "'a \<Rightarrow> 'a SetRB  \<Rightarrow> 'a SetRB"
  where "setRB_enqueuex b rb =  \<lparr>  SX = (SX rb) - {(b)},  SY = (SY rb), TXY = ((TXY rb) \<union> {(b)}),  
                                        TYX = (TYX rb) \<rparr>"

definition listRB_dequeuex :: "'a \<Rightarrow> 'a ListRB \<Rightarrow> 'a ListRB"
  where "listRB_dequeuex buf st_list =  \<lparr> lSX = (lSX st_list) \<union> {buf}, lSY = (lSY st_list),
                                          lTXY = (take 1 (lTXY st_list)), lTYX = (lTYX st_list)\<rparr>" 

definition setRB_dequeuex :: "'a \<Rightarrow> 'a SetRB  \<Rightarrow> 'a SetRB"
  where "setRB_dequeuex b rb =  \<lparr>  SX = (SX rb) \<union> {(b)},  SY = (SY rb), TXY = ((TXY rb) \<union> {(b)}),  
                                   TYX = (TYX rb) - {b} \<rparr>"

lemma
  setListRefinement_enqueue: "(Language.Basic (setRB_enqueuex buf), Language.Basic (listRB_enqueuex buf)) 
        \<in> refinement_s (separable_sr (sr_set_list_enq K) (fr_id K)) \<Gamma>a \<Gamma>c"
  apply(rule refinement_s_BasicI) 
  try
proof
  oops  

lemma
  setListRefinement_dequeue: "(Language.Basic (setRB_dequeuex buf), Language.Basic (listRB_dequeuex buf)) 
        \<in> refinement_s (separable_sr (sr_set_list_deq K) (fr_id K)) \<Gamma>a \<Gamma>c"
  apply(rule refinement_s_BasicI) 
  try
proof
  oops


end