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
  where "I3 st_list \<longleftrightarrow> distinct (lTXY st_list @ lTYX st_list)"


definition sr_set_list :: "'a ListRB \<Rightarrow> 'a SetRB"
  where "sr_set_list st_c = \<lparr>SX = lSX st_c, SY = lSY st_c, 
                             TXY = set (lTXY st_c), TYX = set (lTYX st_c)\<rparr>"

(* fun I1_img :: "'a ListRB \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1_img rb K \<longleftrightarrow> I1 (sr_set_list rb) K" *)

text \<open>The union of all sets is constant. Image for ListRB\<close>
fun I1_img :: "'a ListRB \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1_img rb K \<longleftrightarrow> ((lSX rb) \<union> (lSY rb) \<union> set (lTXY rb) \<union> set (lTYX rb)) = K"

text \<open>All pairwise intersections are empty. Image for ListRB.\<close>
fun I2_img :: "'a ListRB \<Rightarrow> bool"
  where "I2_img rb \<longleftrightarrow> lSX rb \<inter> lSY rb = {} \<and> lSX rb \<inter> set (lTXY rb) = {} \<and> lSX rb \<inter> set (lTYX rb) = {} \<and> 
    lSY rb \<inter> set (lTXY rb) = {} \<and> lSY rb \<inter> set (lTYX rb) = {} \<and> 
    set (lTXY rb) \<inter> set (lTYX rb) = {}"


definition fr_id :: "'a ListRB \<Rightarrow> 'a SetRB"
  where "fr_id = sr_set_list"

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

definition set_pre_enq :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a SetRB, 'a SetRB) Semantic.xstate set"        
  where "set_pre_enq K buf = Semantic.Normal ` {rb. I1 rb K \<and> I2 rb \<and> buf \<in> SX rb \<and> buf \<notin> TXY rb}"

definition list_pre_enq :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a ListRB, 'a ListRB) Semantic.xstate set"        
  where "list_pre_enq K buf = Semantic.Normal ` {rb. I1_img rb K \<and> I2_img rb \<and> I3 rb \<and>
                                            buf \<in> lSX rb \<and> buf \<notin> set (lTXY rb)}"

lemma
  setListRefinement_enqueue: "((\<Gamma>a, set_pre_enq K buf, Language.Basic (setRB_enqueuex buf)), 
                               (\<Gamma>c, list_pre_enq K buf, Language.Basic (listRB_enqueuex buf)))
                               \<in> refinement_s (separable_lift sr_set_list fr_id)"
apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
  unfolding list_pre_enq_def separable_lift_def sr_set_list_def listRB_enqueuex_def setRB_enqueuex_def 
  set_pre_enq_def
  by(auto)

end