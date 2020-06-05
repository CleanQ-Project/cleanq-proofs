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



theory CleanQ_SetListRefinement imports 
  "../Refinements"
  CleanQ_SetModel
  CleanQ_ListModel
begin


definition sr_set_list :: "'a CleanQ_List_State \<Rightarrow> 'a CleanQ_Set_State"
  where "sr_set_list st_c = \<lparr>SX = lSX st_c, SY = lSY st_c, 
                             TXY = set (lTXY st_c), TYX = set (lTYX st_c)\<rparr>"

definition fr_id :: "'a CleanQ_List_State \<Rightarrow> 'a CleanQ_Set_State"
  where "fr_id = sr_set_list"

lemma
  CleanQ_setListRefinement_enq_x: "((\<Gamma>a, CleanQ_Set_enq_x_pre K buf, Language.Basic (CleanQ_Set_enq_x buf)), 
                               (\<Gamma>c, CleanQ_List_enq_x_pre K buf, Language.Basic (CleanQ_List_enq_x buf)))
                               \<in> refinement_s (separable_lift sr_set_list fr_id)"
apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
  unfolding separable_lift_def sr_set_list_def CleanQ_Set_enq_x_def CleanQ_Set_enq_x_pre_def CleanQ_List_enq_x_def
  CleanQ_List_enq_x_pre_def
  by(auto)

lemma
  CleanQ_setListRefinement_enq_y: "((\<Gamma>a, CleanQ_Set_enq_y_pre K buf, Language.Basic (CleanQ_Set_enq_y buf)), 
                               (\<Gamma>c, CleanQ_List_enq_y_pre K buf, Language.Basic (CleanQ_List_enq_y buf)))
                               \<in> refinement_s (separable_lift sr_set_list fr_id)"
apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
  unfolding separable_lift_def sr_set_list_def  CleanQ_Set_enq_y_def CleanQ_Set_enq_y_pre_def CleanQ_List_enq_y_def
  CleanQ_List_enq_y_pre_def
  by(auto)

lemma
  CleanQ_setListRefinement_deq_x: "((\<Gamma>a, CleanQ_Set_deq_x_pre K buf, Language.Basic (CleanQ_Set_deq_x buf)), 
                               (\<Gamma>c, CleanQ_List_deq_x_pre K buf, Language.Basic (CleanQ_List_deq_x buf)))
                               \<in> refinement_s (separable_lift sr_set_list fr_id)"
apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
  unfolding separable_lift_def sr_set_list_def CleanQ_Set_deq_x_def CleanQ_Set_deq_x_pre_def CleanQ_List_deq_x_def
  CleanQ_List_deq_x_pre_def
  by(auto)

lemma
  CleanQ_setListRefinement_deq_y: "((\<Gamma>a, CleanQ_Set_deq_y_pre K buf, Language.Basic (CleanQ_Set_deq_y buf)), 
                               (\<Gamma>c, CleanQ_List_deq_y_pre K buf, Language.Basic (CleanQ_List_deq_y buf)))
                               \<in> refinement_s (separable_lift sr_set_list fr_id)"
apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
  unfolding separable_lift_def sr_set_list_def CleanQ_Set_deq_y_def CleanQ_Set_deq_y_pre_def CleanQ_List_deq_y_def
  CleanQ_List_deq_y_pre_def
  by(auto)

end