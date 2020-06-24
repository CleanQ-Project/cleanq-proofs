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



theory CleanQ_ListRBRefinement imports 
  "../Refinements"
  CleanQ_ListModel
  CleanQ_RBModel
begin

lemma
  CleanQ_listRBRefinement_enq_x: "((\<Gamma>a, CleanQ_List_enq_x_pre K buf, Language.Basic (CleanQ_List_enq_x buf)), 
                               (\<Gamma>c, CleanQ_RB_enq_x_pre K buf, Language.Basic (CleanQ_RB_enq_x buf)))
                               \<in> refinement_s (separable_lift CleanQ_RB2List CleanQ_RB2List)"
apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
  unfolding separable_lift_def CleanQ_RB2List_def CleanQ_List_enq_x_def CleanQ_List_enq_x_pre_def CleanQ_RB_enq_x_def
  CleanQ_RB_enq_x_pre_def
  unfolding CleanQ_RB_list_def
proof(auto)
  oops

lemma
  CleanQ_listRBRefinement_enq_y: "((\<Gamma>a, CleanQ_List_enq_y_pre K buf, Language.Basic (CleanQ_List_enq_y buf)), 
                               (\<Gamma>c, CleanQ_RB_enq_y_pre K buf, Language.Basic (CleanQ_RB_enq_y buf)))
                               \<in> refinement_s (separable_lift CleanQ_RB2List CleanQ_RB2List)"
  apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
   unfolding separable_lift_def CleanQ_List2Set_def  CleanQ_List_enq_y_def CleanQ_List_enq_y_pre_def CleanQ_RB_enq_y_def
  CleanQ_RB_enq_y_pre_def 
proof(auto)
   oops


lemma
  CleanQ_listRBRefinement_deq_x: "((\<Gamma>a, CleanQ_List_deq_x_pre K buf, Language.Basic (CleanQ_List_deq_x)), 
                               (\<Gamma>c, CleanQ_RB_deq_x_pre K buf, Language.Basic (CleanQ_RB_deq_x)))
                               \<in> refinement_s (separable_lift CleanQ_RB2List CleanQ_RB2List)"
  apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
    unfolding separable_lift_def  CleanQ_List_deq_x_def CleanQ_List_deq_x_pre_def CleanQ_RB_deq_x_def
   CleanQ_RB_deq_x_pre_def
  proof(auto)
    oops
 
lemma
  CleanQ_listRBRefinement_deq_y: "((\<Gamma>a, CleanQ_List_deq_y_pre K buf, Language.Basic (CleanQ_List_deq_y)), 
                               (\<Gamma>c, CleanQ_RB_deq_y_pre K buf, Language.Basic (CleanQ_RB_deq_y)))
                               \<in> refinement_s (separable_lift CleanQ_RB2List CleanQ_RB2List)"
  apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
    unfolding separable_lift_def  CleanQ_List_deq_y_def CleanQ_List_deq_y_pre_def CleanQ_RB_deq_y_def
   CleanQ_RB_deq_y_pre_def
  proof(auto)
    oops 

end