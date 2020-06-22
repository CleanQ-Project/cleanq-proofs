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



lemma
  CleanQ_setListRefinement_enq_x: "((\<Gamma>a, CleanQ_Set_enq_x_pre K buf, Language.Basic (CleanQ_Set_enq_x buf)), 
                               (\<Gamma>c, CleanQ_List_enq_x_pre K buf, Language.Basic (CleanQ_List_enq_x buf)))
                               \<in> refinement_s (separable_lift CleanQ_List2Set CleanQ_List2Set)"
apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
  unfolding separable_lift_def CleanQ_List2Set_def CleanQ_Set_enq_x_def CleanQ_Set_enq_x_pre_def CleanQ_List_enq_x_def
  CleanQ_List_enq_x_pre_def
  by(auto)

lemma
  CleanQ_setListRefinement_enq_y: "((\<Gamma>a, CleanQ_Set_enq_y_pre K buf, Language.Basic (CleanQ_Set_enq_y buf)), 
                               (\<Gamma>c, CleanQ_List_enq_y_pre K buf, Language.Basic (CleanQ_List_enq_y buf)))
                               \<in> refinement_s (separable_lift CleanQ_List2Set CleanQ_List2Set)"
  apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
   unfolding separable_lift_def CleanQ_List2Set_def  CleanQ_Set_enq_y_def CleanQ_Set_enq_y_pre_def CleanQ_List_enq_y_def
  CleanQ_List_enq_y_pre_def
  by(auto)

lemma
  CleanQ_setListRefinement_deq_x: "((\<Gamma>a, CleanQ_Set_deq_x_pre K buf, Language.Basic (CleanQ_Set_deq_x buf)), 
                               (\<Gamma>c, CleanQ_List_deq_x_pre K buf, Language.Basic (CleanQ_List_deq_x)))
                               \<in> refinement_s (separable_lift CleanQ_List2Set CleanQ_List2Set)"
  apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
    unfolding separable_lift_def  CleanQ_Set_deq_x_def CleanQ_Set_deq_x_pre_def CleanQ_List_deq_x_def
   CleanQ_List_deq_x_pre_def
   apply(auto)
 unfolding CleanQ_List2Set_def  
   apply(simp add:list_set_hd_tl_subtract)
  by(auto)
  

lemma
  CleanQ_setListRefinement_deq_y: "((\<Gamma>a, CleanQ_Set_deq_y_pre K buf, Language.Basic (CleanQ_Set_deq_y buf)), 
                               (\<Gamma>c, CleanQ_List_deq_y_pre K buf, Language.Basic (CleanQ_List_deq_y)))
                               \<in> refinement_s (separable_lift CleanQ_List2Set CleanQ_List2Set)"
apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
  unfolding separable_lift_def  CleanQ_Set_deq_y_def CleanQ_Set_deq_y_pre_def CleanQ_List_deq_y_def
  CleanQ_List_deq_y_pre_def
   apply(auto)
  unfolding CleanQ_List2Set_def
   apply(simp add:list_set_hd_tl_subtract)
  by(auto)
  
end