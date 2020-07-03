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
  CleanQ_listRBRefinement_enq_x: 
  assumes precond: "Semantic.xstate.Normal sc \<in> CleanQ_RB_enq_x_pre K buf" 
  shows
  "((\<Gamma>a, CleanQ_List_enq_x_pre K buf, Language.Basic (CleanQ_List_enq_x buf)), 
                               (\<Gamma>c, CleanQ_RB_enq_x_pre K buf, Language.Basic (CleanQ_RB_enq_x buf)))
                               \<in> refinement_s (separable_lift CleanQ_RB2List CleanQ_RB2List)"
  apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
  unfolding separable_lift_def
proof -
   show "\<And>sc. Semantic.xstate.Normal sc \<in> CleanQ_RB_enq_x_pre K buf \<Longrightarrow> CleanQ_RB2List (CleanQ_RB_enq_x buf sc) = CleanQ_List_enq_x buf (CleanQ_RB2List sc)" 
     using precond CleanQ_RB_enq_x_equal
     by (simp add: CleanQ_RB_enq_x_equal CleanQ_RB_enq_x_pre_def image_iff)
 next
   have core_g2: "Semantic.xstate.Normal (CleanQ_RB2List sc) \<in> CleanQ_List_enq_x_pre K buf" using precond
   proof -
     fix b
     have b_in_sx: "b \<in> (rSX sc) \<Longrightarrow> b \<in> lSX (CleanQ_RB2List sc)"
       by (simp add: CleanQ_RB2List_def)
     have b_notin_txy: "b \<in> (rSX sc) \<Longrightarrow> b \<notin> set (lTXY (CleanQ_RB2List sc))" 
       using precond
       unfolding CleanQ_RB_enq_x_pre_def CleanQ_RB2List_def
       by auto
     have final: "Semantic.xstate.Normal sc \<in> CleanQ_RB_enq_x_pre K buf \<Longrightarrow> Semantic.xstate.Normal (CleanQ_RB2List sc) \<in> CleanQ_List_enq_x_pre K buf" 
       using b_in_sx b_notin_txy precond unfolding CleanQ_RB2List_def CleanQ_RB_enq_x_pre_def CleanQ_List_enq_x_pre_def
       by (smt CleanQ_List_State.select_convs(1) CleanQ_List_State.select_convs(3) CleanQ_RB2List_def CleanQ_RB_Invariants.elims(2) 
           CleanQ_RB_Invariants_List_Invariants I2_rb_img.elims(2) Semantic.xstate.inject(1) 
           disjoint_insert(1) imageE image_eqI insert_absorb mem_Collect_eq)
     show ?thesis using final precond
       by blast
   qed

   have core:"\<And>xa. xa \<in> CleanQ_RB_enq_x_pre K buf \<Longrightarrow>
          (case xa of Semantic.xstate.Normal sc \<Rightarrow> Semantic.xstate.Normal (CleanQ_RB2List sc) | Abrupt sc \<Rightarrow> Abrupt (CleanQ_RB2List sc)
           | Semantic.xstate.Fault fc \<Rightarrow> Semantic.xstate.Fault (CleanQ_RB2List fc) | Semantic.xstate.Stuck \<Rightarrow> Semantic.xstate.Stuck)
          \<in> CleanQ_List_enq_x_pre K buf" 
     sorry

   show "Semantic.xstate.case_xstate (\<lambda>sc. Semantic.xstate.Normal (CleanQ_RB2List sc)) (\<lambda>sc. Abrupt (CleanQ_RB2List sc)) (\<lambda>fc. Semantic.xstate.Fault (CleanQ_RB2List fc))
     Semantic.xstate.Stuck `
    CleanQ_RB_enq_x_pre K buf
    \<subseteq> CleanQ_List_enq_x_pre K buf" using core
     by blast
qed


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