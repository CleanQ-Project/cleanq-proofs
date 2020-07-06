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

declare [[ smt_timeout = 120 ]]

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
   show "Semantic.xstate.case_xstate (\<lambda>sc. Semantic.xstate.Normal (CleanQ_RB2List sc)) (\<lambda>sc. Abrupt (CleanQ_RB2List sc)) (\<lambda>fc. Semantic.xstate.Fault (CleanQ_RB2List fc))
     Semantic.xstate.Stuck ` CleanQ_RB_enq_x_pre K buf \<subseteq> CleanQ_List_enq_x_pre K buf"
     using core_g2 CleanQ_RB_Invariants_List_Invariants unfolding CleanQ_RB_enq_x_pre_def CleanQ_List_enq_x_pre_def
     by (smt CleanQ_List_State.select_convs(1) CleanQ_List_State.select_convs(3) CleanQ_RB2List_def CleanQ_RB_Invariants.elims(2) I2_rb_img.elims(2)
         Semantic.xstate.simps(16) disjoint_iff_not_equal image_Collect_subsetI image_def mem_Collect_eq)
qed

lemma
  CleanQ_listRBRefinement_enq_y: 
  assumes precond: "Semantic.xstate.Normal sc \<in> CleanQ_RB_enq_y_pre K buf" 
  shows
  "((\<Gamma>a, CleanQ_List_enq_y_pre K buf, Language.Basic (CleanQ_List_enq_y buf)), 
                               (\<Gamma>c, CleanQ_RB_enq_y_pre K buf, Language.Basic (CleanQ_RB_enq_y buf)))
                               \<in> refinement_s (separable_lift CleanQ_RB2List CleanQ_RB2List)"
  apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
  unfolding separable_lift_def
proof -
   show "\<And>sc. Semantic.xstate.Normal sc \<in> CleanQ_RB_enq_y_pre K buf \<Longrightarrow> CleanQ_RB2List (CleanQ_RB_enq_y buf sc) = CleanQ_List_enq_y buf (CleanQ_RB2List sc)" 
     using precond CleanQ_RB_enq_y_equal
     by (simp add: CleanQ_RB_enq_y_equal CleanQ_RB_enq_y_pre_def image_iff)
 next
   have core_g2: "Semantic.xstate.Normal (CleanQ_RB2List sc) \<in> CleanQ_List_enq_y_pre K buf" using precond
   proof -
     fix b
     have b_in_sx: "b \<in> (rSY sc) \<Longrightarrow> b \<in> lSY (CleanQ_RB2List sc)"
       by (simp add: CleanQ_RB2List_def)
     have b_notin_tyx: "b \<in> (rSY sc) \<Longrightarrow> b \<notin> set (lTYX (CleanQ_RB2List sc))" 
       using precond
       unfolding CleanQ_RB_enq_y_pre_def CleanQ_RB2List_def
       by auto
     have final: "Semantic.xstate.Normal sc \<in> CleanQ_RB_enq_y_pre K buf \<Longrightarrow> Semantic.xstate.Normal (CleanQ_RB2List sc) \<in> CleanQ_List_enq_y_pre K buf" 
       using b_in_sx b_notin_tyx precond unfolding CleanQ_RB2List_def CleanQ_RB_enq_y_pre_def CleanQ_List_enq_y_pre_def
       by fastforce
     show ?thesis using final precond
       by simp
   qed
   show "Semantic.xstate.case_xstate (\<lambda>sc. Semantic.xstate.Normal (CleanQ_RB2List sc)) (\<lambda>sc. Abrupt (CleanQ_RB2List sc)) (\<lambda>fc. Semantic.xstate.Fault (CleanQ_RB2List fc))
     Semantic.xstate.Stuck ` CleanQ_RB_enq_y_pre K buf \<subseteq> CleanQ_List_enq_y_pre K buf"
     using core_g2 CleanQ_RB_Invariants_List_Invariants unfolding CleanQ_RB_enq_y_pre_def CleanQ_List_enq_y_pre_def
     by (smt CleanQ_List_State.select_convs(2) CleanQ_List_State.select_convs(4) CleanQ_RB2List_def CleanQ_RB_Invariants.elims(2) I2_rb_img.elims(2)
         Semantic.xstate.simps(16) disjoint_iff_not_equal image_Collect_subsetI image_def mem_Collect_eq)
qed

lemma 
  refine_hd_list_tl_ring:
  fixes buf sc
  assumes precond: "Semantic.xstate.Normal sc \<in> CleanQ_RB_deq_x_pre K buf"
  shows "buf = ring (rTYX sc) (tail (rTYX sc)) \<Longrightarrow> buf = hd (lTYX (CleanQ_RB2List sc))"
  unfolding CleanQ_RB2List_def using precond 
  apply auto
  by (metis (mono_tags, lifting) CleanQ_RB_Invariants.elims(2) CleanQ_RB_deq_x_possible_def CleanQ_RB_deq_x_pre_def 
      CollectD I4_rb_valid.elims(2) imageE prod.sel(1) rb_deq_def rb_deq_list_was_head state_simps(1))   

lemma
  CleanQ_listRBRefinement_deq_x:   
  assumes precond: "Semantic.xstate.Normal sc \<in> CleanQ_RB_deq_x_pre K buf" 
  shows
  "((\<Gamma>a, CleanQ_List_deq_x_pre K buf, Language.Basic (CleanQ_List_deq_x)), 
    (\<Gamma>c, CleanQ_RB_deq_x_pre K buf, Language.Basic (CleanQ_RB_deq_x)))
                               \<in> refinement_s (separable_lift CleanQ_RB2List CleanQ_RB2List)"
  apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
  unfolding separable_lift_def
proof -
    show "\<And>sc. Semantic.xstate.Normal sc \<in> CleanQ_RB_deq_x_pre K buf \<Longrightarrow> CleanQ_RB2List (CleanQ_RB_deq_x sc) = CleanQ_List_deq_x (CleanQ_RB2List sc)" 
    using CleanQ_RB_deq_x_equal
    by (smt CleanQ_RB_deq_x_pre_def CollectD image_def state_simps(1))
next
   fix b
   have b_in_tyx: "b \<in> set (CleanQ_RB_list (rTYX sc)) \<Longrightarrow> b \<in> set (lTYX (CleanQ_RB2List sc))"
      by (simp add: CleanQ_RB2List_def)
   have b_notin_sx: "b \<in> set (CleanQ_RB_list (rTYX sc)) \<Longrightarrow> b \<notin> (lSX (CleanQ_RB2List sc))" 
     using precond
     unfolding CleanQ_RB_deq_x_pre_def CleanQ_RB2List_def
     by auto
   have non_empty: "CleanQ_RB_deq_x_possible sc \<Longrightarrow> lTYX (CleanQ_RB2List sc) \<noteq> []" 
     using precond unfolding CleanQ_RB_deq_x_possible_def
   by (metis (no_types, lifting) CleanQ_List_State.select_convs(4) CleanQ_RB2List_def 
      CleanQ_RB_Invariants.elims(2) CleanQ_RB_deq_x_pre_def CollectD I3_rb_img.elims(2) 
      I4_rb_valid.elims(2) image_iff list.sel(2) rb_deq_list_not_in rb_deq_list_tail rb_deq_list_was_in state_simps(1))
   have core_g2: "Semantic.xstate.Normal (CleanQ_RB2List sc) \<in> CleanQ_List_deq_x_pre K buf" using precond
   proof -
     have precond_buf: " buf = hd (lTYX (CleanQ_RB2List sc)) \<longleftrightarrow> buf = ring (rTYX sc) (tail (rTYX sc))"
       using precond refine_hd_list_tl_ring
       by (smt CleanQ_RB_deq_x_pre_def CollectD imageE state_simps(1))

     have final: "Semantic.xstate.Normal sc \<in> CleanQ_RB_deq_x_pre K buf \<Longrightarrow> Semantic.xstate.Normal (CleanQ_RB2List sc) \<in> CleanQ_List_deq_x_pre K buf" 
       using b_in_tyx b_notin_sx precond non_empty refine_hd_list_tl_ring precond_buf unfolding CleanQ_RB2List_def CleanQ_RB_deq_x_pre_def CleanQ_List_deq_x_pre_def
       by force
     show ?thesis using final precond
       by simp
   qed
   show "Semantic.xstate.case_xstate (\<lambda>sc. Semantic.xstate.Normal (CleanQ_RB2List sc)) (\<lambda>sc. Abrupt (CleanQ_RB2List sc)) 
         (\<lambda>fc. Semantic.xstate.Fault (CleanQ_RB2List fc)) Semantic.xstate.Stuck ` CleanQ_RB_deq_x_pre K buf \<subseteq> CleanQ_List_deq_x_pre K buf"
     using core_g2 CleanQ_RB_Invariants_List_Invariants refine_hd_list_tl_ring non_empty
     unfolding CleanQ_RB_deq_x_pre_def CleanQ_List_deq_x_pre_def rb_empty_def
     sorry
 
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