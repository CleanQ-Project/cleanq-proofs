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



section \<open>CleanQ List Model to Ring Buffer Model refinement COMPLEX to SIMPLE\<close>

text \<open>
  The second refinement is from unbounded lists to bounded buffer rings for transferring
  ownership between two agents.
\<close>

theory CleanQ_ListRBRefinement
(*<*) imports
  "../Refinements"
  CleanQ_ListModel
  CleanQ_RBModel
begin
(*>*)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue Refinement\<close>
(* ------------------------------------------------------------------------------------ *)

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

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue Refinement\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We first show some helper lemmas that connect the two preconditions on the Ring buffer
  model and the List model.   
\<close>

lemma 
  refine_hd_list_tl_ring_tyx:
  fixes buf sc
  assumes precond: "Semantic.xstate.Normal sc \<in> CleanQ_RB_deq_x_pre K buf"
  shows "buf = the (ring (rTYX sc) (tail (rTYX sc))) \<Longrightarrow> buf = hd (lTYX (CleanQ_RB2List sc))"
  using precond unfolding CleanQ_RB2List_def 
  apply auto
  by (metis (mono_tags, lifting) CleanQ_RB_Invariants.elims(2) CleanQ_RB_deq_x_possible_def 
      CleanQ_RB_deq_x_pre_def CollectD I4_rb_valid.elims(2) imageE prod.sel(1) rb_deq_def 
      rb_deq_list_was_head rb_valid_def state_simps(1))
  
  

lemma 
  refine_hd_list_tl_ring_txy:
  fixes buf sc
  assumes precond: "Semantic.xstate.Normal sc \<in> CleanQ_RB_deq_y_pre K buf"
  shows "buf = the (ring (rTXY sc) (tail (rTXY sc))) \<Longrightarrow> buf = hd (lTXY (CleanQ_RB2List sc))"
  using precond unfolding CleanQ_RB2List_def CleanQ_RB_deq_y_pre_def
  apply auto
  by (metis CleanQ_RB_deq_y_possible_def prod.sel(1) rb_deq_def rb_deq_list_was_head rb_valid_def)
  


lemma 
  deq_x_rb_pre_implies_list_pre:
  assumes precond: "Semantic.xstate.Normal sc \<in> CleanQ_RB_deq_x_pre K buf"
  shows "CleanQ_RB_Invariants K sc \<and> buf = the (ring (rTYX sc) (tail (rTYX sc))) \<and> \<not> rb_empty (rTYX sc)
         \<Longrightarrow> CleanQ_List_Invariants K (CleanQ_RB2List sc) \<and> buf = hd (lTYX (CleanQ_RB2List sc)) \<and> lTYX (CleanQ_RB2List sc) \<noteq> []"
proof -
   have precond_buf: " buf = hd (lTYX (CleanQ_RB2List sc)) \<longleftrightarrow> buf = the (ring (rTYX sc) (tail (rTYX sc)))"
       using refine_hd_list_tl_ring_tyx precond
       by (smt CleanQ_RB_deq_x_pre_def CollectD Semantic.xstate.inject(1) imageE rb_read_tail_def)
        
   have non_empty: "CleanQ_RB_deq_x_possible sc \<Longrightarrow> lTYX (CleanQ_RB2List sc) \<noteq> []" 
     using precond unfolding CleanQ_RB_deq_x_possible_def CleanQ_RB2List_def CleanQ_RB_deq_x_pre_def
     using I4_rb_valid.elims(2) rb_deq_not_empty by auto
     
      
   show ?thesis  using non_empty precond_buf CleanQ_RB_Invariants_List_Invariants      
     using precond non_empty refine_hd_list_tl_ring_tyx precond_buf 
     unfolding CleanQ_RB2List_def CleanQ_RB_deq_x_pre_def CleanQ_List_deq_x_pre_def
     by (smt CollectD imageE rb_read_tail_def state_simps(1))
 qed


lemma 
  deq_y_rb_pre_implies_list_pre:
  assumes precond: "Semantic.xstate.Normal sc \<in> CleanQ_RB_deq_y_pre K buf"
  shows "CleanQ_RB_Invariants K sc \<and> buf = the (ring (rTXY sc) (tail (rTXY sc))) \<and> \<not> rb_empty (rTXY sc) 
         \<Longrightarrow> CleanQ_List_Invariants K (CleanQ_RB2List sc) \<and> buf = hd (lTXY (CleanQ_RB2List sc)) \<and> lTXY (CleanQ_RB2List sc) \<noteq> []"
proof -
   have precond_buf: " buf = hd (lTXY (CleanQ_RB2List sc)) \<longleftrightarrow> buf = the (ring (rTXY sc) (tail (rTXY sc)))"
     using refine_hd_list_tl_ring_txy precond unfolding CleanQ_RB_deq_y_pre_def
     by (smt CollectD imageE precond rb_read_tail_def refine_hd_list_tl_ring_txy state_simps(1)) 
     
   have non_empty: "CleanQ_RB_deq_y_possible sc \<Longrightarrow> lTXY (CleanQ_RB2List sc) \<noteq> []" 
     using precond unfolding CleanQ_RB_deq_y_possible_def
     by (smt CleanQ_List_State.select_convs(3) CleanQ_RB2List_def CleanQ_RB_Invariants.simps 
         CleanQ_RB_deq_y_pre_def CollectD I4_rb_valid.simps Semantic.xstate.inject(1) image_def 
         rb_deq_not_empty)
      
   show ?thesis  using non_empty precond_buf CleanQ_RB_Invariants_List_Invariants      
     using precond non_empty refine_hd_list_tl_ring_txy precond_buf 
     unfolding CleanQ_RB2List_def CleanQ_RB_deq_y_pre_def CleanQ_List_deq_y_pre_def
     by (smt CollectD imageE rb_read_tail_def state_simps(1))   
 qed

text \<open>
  Finally the proofs for the Dequeue refinement.
\<close>

lemma
  CleanQ_listRBRefinement_deq_x:   
  assumes precond: "Semantic.xstate.Normal sc \<in> CleanQ_RB_deq_x_pre K buf" 
  shows
  "((\<Gamma>a, CleanQ_List_deq_x_pre K buf, Language.Basic (CleanQ_List_deq_x)), 
    (\<Gamma>c, CleanQ_RB_deq_x_pre K buf, Language.Basic (CleanQ_RB_deq_x)))
                               \<in> refinement_s (separable_lift CleanQ_RB2List CleanQ_RB2List)"
  apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
  unfolding separable_lift_def
proof auto
    show "\<And>sc. Semantic.xstate.Normal sc \<in> CleanQ_RB_deq_x_pre K buf \<Longrightarrow> CleanQ_RB2List (CleanQ_RB_deq_x sc) = CleanQ_List_deq_x (CleanQ_RB2List sc)" 
    using CleanQ_RB_deq_x_equal
    by (smt CleanQ_RB_deq_x_pre_def CollectD image_def state_simps(1))
next
   have core: "\<And>x. Semantic.xstate.Normal x \<in> CleanQ_RB_deq_x_pre K buf \<Longrightarrow> Semantic.xstate.Normal (CleanQ_RB2List x)
         \<in> CleanQ_List_deq_x_pre K buf"
       using deq_x_rb_pre_implies_list_pre precond CleanQ_RB_Invariants_List_Invariants 
       unfolding CleanQ_RB_deq_x_pre_def CleanQ_List_deq_x_pre_def CleanQ_RB_deq_x_possible_def
                 rb_can_deq_def rb_read_tail_def
       by (smt CleanQ_RB_deq_x_pre_def CollectD CollectI imageE image_eqI rb_can_deq_def rb_read_tail_def state_simps(1))
       
   show "\<And>xa. xa \<in> CleanQ_RB_deq_x_pre K buf \<Longrightarrow>
          (case xa of Semantic.xstate.Normal sc \<Rightarrow> Semantic.xstate.Normal (CleanQ_RB2List sc) | Abrupt sc \<Rightarrow> Abrupt (CleanQ_RB2List sc) | Semantic.xstate.Fault fc \<Rightarrow> Semantic.xstate.Fault (CleanQ_RB2List fc)
           | Semantic.xstate.Stuck \<Rightarrow> Semantic.xstate.Stuck)
          \<in> CleanQ_List_deq_x_pre K buf"     
     unfolding CleanQ_RB_deq_x_pre_def CleanQ_List_deq_x_pre_def
     apply (auto)
     using core precond unfolding CleanQ_RB_deq_x_pre_def CleanQ_List_deq_x_pre_def
     by auto
 qed


lemma
  CleanQ_listRBRefinement_deq_y:   
  assumes precond: "Semantic.xstate.Normal sc \<in> CleanQ_RB_deq_y_pre K buf" 
  shows
  "((\<Gamma>a, CleanQ_List_deq_y_pre K buf, Language.Basic (CleanQ_List_deq_y)), 
    (\<Gamma>c, CleanQ_RB_deq_y_pre K buf, Language.Basic (CleanQ_RB_deq_y)))
                               \<in> refinement_s (separable_lift CleanQ_RB2List CleanQ_RB2List)"
  apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
  unfolding separable_lift_def
proof auto
    show "\<And>sc. Semantic.xstate.Normal sc \<in> CleanQ_RB_deq_y_pre K buf \<Longrightarrow> CleanQ_RB2List (CleanQ_RB_deq_y sc) = CleanQ_List_deq_y (CleanQ_RB2List sc)" 
    using CleanQ_RB_deq_y_equal
    by (smt CleanQ_RB_deq_y_pre_def CollectD image_def state_simps(1))
next
   have core: "\<And>x. Semantic.xstate.Normal x \<in> CleanQ_RB_deq_y_pre K buf \<Longrightarrow> Semantic.xstate.Normal (CleanQ_RB2List x)
         \<in> CleanQ_List_deq_y_pre K buf"
       using deq_y_rb_pre_implies_list_pre precond CleanQ_RB_Invariants_List_Invariants 
       unfolding CleanQ_RB_deq_y_pre_def CleanQ_List_deq_y_pre_def CleanQ_RB_deq_y_possible_def
                 rb_can_deq_def rb_read_tail_def
       by (smt CleanQ_RB_deq_y_pre_def CollectD CollectI imageE image_eqI rb_can_deq_def rb_read_tail_def state_simps(1))
       

   show "\<And>xa. xa \<in> CleanQ_RB_deq_y_pre K buf \<Longrightarrow>
          (case xa of Semantic.xstate.Normal sc \<Rightarrow> Semantic.xstate.Normal (CleanQ_RB2List sc) | Abrupt sc \<Rightarrow> Abrupt (CleanQ_RB2List sc) | Semantic.xstate.Fault fc \<Rightarrow> Semantic.xstate.Fault (CleanQ_RB2List fc)
           | Semantic.xstate.Stuck \<Rightarrow> Semantic.xstate.Stuck)
          \<in> CleanQ_List_deq_y_pre K buf"     
     unfolding CleanQ_RB_deq_y_pre_def CleanQ_List_deq_x_pre_def
     apply (auto)
     using core precond unfolding CleanQ_RB_deq_y_pre_def CleanQ_List_deq_y_pre_def
     by auto
qed

end