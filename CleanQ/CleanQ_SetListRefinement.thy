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


(* ==================================================================================== *)
subsection \<open>Set Pre- and post- conditions\<close>
(* ==================================================================================== *)

definition CleanQ_Set_deq_x_pre :: 
  "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_deq_x_pre K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> TYX rb }"

definition CleanQ_Set_deq_x_post :: 
  "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_deq_x_post K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> SX rb }"

definition CleanQ_Set_deq_y_pre :: 
  "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_deq_y_pre K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> TXY rb }"

definition CleanQ_Set_deq_y_post :: 
  "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_deq_y_post K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> SY rb }"


definition CleanQ_Set_enq_x_pre :: 
  "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_enq_x_pre K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> SX rb }"

definition CleanQ_Set_enq_x_post :: 
  "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_enq_x_post K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> TXY rb }"

definition CleanQ_Set_enq_y_pre :: 
  "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_enq_y_pre K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> SY rb }"

definition CleanQ_Set_enq_y_post :: 
  "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_Set_State, 'a CleanQ_Set_State) Semantic.xstate set"
  where "CleanQ_Set_enq_y_post K b = Semantic.Normal ` { rb. I1 rb K \<and> I2 rb \<and> b \<in> TYX rb }"


(* ==================================================================================== *)
subsection \<open>List Pre- conditions\<close>
(* ==================================================================================== *)

definition CleanQ_List_enq_x_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_List_State, 'a CleanQ_List_State) Semantic.xstate set"
  where "CleanQ_List_enq_x_pre K b =  Semantic.Normal ` {rb. CleanQ_List_Invariants K rb \<and> b \<in> lSX rb \<and> b \<notin> set (lTXY rb)}"

definition CleanQ_List_enq_y_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_List_State, 'a CleanQ_List_State) Semantic.xstate set"
  where "CleanQ_List_enq_y_pre K b = Semantic.Normal ` {rb. CleanQ_List_Invariants K rb \<and> b \<in> lSY rb \<and> b \<notin> set (lTYX rb)}"

definition CleanQ_List_deq_x_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_List_State, 'a CleanQ_List_State) Semantic.xstate set"        
  where "CleanQ_List_deq_x_pre K buf = Semantic.Normal ` {rb.  CleanQ_List_Invariants K rb \<and>
                                                          (lTYX rb) \<noteq> [] \<and> buf = hd (lTYX rb) }"

definition CleanQ_List_deq_y_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_List_State, 'a CleanQ_List_State) Semantic.xstate set"        
  where "CleanQ_List_deq_y_pre K buf = Semantic.Normal ` {rb. CleanQ_List_Invariants K rb \<and>
                                                          (lTXY rb) \<noteq> [] \<and> buf = hd (lTXY rb) }"
(* ==================================================================================== *)
subsection \<open>Refinement\<close>
(* ==================================================================================== *)


lemma
  CleanQ_setListRefinement_enq_x: "((\<Gamma>a, CleanQ_Set_enq_x_pre K buf, Language.Basic (CleanQ_Set_enq_x buf)), 
                               (\<Gamma>c, CleanQ_List_enq_x_pre K buf, Language.Basic (CleanQ_List_enq_x buf)))
                               \<in> refinement_s (separable_lift CleanQ_List2Set CleanQ_List2Set)"
apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
  unfolding separable_lift_def CleanQ_List2Set_def CleanQ_List_enq_x_def CleanQ_Set_enq_x_def 
  CleanQ_List_enq_x_pre_def CleanQ_Set_enq_x_pre_def 
   apply auto
  by (simp add: CleanQ_List2Set_def CleanQ_List_Invariants_def I1_list_img_lift I2_list_img_lift)

lemma
  CleanQ_setListRefinement_enq_y: "((\<Gamma>a, CleanQ_Set_enq_y_pre K buf, Language.Basic (CleanQ_Set_enq_y buf)), 
                               (\<Gamma>c, CleanQ_List_enq_y_pre K buf, Language.Basic (CleanQ_List_enq_y buf)))
                               \<in> refinement_s (separable_lift CleanQ_List2Set CleanQ_List2Set)"
  apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
   unfolding separable_lift_def CleanQ_List2Set_def  CleanQ_Set_enq_y_def CleanQ_Set_enq_y_pre_def CleanQ_List_enq_y_def
  CleanQ_List_enq_y_pre_def
   apply(auto)
   by (simp add: CleanQ_List2Set_def CleanQ_List_Invariants_def I1_list_img_lift I2_list_img_lift)

lemma
  CleanQ_setListRefinement_deq_x: "((\<Gamma>a, CleanQ_Set_deq_x_pre K buf, Language.Basic (CleanQ_Set_deq_x buf)), 
                               (\<Gamma>c, CleanQ_List_deq_x_pre K buf, Language.Basic (CleanQ_List_deq_x)))
                               \<in> refinement_s (separable_lift CleanQ_List2Set CleanQ_List2Set)"
  apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
  unfolding separable_lift_def  CleanQ_Set_deq_x_def CleanQ_Set_deq_x_pre_def CleanQ_List_deq_x_def
   CleanQ_List_deq_x_pre_def CleanQ_List_Invariants_def CleanQ_List2Set_def
  apply auto
  apply (simp add: list.set_sel(2))
  apply (metis I3_def distinct.simps(2) hd_Cons_tl)
  using hd_Cons_tl apply force
  by (simp add: CleanQ_List2Set_def I1_list_img_lift I2_list_img_lift)

lemma
  CleanQ_setListRefinement_deq_y: "((\<Gamma>a, CleanQ_Set_deq_y_pre K buf, Language.Basic (CleanQ_Set_deq_y buf)), 
                               (\<Gamma>c, CleanQ_List_deq_y_pre K buf, Language.Basic (CleanQ_List_deq_y)))
                               \<in> refinement_s (separable_lift CleanQ_List2Set CleanQ_List2Set)"
apply(rule refinement_s_BasicI) (* Problem applying this after unfolding*)
  unfolding separable_lift_def  CleanQ_Set_deq_y_def CleanQ_Set_deq_y_pre_def CleanQ_List_deq_y_def
  CleanQ_List_deq_y_pre_def CleanQ_List_Invariants_def CleanQ_List2Set_def
  apply auto
  apply (simp add: list.set_sel(2))
  apply (metis I3_def distinct.simps(2) hd_Cons_tl)
  using hd_Cons_tl apply force
  by (simp add: CleanQ_List2Set_def I1_list_img_lift I2_list_img_lift)
  
end