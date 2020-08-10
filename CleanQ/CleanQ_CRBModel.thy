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



section \<open>CleanQ Abstract Concurrent Ring Buffer Model\<close>

text \<open>
  This model is the concurrent version of the ring buffer. The \verb+enqueue+ and \verb+deqeue+
  operations are executed in two steps and the frame condition needs to be relaxed in order
  to allow the "other" side to take concurrent actions. 
\<close>

theory CleanQ_CRBModel 
(*<*) 
  imports Main "../Simpl/Vcg"  "../Complx/OG_Hoare" CleanQ_RB CleanQ_RBModel
(*>*)  
begin
declare[[show_types]]

(* ==================================================================================== *)
subsection \<open>CleanQ Abstract Concurrent Ring Buffer Model State\<close>
(* ==================================================================================== *)

text \<open>
  the model is exactly the same and we reuse the RB Model. 
\<close>

(*<*)
(* Define some global variables to make Simpl/Complex proofs work *)
record 'g CleanQ_RB_State_vars = 
  RingCRB_'  :: "nat CleanQ_RB_State"
(*>*)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Weak frame condition\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  Assuming a two concurrently acting agents, we can not assume that all of the RB state
  stays the same. In order to model this, we have to weaken the frame condition which
  we up to now implicitly used. \<close>

definition frame_rb_weak_x :: "'a CleanQ_RB_State \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> bool"
  where "frame_rb_weak_x st' st \<longleftrightarrow> rSX st = rSX st' \<and> frame_rb_weak_left (rTXY st') (rTXY st) \<and> 
                                    frame_rb_weak_right (rTYX st') (rTYX st) \<and> 
                                    rSY st' \<union> set (rb_delta_tail_st (rTXY st') (rTXY st)) = (set (rb_delta_head_st (rTYX st') (rTYX st)) \<union> 
                                    rSY st) \<and> distinct (rb_delta_head_st (rTYX st') (rTYX st)) \<and> 
                                    rSY st \<inter> set (rb_delta_head_st (rTYX st') (rTYX st)) = {}" 


definition frame_rb_weak_y :: "'a CleanQ_RB_State \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> bool"
  where "frame_rb_weak_y st' st \<longleftrightarrow> rSY st = rSY st' \<and> frame_rb_weak_left (rTYX st') (rTYX st) \<and>
                                    frame_rb_weak_right (rTXY st') (rTXY st) \<and>
                                    rSX st' \<union> set (rb_delta_tail_st (rTYX st') (rTYX st)) = (set (rb_delta_head_st (rTXY st') (rTXY st)) \<union> 
                                    rSX st) \<and> distinct (rb_delta_head_st (rTXY st') (rTXY st)) \<and> 
                                    rSX st \<inter> set (rb_delta_head_st (rTXY st') (rTXY st)) = {}" 


lemma frame_rb_s_w_x:
 "frame_rb_strong st' st \<Longrightarrow> frame_rb_weak_x st' st"
  unfolding frame_rb_weak_x_def frame_rb_strong_def frame_rb_weak_left_def
  frame_rb_weak_right_def rb_delta_tail_st_def rb_delta_head_st_def
  by (simp add: rb_delta_head_def rb_delta_tail_def rb_incr_head_n_delta_def 
      rb_incr_head_n_delta_map_def rb_incr_tail_n_delta_def rb_incr_tail_n_delta_map_def)

lemma frame_rb_s_w_y:
  "frame_rb_strong dev' dev \<Longrightarrow> frame_rb_weak_y dev' dev"
  unfolding frame_rb_weak_y_def frame_rb_strong_def frame_rb_weak_left_def
  frame_rb_weak_right_def rb_delta_tail_st_def rb_delta_head_st_def
  by (simp add: rb_delta_head_def rb_delta_tail_def rb_incr_head_n_delta_def 
      rb_incr_head_n_delta_map_def rb_incr_tail_n_delta_def rb_incr_tail_n_delta_map_def)
  
lemma frame_weak_x_tl_delta: 
  assumes Inv: "CleanQ_RB_Invariants K rb'" and
          frame: "frame_rb_weak_x rb' rb"
  shows"map (the \<circ> ring (rTXY rb')) (rb_valid_entries (rTXY rb')) =
        rb_delta_tail_st (rTXY rb') (rTXY rb) @ map (the \<circ> ring (rTXY rb)) (rb_valid_entries (rTXY rb))"
  unfolding rb_delta_tail_st_def rb_incr_tail_n_delta_map_def rb_incr_tail_n_delta_def
  by (metis (no_types, hide_lams) frame frame_rb_weak_x_def rb_delta_tail_incr rb_delta_tail_st_def 
      rb_incr_tail_n_delta_def rb_incr_tail_n_delta_map_def) 

lemma frame_weak_y_tl_delta: 
  assumes Inv: "CleanQ_RB_Invariants K rb'" and
          frame: "frame_rb_weak_y rb' rb"
  shows"map (the \<circ> ring (rTYX rb')) (rb_valid_entries (rTYX rb')) =
        rb_delta_tail_st (rTYX rb') (rTYX rb) @ map (the \<circ> ring (rTYX rb)) (rb_valid_entries (rTYX rb))"
  unfolding rb_delta_tail_st_def rb_incr_tail_n_delta_map_def rb_incr_tail_n_delta_def
  by (metis (no_types, hide_lams) frame frame_rb_weak_y_def rb_delta_tail_incr rb_delta_tail_st_def 
      rb_incr_tail_n_delta_def rb_incr_tail_n_delta_map_def) 

lemma frame_weak_x_hd_delta:
  assumes Inv: "CleanQ_RB_Invariants K rb'" and
          frame: "frame_rb_weak_x rb' rb"
  shows"map (the \<circ> ring (rTYX rb')) (rb_valid_entries (rTYX rb')) @ rb_delta_head_st (rTYX rb') (rTYX rb) =
        map (the \<circ> ring (rTYX rb)) (rb_valid_entries (rTYX rb))"
  unfolding rb_delta_head_st_def rb_incr_head_n_delta_map_def rb_incr_head_n_delta_def
  using frame rb_delta_head_incr unfolding frame_rb_weak_x_def
  by (metis rb_delta_head_st_def rb_incr_head_n_delta_def rb_incr_head_n_delta_map_def) 


lemma frame_weak_y_hd_delta:
  assumes Inv: "CleanQ_RB_Invariants K rb'" and
          frame: "frame_rb_weak_y rb' rb"
  shows"map (the \<circ> ring (rTXY rb')) (rb_valid_entries (rTXY rb')) @ rb_delta_head_st (rTXY rb') (rTXY rb) =
        map (the \<circ> ring (rTXY rb)) (rb_valid_entries (rTXY rb))"
  unfolding rb_delta_head_st_def rb_incr_head_n_delta_map_def rb_incr_head_n_delta_def
  using frame rb_delta_head_incr unfolding frame_rb_weak_y_def
  by (metis rb_delta_head_st_def rb_incr_head_n_delta_def rb_incr_head_n_delta_map_def) 

lemma frame_weak_x_sy_delta:
  assumes Inv: "CleanQ_RB_Invariants K rb'" and
          frame: "frame_rb_weak_x rb' rb"
        shows "rSY rb' \<union> set (rb_delta_tail_st (rTXY rb') (rTXY rb)) = set (rb_delta_head_st (rTYX rb') (rTYX rb)) \<union> rSY rb"
  using frame unfolding frame_rb_weak_x_def
  by linarith

lemma frame_weak_y_sx_delta:
  assumes Inv: "CleanQ_RB_Invariants K rb'" and
          frame: "frame_rb_weak_y rb' rb"
        shows "rSX rb' \<union> set (rb_delta_tail_st (rTYX rb') (rTYX rb)) = set (rb_delta_head_st (rTXY rb') (rTXY rb)) \<union> rSX rb"
  using frame unfolding frame_rb_weak_y_def
  by linarith

lemma frame_weak_x_sy:
  assumes Inv: "CleanQ_RB_Invariants K rb'" and
          frame: "frame_rb_weak_x rb' rb"
  shows "(rSY rb) \<inter> set (rb_delta_head_st (rTYX rb') (rTYX rb)) = {}"
  using frame unfolding frame_rb_weak_x_def
  by blast


lemma frame_weak_y_sy:
  assumes Inv: "CleanQ_RB_Invariants K rb'" and
          frame: "frame_rb_weak_y rb' rb"
  shows "(rSX rb) \<inter> set (rb_delta_head_st (rTXY rb') (rTXY rb)) = {}"
  using frame unfolding frame_rb_weak_y_def
  by blast


text \<open>Finally we show that the RB weak frame condition refines the List weak frame condition.\<close>

lemma frame_rb_weak_x_list_weak:
  fixes rb rb' K
  assumes I1: "CleanQ_RB_Invariants K rb'"
      and frame: "frame_rb_weak_x rb' rb"
    shows "frame_list_weak (lTXY (CleanQ_RB2List rb'), lSY (CleanQ_RB2List rb'), lTYX (CleanQ_RB2List rb'), lSX (CleanQ_RB2List rb')) 
                           (lTXY (CleanQ_RB2List rb), lSY (CleanQ_RB2List rb), lTYX (CleanQ_RB2List rb), lSX (CleanQ_RB2List rb))"
  unfolding CleanQ_RB2List_def CleanQ_RB_list_def
  apply auto 
proof -
  show "\<And>x. x \<in> rSX rb' \<Longrightarrow> x \<in> rSX rb"
    by (metis frame frame_rb_weak_x_def) 
  show " \<And>x. x \<in> rSX rb \<Longrightarrow> x \<in> rSX rb'"
    by (metis frame frame_rb_weak_x_def)
  show "\<exists>\<delta>aB::'a list.
       map (the \<circ> ring (rTXY rb')) (rb_valid_entries (rTXY rb')) = \<delta>aB @ map (the \<circ> ring (rTXY rb)) (rb_valid_entries (rTXY rb)) \<and>
       (\<exists>\<delta>Bc::'a list.
           rSY rb' \<union> set \<delta>aB = set \<delta>Bc \<union> rSY rb \<and>
           map (the \<circ> ring (rTYX rb')) (rb_valid_entries (rTYX rb')) @ \<delta>Bc = map (the \<circ> ring (rTYX rb)) (rb_valid_entries (rTYX rb)) \<and> rSY rb \<inter> set \<delta>Bc = {} \<and> distinct \<delta>Bc)"
  using frame unfolding frame_rb_weak_x_def frame_rb_weak_left_def
  proof
    define \<delta>xy where "\<delta>xy = rb_delta_tail_st (rTXY rb') (rTXY rb)"
    define \<delta>yx where "\<delta>yx = rb_delta_head_st (rTYX rb') (rTYX rb)"
  
    have c1: "map (the \<circ> ring (rTXY rb')) (rb_valid_entries (rTXY rb')) = \<delta>xy @ map (the \<circ> ring (rTXY rb)) (rb_valid_entries (rTXY rb))"
      using I1 \<delta>xy_def frame frame_weak_x_tl_delta by blast
  
    have c2: "map (the \<circ> ring (rTYX rb')) (rb_valid_entries (rTYX rb')) @ \<delta>yx = map (the \<circ> ring (rTYX rb)) (rb_valid_entries (rTYX rb))"
      using I1 \<delta>yx_def frame frame_weak_x_hd_delta by blast
    
    have c3: "rSY rb' \<union> set \<delta>xy = set \<delta>yx \<union> rSY rb "
      using I1 \<delta>xy_def \<delta>yx_def frame frame_weak_x_sy_delta by blast 
  
    from I1 have c4: "distinct \<delta>yx"
      using \<delta>yx_def frame frame_rb_weak_x_def by blast 
  
    from \<delta>yx_def frame have c5: "rSY rb \<inter> set \<delta>yx = {}" 
      unfolding frame_rb_weak_x_def
      by blast 
    
    show ?thesis using c1 c2 c3 c4 c5
      by blast
  qed
qed

lemma frame_rb_weak_y_list_weak:
  fixes rb rb' K
  assumes I1: "CleanQ_RB_Invariants K rb'"
      and frame: "frame_rb_weak_y rb' rb"
    shows "frame_list_weak (lTYX (CleanQ_RB2List rb'), lSX (CleanQ_RB2List rb'), lTXY (CleanQ_RB2List rb'), lSY (CleanQ_RB2List rb')) 
                           (lTYX (CleanQ_RB2List rb), lSX (CleanQ_RB2List rb), lTXY (CleanQ_RB2List rb), lSY (CleanQ_RB2List rb))"
  unfolding CleanQ_RB2List_def CleanQ_RB_list_def
  apply auto 
proof -
  show "\<And>x. x \<in> rSY rb' \<Longrightarrow> x \<in> rSY rb"
    by (metis frame frame_rb_weak_y_def) 
  show " \<And>x. x \<in> rSY rb \<Longrightarrow> x \<in> rSY rb'"
    by (metis frame frame_rb_weak_y_def)
  show "\<exists>\<delta>aB::'a list.
       map (the \<circ> ring (rTYX rb')) (rb_valid_entries (rTYX rb')) = \<delta>aB @ map (the \<circ> ring (rTYX rb)) (rb_valid_entries (rTYX rb)) \<and>
       (\<exists>\<delta>Bc::'a list.
           rSX rb' \<union> set \<delta>aB = set \<delta>Bc \<union> rSX rb \<and>
           map (the \<circ> ring (rTXY rb')) (rb_valid_entries (rTXY rb')) @ \<delta>Bc = map (the \<circ> ring (rTXY rb)) (rb_valid_entries (rTXY rb)) \<and> rSX rb \<inter> set \<delta>Bc = {} \<and> distinct \<delta>Bc)"
  using frame unfolding frame_rb_weak_y_def frame_rb_weak_left_def
  proof
  
    define \<delta>xy where "\<delta>xy = rb_delta_tail_st (rTYX rb') (rTYX rb)"
    define \<delta>yx where "\<delta>yx = rb_delta_head_st (rTXY rb') (rTXY rb)"
  
    have c1: "map (the \<circ> ring (rTYX rb')) (rb_valid_entries (rTYX rb')) = \<delta>xy @ map (the \<circ> ring (rTYX rb)) (rb_valid_entries (rTYX rb))"
      using I1 \<delta>xy_def frame frame_weak_y_tl_delta by blast
  
    have c2: "map (the \<circ> ring (rTXY rb')) (rb_valid_entries (rTXY rb')) @ \<delta>yx = map (the \<circ> ring (rTXY rb)) (rb_valid_entries (rTXY rb))"
      using I1 \<delta>yx_def frame frame_weak_y_hd_delta by blast
    
    have c3: "rSX rb' \<union> set \<delta>xy = set \<delta>yx \<union> rSX rb "
      using I1 \<delta>xy_def \<delta>yx_def frame frame_weak_y_sx_delta by blast 
  
    from I1 have c4: "distinct \<delta>yx"
      using \<delta>yx_def frame frame_rb_weak_y_def by blast 
  
    from \<delta>yx_def frame have c5: "rSX rb \<inter> set \<delta>yx = {}" 
      unfolding frame_rb_weak_y_def
      by blast 
    
    show ?thesis using c1 c2 c3 c4 c5
      by blast
  qed
qed


(* ==================================================================================== *)
subsection \<open>State Transition Operations\<close>
(* ==================================================================================== *)

text \<open>
  We now formulate the state transition operations in terms of the CleanQ RB model
  state. Again, the two agents can, independently from each other, perform one of 
  two operations, \verb+enqueue+ and \verb+dequeue+,  which trigger an ownership 
  transfer of buffer elements.  
\<close>

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue Operation\<close>
(* ------------------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)
  
end 