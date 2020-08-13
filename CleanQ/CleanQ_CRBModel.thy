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
  imports CleanQ_RB 
          CleanQ_RBModel
(*>*)  
begin

(* ==================================================================================== *)
subsection \<open>CleanQ Abstract Concurrent Ring Buffer Model State\<close>
(* ==================================================================================== *)

text \<open>
  the model is exactly the same and we reuse the RB Model. 
\<close>

(*<*)
(* Define some global variables to make Simpl/Complex proofs work *)
record 'g CleanQ_CRB_State_vars = 
  RingCRB_'  :: "nat CleanQ_RB_State"
  b_' :: "nat"
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
  by (simp add: I4_rb_valid_def rb_delta_head_def rb_delta_tail_def rb_incr_head_n_delta_def 
      rb_incr_head_n_delta_map_def rb_incr_tail_n_delta_def rb_incr_tail_n_delta_map_def)

lemma frame_rb_s_w_y:
  "frame_rb_strong dev' dev \<Longrightarrow> frame_rb_weak_y dev' dev"
  unfolding frame_rb_weak_y_def frame_rb_strong_def frame_rb_weak_left_def
  frame_rb_weak_right_def rb_delta_tail_st_def rb_delta_head_st_def
  by (simp add: I4_rb_valid_def rb_delta_head_def rb_delta_tail_def rb_incr_head_n_delta_def 
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
  show " \<exists>\<delta>aB::'a list.
       map (the \<circ> ring (rTXY rb')) (rb_valid_entries (rTXY rb')) =
       \<delta>aB @ map (the \<circ> ring (rTXY rb)) (rb_valid_entries (rTXY rb)) \<and>
       (\<exists>\<delta>Bc::'a list.
           rSY rb' \<union> set \<delta>aB = set \<delta>Bc \<union> rSY rb \<and>
           map (the \<circ> ring (rTYX rb')) (rb_valid_entries (rTYX rb')) @ \<delta>Bc =
           map (the \<circ> ring (rTYX rb)) (rb_valid_entries (rTYX rb)) \<and>
           rSY rb \<inter> set \<delta>Bc = {} \<and> distinct \<delta>Bc)"
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

    from \<delta>yx_def frame have c6: "set (CleanQ_RB_list (rTXY rb)) \<inter> set \<delta>yx  = {}"
      unfolding CleanQ_RB_list_def
      by (smt CleanQ_RB_Invariants_def CleanQ_RB_list_def I1 I2_rb_img_def I3_rb_img_def Set.set_insert
          UnE Un_insert_right c1 c3 disjoint_iff_not_equal disjoint_insert(1) distinct_append set_append 
          subsetD sup_ge1)

    from \<delta>xy_def frame have c7: "set (CleanQ_RB_list (rTXY rb)) \<inter> set \<delta>xy = {}"
      unfolding CleanQ_RB_list_def
      by (metis CleanQ_RB_Invariants_def CleanQ_RB_list_def I1 I3_rb_img_def c1 distinct_append inf_commute) 

    show ?thesis using c1 c2 c3 c4 c5 c6 c7
      by (metis (no_types, lifting) CleanQ_RB_list_def comp_apply image_cong list.set_map) 
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
       map (the \<circ> ring (rTYX rb')) (rb_valid_entries (rTYX rb')) =
       \<delta>aB @ map (the \<circ> ring (rTYX rb)) (rb_valid_entries (rTYX rb)) \<and>
       (\<exists>\<delta>Bc::'a list.
           rSX rb' \<union> set \<delta>aB = set \<delta>Bc \<union> rSX rb \<and>
           map (the \<circ> ring (rTXY rb')) (rb_valid_entries (rTXY rb')) @ \<delta>Bc =
           map (the \<circ> ring (rTXY rb)) (rb_valid_entries (rTXY rb)) \<and>
           rSX rb \<inter> set \<delta>Bc = {} \<and> distinct \<delta>Bc)"
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
  
    from \<delta>yx_def frame have c6: "set (CleanQ_RB_list (rTYX rb)) \<inter> set \<delta>yx  = {}"
      unfolding CleanQ_RB_list_def
      by (smt CleanQ_RB_Invariants_def CleanQ_RB_list_def I1 I2_rb_img_def I3_rb_img_def Set.set_insert
          UnE Un_insert_right c1 c3 disjoint_iff_not_equal disjoint_insert(1) distinct_append set_append 
          subsetD sup_ge1)

    from \<delta>xy_def frame have c7: "set (CleanQ_RB_list (rTYX rb)) \<inter> set \<delta>xy = {}"
      unfolding CleanQ_RB_list_def
      by (metis CleanQ_RB_Invariants_def CleanQ_RB_list_def I1 I3_rb_img_def c1 distinct_append inf_commute) 

    show ?thesis using c1 c2 c3 c4 c5 c6 c7
      by (metis (no_types, lifting) CleanQ_RB_list_def comp_apply image_cong list.set_map)
  qed
qed


(* ==================================================================================== *)
subsection \<open>State Transition Operations\<close>
(* ==================================================================================== *)

text \<open>
  We now formulate the state transition operations in terms of the CleanQ RB model
  state. Again, the two agents can, independently from each other, perform one of 
  two operations, \verb+enqueue+ and \verb+dequeue+,  which trigger an ownership 
  transfer of buffer elements. In the previous model we implemented \verb+enqueue+ and
  \verb+dequeue+ as a single atomic step. Here we define it as two steps each.   

  We will first show that the enqueue and dequeue operations in two calls are
  the same as the atomic step and also preserve the invariant. This is basically
  showing equivalence in the non concurrent setting
\<close>

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue Operation\<close>
(* ------------------------------------------------------------------------------------ *)

definition CleanQ_RB_write_head_x :: "'a \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> 'a CleanQ_RB_State" 
  where "CleanQ_RB_write_head_x b rb = rb \<lparr>rTXY := rb_write_head b (rTXY rb) \<rparr>"

definition CleanQ_RB_incr_head_x :: "'a \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> 'a CleanQ_RB_State" 
  where "CleanQ_RB_incr_head_x b rb = rb \<lparr>rTXY := rb_incr_head (rTXY rb), rSX := (rSX rb) - {b} \<rparr>"

definition CleanQ_RB_write_head_y :: "'a \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> 'a CleanQ_RB_State" 
  where "CleanQ_RB_write_head_y b rb = rb \<lparr>rTYX := rb_write_head b (rTYX rb) \<rparr>"

definition CleanQ_RB_incr_head_y :: "'a \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> 'a CleanQ_RB_State" 
  where "CleanQ_RB_incr_head_y b rb = rb \<lparr>rTYX := rb_incr_head (rTYX rb), rSY := (rSY rb) - {b} \<rparr>"



definition CleanQ_RB_read_head_x :: "'a CleanQ_RB_State \<Rightarrow> 'a " 
  where "CleanQ_RB_read_head_x rb = rb_read_head (rTXY rb)"

definition CleanQ_RB_read_head_y :: "'a CleanQ_RB_State \<Rightarrow> 'a " 
  where "CleanQ_RB_read_head_y rb = rb_read_head (rTYX rb)"

lemma CleanQ_split_enq_x_equal[simp]:
  shows "CleanQ_RB_incr_head_x b (CleanQ_RB_write_head_x b rb) = CleanQ_RB_enq_x b rb"
  unfolding CleanQ_RB_incr_head_x_def CleanQ_RB_write_head_x_def CleanQ_RB_enq_x_def
  rb_enq_def by simp

lemma CleanQ_split_enq_y_equal[simp]:
  shows "CleanQ_RB_incr_head_y b (CleanQ_RB_write_head_y b rb) = CleanQ_RB_enq_y b rb"
  unfolding CleanQ_RB_incr_head_y_def CleanQ_RB_write_head_y_def CleanQ_RB_enq_y_def
  rb_enq_def by simp


text \<open>
  The two operations \verb+CleanQ_RB_enq_x+ and \verb+CleanQ_RB_enq_y+ as partial 
  operations also preserver the invariants. To show this we need some helper lemmas.
  First writeing at head does not invalidate the Invariants since it is the same
  state from the invariants persective as withouth the write. 
\<close>

lemma CleanQ_RB_enq_x_write_list:
  assumes Inv:" CleanQ_RB_Invariants K rb" and
          sx: "b \<in> rSX rb" and
          enq:"CleanQ_RB_enq_x_possible rb" 
  shows "CleanQ_RB_list (rTXY (CleanQ_RB_write_head_x b rb)) = CleanQ_RB_list (rTXY rb)"
  using assms
  by (metis CleanQ_RB_State.select_convs(3) CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(3) 
      CleanQ_RB_write_head_x_def rb_enq_write_same) 

lemma CleanQ_RB_enq_y_write_list:
  assumes Inv:" CleanQ_RB_Invariants K rb" and
          sy: "b \<in> rSY rb" and
          enq:"CleanQ_RB_enq_y_possible rb" 
  shows "CleanQ_RB_list (rTYX (CleanQ_RB_write_head_y b rb)) = CleanQ_RB_list (rTYX rb)"
  using assms
  by (metis CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(4) CleanQ_RB_write_head_y_def rb_enq_write_same)

lemma CleanQ_RB_enq_x_write_can_enq:
  assumes Inv:" CleanQ_RB_Invariants K rb" and
          sx: "b \<in> rSX rb" and
          enq:"CleanQ_RB_enq_x_possible rb" 
  shows "CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_x b rb)"
  using assms
  by (simp add: CleanQ_RB_write_head_x_def CleanQ_RB_enq_x_possible_def 
      rb_enq_write_can_enq) 

lemma CleanQ_RB_enq_y_write_can_enq:
  assumes Inv:" CleanQ_RB_Invariants K rb" and
          sx: "b \<in> rSY rb" and
          enq:"CleanQ_RB_enq_y_possible rb" 
  shows "CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_y b rb)"
  using assms
  by (simp add: CleanQ_RB_write_head_y_def CleanQ_RB_enq_y_possible_def 
      rb_enq_write_can_enq) 


lemma CleanQ_RB_write_head_y_can_enq_x:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> 
   CleanQ_RB_enq_x_possible rb = CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_y b rb)"
  by (simp add: CleanQ_RB_write_head_y_def CleanQ_RB_enq_x_possible_def) 

lemma CleanQ_RB_write_head_y_can_deq_x:
"CleanQ_RB_Invariants K rb \<Longrightarrow> 
  CleanQ_RB_deq_x_possible rb = CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_y b rb)"
  by(simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_write_head_y_def rb_write_can_deq)

lemma CleanQ_RB_write_head_y_can_deq_y:
  "CleanQ_RB_Invariants K rb \<Longrightarrow> 
  CleanQ_RB_deq_y_possible rb = CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_y b rb)"
  by (simp add: CleanQ_RB_deq_y_possible_def CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_y_can_enq_y:
"CleanQ_RB_Invariants K rb \<Longrightarrow> 
  CleanQ_RB_enq_y_possible rb = CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_y b rb)"
  by(simp add: CleanQ_RB_enq_y_possible_def CleanQ_RB_write_head_y_def rb_write_can_enq)
   

lemmas CleanQ_RB_write_head_y_can_enq_deq_simps  = CleanQ_RB_write_head_y_can_enq_x 
                                                  CleanQ_RB_write_head_y_can_deq_x 
                                                  CleanQ_RB_write_head_y_can_deq_y 
                                                  CleanQ_RB_write_head_y_can_enq_y

 


lemma CleanQ_RB_enq_x_incr_inv:
  assumes Inv:" CleanQ_RB_Invariants K rb" and
          sx: "b \<in> rSX rb \<and> the (((ring (rTXY rb) ) (head (rTXY rb)))) = b" and
          enq:"CleanQ_RB_enq_x_possible rb" 
  shows "I1_rb_img (CleanQ_RB_incr_head_x b rb) K"
  using assms unfolding CleanQ_RB_incr_head_x_def rb_incr_head_def I1_rb_img_def
  oops

lemma CleanQ_RB_enq_x_equal :
  shows "CleanQ_RB_enq_x b rb =  (CleanQ_RB_incr_head_x b (CleanQ_RB_write_head_x b rb))"
  unfolding CleanQ_RB_incr_head_x_def CleanQ_RB_write_head_x_def CleanQ_RB_enq_x_def
  by (metis CleanQ_RB_enq_x_def CleanQ_RB_incr_head_x_def CleanQ_RB_write_head_x_def
      CleanQ_split_enq_x_equal)

lemma CleanQ_RB_enq_y_equal :
  shows "CleanQ_RB_enq_y b rb =  (CleanQ_RB_incr_head_y b (CleanQ_RB_write_head_y b rb))"
  unfolding CleanQ_RB_incr_head_y_def CleanQ_RB_write_head_y_def CleanQ_RB_enq_y_def
  by (metis CleanQ_RB_enq_y_def CleanQ_RB_incr_head_y_def CleanQ_RB_write_head_y_def
      CleanQ_split_enq_y_equal)

lemma CleanQ_RB_enq_x_write_I1:
  assumes Inv:" CleanQ_RB_Invariants K rb" 
  shows "I1_rb_img (CleanQ_RB_write_head_x b rb) K"
  using assms
  by (metis CleanQ_RB_Invariants_def CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective 
            CleanQ_RB_State.update_convs(3) CleanQ_RB_write_head_x_def I1_rb_img_def 
            rb_enq_write_same)

lemma CleanQ_RB_enq_x_write_I2:
  assumes Inv:" CleanQ_RB_Invariants K rb" 
  shows "I2_rb_img (CleanQ_RB_write_head_x b rb)"
  using assms unfolding CleanQ_RB_Invariants_simp CleanQ_RB_write_head_x_def
  by (smt CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(3) rb_enq_write_same)

lemma CleanQ_RB_enq_x_write_I3:
  assumes Inv:" CleanQ_RB_Invariants K rb" 
  shows "I3_rb_img (CleanQ_RB_write_head_x b rb)"
  using assms unfolding I3_rb_img_def CleanQ_RB_write_head_x_def
  by (metis CleanQ_RB_Invariants_def CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective 
            CleanQ_RB_State.update_convs(3) I3_rb_img_def rb_enq_write_same) 

lemma CleanQ_RB_enq_x_write_I4:
  assumes Inv:" CleanQ_RB_Invariants K rb" 
  shows "I4_rb_valid(CleanQ_RB_write_head_x b rb)"
  using assms unfolding I4_rb_valid_def CleanQ_RB_write_head_x_def
  by (simp add: CleanQ_RB_Invariants_def I4_rb_valid_def rb_write_preserves_valid)


lemma CleanQ_RB_enq_y_write_I1:
  assumes Inv:" CleanQ_RB_Invariants K rb" 
  shows "I1_rb_img (CleanQ_RB_write_head_y b rb) K"
  using assms
  by (metis CleanQ_RB2List_def CleanQ_RB_Invariants_def CleanQ_RB_State.ext_inject 
            CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(4) CleanQ_RB_write_head_y_def 
            I1_rb_img_lift rb_enq_write_same)
 


lemma CleanQ_RB_enq_y_write_I2:
assumes Inv:" CleanQ_RB_Invariants K rb"  
  shows "I2_rb_img (CleanQ_RB_write_head_y b rb)"
  using assms unfolding I2_rb_img_def CleanQ_RB_write_head_y_def
  by (smt CleanQ_RB_Invariants_def CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective 
          CleanQ_RB_State.update_convs(1)  CleanQ_RB_State.update_convs(4) I2_rb_img_def 
          rb_enq_write_same)
  

lemma CleanQ_RB_enq_y_write_I3:
assumes Inv:" CleanQ_RB_Invariants K rb" 
  shows "I3_rb_img (CleanQ_RB_write_head_y b rb)"
  using assms unfolding I3_rb_img_def CleanQ_RB_write_head_y_def
  by (metis CleanQ_RB_Invariants_def CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective 
      CleanQ_RB_State.update_convs(4) I3_rb_img_def rb_enq_write_same)
  
lemma CleanQ_RB_enq_y_write_I4:
assumes Inv:" CleanQ_RB_Invariants K rb" 
  shows "I4_rb_valid(CleanQ_RB_write_head_y b rb)"
  using assms unfolding I4_rb_valid_def CleanQ_RB_write_head_y_def
  by (simp add: CleanQ_RB_Invariants_def I4_rb_valid_def rb_write_preserves_valid)
  

lemma CleanQ_RB_enq_x_write_inv_all:
assumes Inv:" CleanQ_RB_Invariants K rb"  
  shows "CleanQ_RB_Invariants K (CleanQ_RB_write_head_x b rb)"
  using assms unfolding CleanQ_RB_Invariants_def CleanQ_RB_write_head_x_def
  by (metis CleanQ_RB_write_head_x_def CleanQ_RB_enq_x_write_I1 CleanQ_RB_enq_x_write_I2 
      CleanQ_RB_enq_x_write_I3 CleanQ_RB_enq_x_write_I4 Inv)
  
lemma CleanQ_RB_enq_y_write_inv_all:
assumes Inv:" CleanQ_RB_Invariants K rb" 
  shows "CleanQ_RB_Invariants K (CleanQ_RB_write_head_y b rb)"
  using assms unfolding CleanQ_RB_Invariants_def CleanQ_RB_write_head_y_def
  by (metis CleanQ_RB_write_head_y_def CleanQ_RB_enq_y_write_I1 CleanQ_RB_enq_y_write_I2 
      CleanQ_RB_enq_y_write_I3 CleanQ_RB_enq_y_write_I4 Inv)

lemma CleanQ_RB_write_head_inv_all:
  "CleanQ_RB_Invariants K rb \<longleftrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_y b rb)"
  apply(auto simp:CleanQ_RB_enq_y_write_inv_all)
  unfolding CleanQ_RB_Invariants_def CleanQ_RB_write_head_y_def
  apply(auto)
     apply(simp add: I1_rb_img_def) apply (metis rb_enq_write_same)
    apply(simp add: I2_rb_img_def) apply (metis rb_enq_write_same)
   apply(simp add: I3_rb_img_def) apply (metis rb_enq_write_same)
  apply(simp add:I4_rb_valid_def) by (meson rb_write_head_valid)
  

lemma CleanQ_RB_enq_x_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RingCRB \<and> CleanQ_RB_Invariants K \<acute> RingCRB \<and> b \<in> rSX \<acute> RingCRB \<and>
         CleanQ_RB_enq_x_possible \<acute>RingCRB \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_write_head_x b \<acute>RingCRB) ;;
        \<acute>RingCRB :== (CleanQ_RB_incr_head_x b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_Invariants K \<acute>RingCRB \<rbrace>"
  apply(vcg)
  using CleanQ_split_enq_x_equal
  by (metis CleanQ_RB_enq_x_inv_all) 
  
lemma CleanQ_RB_enq_y_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RingCRB \<and> CleanQ_RB_Invariants K \<acute> RingCRB \<and> b \<in> rSY \<acute> RingCRB \<and>
         CleanQ_RB_enq_y_possible \<acute>RingCRB \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_write_head_y b \<acute>RingCRB) ;;
        \<acute>RingCRB :== (CleanQ_RB_incr_head_y b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_Invariants K \<acute>RingCRB \<rbrace>"
  apply(vcg)
  using CleanQ_split_enq_y_equal
  by (metis CleanQ_RB_enq_y_inv_all)   
  
(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)

definition CleanQ_RB_read_tail_x :: "'a CleanQ_RB_State \<Rightarrow> 'a " 
  where "CleanQ_RB_read_tail_x rb = rb_read_tail (rTYX rb)"

definition CleanQ_RB_read_tail_y :: "'a CleanQ_RB_State \<Rightarrow> 'a " 
  where "CleanQ_RB_read_tail_y rb = rb_read_tail (rTXY rb)"

definition CleanQ_RB_incr_tail_x :: "'a \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> 'a CleanQ_RB_State" 
  where "CleanQ_RB_incr_tail_x b rb = rb \<lparr>rTYX := rb_incr_tail (rTYX rb), rSX := (rSX rb) \<union> {b} \<rparr>"

definition CleanQ_RB_incr_tail_y :: "'a \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> 'a CleanQ_RB_State" 
  where "CleanQ_RB_incr_tail_y b rb = rb \<lparr>rTXY := rb_incr_tail (rTXY rb), rSY := (rSY rb) \<union> {b} \<rparr>"

lemma CleanQ_split_deq_x_equal:
  shows "(let b = CleanQ_RB_read_tail_x rb in CleanQ_RB_incr_tail_x b rb) = CleanQ_RB_deq_x rb"
  unfolding CleanQ_RB_deq_x_def rb_deq_def CleanQ_RB_read_tail_x_def CleanQ_RB_incr_tail_x_def
  by simp

lemma CleanQ_split_deq_x_equal2[simp]:
  shows "CleanQ_RB_incr_tail_x (CleanQ_RB_read_tail_x rb) rb = CleanQ_RB_deq_x rb"
  unfolding CleanQ_RB_deq_x_def rb_deq_def CleanQ_RB_read_tail_x_def CleanQ_RB_incr_tail_x_def
  by simp

lemma CleanQ_split_deq_y_equal:
  shows "(let b = CleanQ_RB_read_tail_y rb in CleanQ_RB_incr_tail_y b rb) = CleanQ_RB_deq_y rb"
  unfolding CleanQ_RB_deq_y_def rb_deq_def CleanQ_RB_read_tail_y_def CleanQ_RB_incr_tail_y_def
  by simp

lemma CleanQ_split_deq_y_equal2[simp]:
  shows "CleanQ_RB_incr_tail_y (CleanQ_RB_read_tail_y rb) rb = CleanQ_RB_deq_y rb"
  unfolding CleanQ_RB_deq_y_def rb_deq_def CleanQ_RB_read_tail_y_def CleanQ_RB_incr_tail_y_def
  by simp



lemma CleanQ_RB_deq_x_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace>  CleanQ_RB_Invariants K \<acute> RingCRB \<and> CleanQ_RB_deq_x_possible \<acute>RingCRB \<rbrace> 
        \<acute>b :== (CleanQ_RB_read_tail_x \<acute>RingCRB) ;;
        \<acute>RingCRB :== (CleanQ_RB_incr_tail_x \<acute>b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_Invariants K \<acute>RingCRB \<rbrace>"
  apply(vcg)
  using CleanQ_split_deq_x_equal
  by (metis CleanQ_RB_deq_x_all_inv) 


lemma CleanQ_RB_deq_y_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace>  CleanQ_RB_Invariants K \<acute> RingCRB \<and> CleanQ_RB_deq_y_possible \<acute>RingCRB \<rbrace> 
        \<acute>b :== (CleanQ_RB_read_tail_y \<acute>RingCRB) ;;
        \<acute>RingCRB :== (CleanQ_RB_incr_tail_y \<acute>b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_Invariants K \<acute>RingCRB \<rbrace>"
  apply(vcg)
  using CleanQ_split_deq_y_equal
  by (metis CleanQ_RB_deq_y_all_inv) 

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Invariants are TRUE invariants\<close>
(* ------------------------------------------------------------------------------------ *)
text \<open>
  To show that the Invariants we defined are true invariants it has to hold at each
  step of the computation and not only at beginning and end. To show this
  we will show the invariant for each of the two steps of \verb+enqueue+ and \verb+dequeue+. 
\<close>

lemma CleanQ_CRB_write_enq_x_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RingCRB \<and> CleanQ_RB_Invariants K \<acute> RingCRB \<and> b \<in> rSX \<acute> RingCRB \<and>
         CleanQ_RB_enq_x_possible \<acute>RingCRB \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_write_head_x b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_Invariants K \<acute> RingCRB \<and> b \<in> rSX \<acute> RingCRB \<and> 
        CleanQ_RB_enq_x_possible \<acute>RingCRB \<and> b = the (((ring (rTXY \<acute>RingCRB) ) (head (rTXY \<acute>RingCRB))))\<rbrace>"
  apply(vcg)
  unfolding CleanQ_RB_enq_x_possible_def rb_can_enq_def 
    CleanQ_RB_write_head_x_def rb_write_head_def
proof -
  fix RingCRB :: "nat CleanQ_RB_State"
  assume a1: "\<not> rb_full (rTXY RingCRB)"
  assume a2: "b \<in> rSX RingCRB"
  assume a3: "CleanQ_RB_Invariants K RingCRB"
  have "rb_can_enq (rTXY RingCRB)"
    using a1 rb_can_enq_def by blast
  then have "CleanQ_RB_enq_x_possible RingCRB"
    by (simp add: CleanQ_RB_enq_x_possible_def)
  then show "CleanQ_RB_Invariants K (RingCRB \<lparr>rTXY := rTXY RingCRB \<lparr>ring := ring (rTXY RingCRB)(head (rTXY RingCRB) \<mapsto> b)\<rparr>\<rparr>) \<and> b \<in> rSX (RingCRB \<lparr>rTXY := rTXY RingCRB \<lparr>ring := ring (rTXY RingCRB) (head (rTXY RingCRB) \<mapsto> b)\<rparr>\<rparr>) \<and> \<not> rb_full (rTXY (RingCRB \<lparr>rTXY := rTXY RingCRB \<lparr>ring := ring (rTXY RingCRB) (head (rTXY RingCRB) \<mapsto> b)\<rparr>\<rparr>)) \<and> b = the (ring (rTXY (RingCRB \<lparr>rTXY := rTXY RingCRB \<lparr>ring := ring (rTXY RingCRB)(head (rTXY RingCRB) \<mapsto> b)\<rparr>\<rparr>)) (head (rTXY (RingCRB \<lparr>rTXY := rTXY RingCRB \<lparr>ring := ring (rTXY RingCRB) (head (rTXY RingCRB) \<mapsto> b)\<rparr>\<rparr>))))"
    using a3 a2 by (metis (no_types) CleanQ_RB_State.select_convs(1) CleanQ_RB_State.select_convs(3) CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(1) CleanQ_RB_State.update_convs(3) CleanQ_RB_write_head_x_def CleanQ_RB_enq_x_possible_def CleanQ_RB_enq_x_write_can_enq CleanQ_RB_enq_x_write_inv_all option.sel rb_can_enq_def rb_write_head_def rb_write_head_element)
qed 

lemma CleanQ_CRB_write_enq_y_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RingCRB \<and> CleanQ_RB_Invariants K \<acute> RingCRB \<and> b \<in> rSY \<acute> RingCRB \<and>
         CleanQ_RB_enq_y_possible \<acute>RingCRB \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_write_head_y b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_Invariants K \<acute> RingCRB \<and> b \<in> rSY \<acute> RingCRB \<and> 
        CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> b = the (((ring (rTYX \<acute>RingCRB) ) (head (rTYX \<acute>RingCRB))))\<rbrace>"
  apply(vcg)
  unfolding CleanQ_RB_enq_y_possible_def rb_can_enq_def 
    CleanQ_RB_write_head_y_def rb_write_head_def
  apply auto
  apply (smt CleanQ_RB.ext_inject CleanQ_RB.surjective CleanQ_RB.update_convs(1) 
         CleanQ_RB_Invariants_def CleanQ_RB_State.select_convs(1) CleanQ_RB_State.select_convs(2) 
         CleanQ_RB_State.select_convs(3) CleanQ_RB_State.select_convs(4) CleanQ_RB_State.surjective 
         CleanQ_RB_State.update_convs(4) CleanQ_RB_list_def I1_rb_img_def I2_rb_img_def I3_rb_img_def 
         I4_rb_valid_def fun_upd_other map_fun_upd map_map rb_valid_def rb_valid_entries_def 
         rb_valid_ptr_def rb_write_head_element_notin_valid)
  by (simp add: rb_full_def)

(*
lemma CleanQ_CRB_incr_enq_x_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_Invariants K rb \<and> b \<in> rSX rb \<and> 
        CleanQ_RB_enq_x_possible rb \<and>\<acute>RingCRB = (CleanQ_RB_write_head_y b rb)\<rbrace>
        \<acute>RingCRB :== (CleanQ_RB_incr_head_x b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_Invariants K \<acute> RingCRB\<rbrace>"
  apply(vcg) 
  using CleanQ_RB_enq_x_equal CleanQ_RB_enq_x_inv_all
  apply auto
  *)
 
  


lemma CleanQ_CRB_read_deq_x_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace>  CleanQ_RB_Invariants K \<acute> RingCRB \<and> CleanQ_RB_deq_x_possible \<acute>RingCRB \<rbrace> 
        \<acute>b :== (CleanQ_RB_read_tail_x \<acute>RingCRB)
      \<lbrace> \<acute>b = (CleanQ_RB_read_tail_x \<acute>RingCRB) \<and> CleanQ_RB_Invariants K \<acute>RingCRB \<and> 
         CleanQ_RB_deq_x_possible \<acute>RingCRB \<rbrace>"
  by vcg


lemma CleanQ_CRB_read_deq_y_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace>  CleanQ_RB_Invariants K \<acute> RingCRB \<and> CleanQ_RB_deq_y_possible \<acute>RingCRB \<rbrace> 
        \<acute>b :== (CleanQ_RB_read_tail_y \<acute>RingCRB)
      \<lbrace> \<acute>b = (CleanQ_RB_read_tail_y \<acute>RingCRB) \<and> CleanQ_RB_Invariants K \<acute>RingCRB \<and> 
        CleanQ_RB_deq_y_possible \<acute>RingCRB \<rbrace>"
  by vcg

lemma CleanQ_CRB_incr_deq_x_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> \<acute>b = (CleanQ_RB_read_tail_x \<acute>RingCRB) \<and> CleanQ_RB_Invariants K \<acute> RingCRB \<and> 
         CleanQ_RB_deq_x_possible \<acute>RingCRB \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_incr_tail_x \<acute>b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_Invariants K \<acute>RingCRB \<rbrace>"
  apply vcg
  by (metis CleanQ_RB_deq_x_all_inv CleanQ_split_deq_x_equal)

lemma CleanQ_RB_incr_deq_y_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> \<acute>b = (CleanQ_RB_read_tail_y \<acute>RingCRB) \<and> CleanQ_RB_Invariants K \<acute> RingCRB \<and> 
         CleanQ_RB_deq_y_possible \<acute>RingCRB \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_incr_tail_y \<acute>b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_Invariants K \<acute>RingCRB \<rbrace>"
    apply vcg
  by (metis CleanQ_RB_deq_y_all_inv CleanQ_split_deq_y_equal)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Weak frame condition preserver invariants\<close>
(* ------------------------------------------------------------------------------------ *)

lemma frame_rb_weak_x_notin_xy_yx_sy:
  fixes rb rb' K
  assumes frame: "frame_rb_weak_x rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows "x \<in> K \<Longrightarrow> x \<notin> set (CleanQ_RB_list (rTYX rb)) \<Longrightarrow> x \<notin> set (CleanQ_RB_list (rTXY rb)) \<Longrightarrow> x \<notin> rSY rb \<Longrightarrow> x \<in> rSX rb'"
  using assms unfolding frame_rb_weak_x_def CleanQ_RB_Invariants_def
  by (smt CleanQ_RB_list_def I1_rb_img_def UnCI UnI2 Un_commute Un_iff inf_commute rb_delta_head_incr 
      rb_delta_tail_incr set_append) 

lemma frame_rb_weak_y_notin_xy_yx_sx:
  fixes rb rb' K
  assumes frame: "frame_rb_weak_y rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows "x \<in> K \<Longrightarrow> x \<notin> set (CleanQ_RB_list (rTXY rb)) \<Longrightarrow> x \<notin> set (CleanQ_RB_list (rTYX rb)) \<Longrightarrow> x \<notin> rSX rb \<Longrightarrow> x \<in> rSY rb'"
  using assms unfolding frame_rb_weak_y_def CleanQ_RB_Invariants_def frame_rb_weak_left_def
  frame_rb_weak_right_def apply auto
  by (smt CleanQ_RB_list_def I1_rb_img_def UnE Un_commute Un_upper2 frame frame_rb_weak_right_def 
      frame_weak_y_tl_delta invariants rb_delta_head_incr set_append subsetD)

lemma CleanQ_CRB_frame_x_I1 :
  fixes rb rb' K
  assumes frame: "frame_rb_weak_x rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows "I1_rb_img rb K"
  using assms unfolding frame_rb_weak_x_def I1_rb_img_def CleanQ_RB_Invariants_def
  frame_rb_weak_left_def frame_rb_weak_right_def
  apply auto
  apply (smt CleanQ_RB_list_def UnE UnI1 Un_upper2 frame frame_weak_x_tl_delta invariants set_append subsetD)
  apply (metis CleanQ_RB_list_def UnCI frame frame_weak_x_tl_delta invariants set_append)
  apply (smt CleanQ_RB_list_def UnE frame frame_rb_weak_x_def frame_weak_x_tl_delta invariants 
         rb_delta_head_incr set_append subsetD sup_ge1)
  using frame frame_rb_weak_x_notin_xy_yx_sy invariants apply fastforce
  apply (metis (no_types) Un_iff frame frame_rb_weak_x_notin_xy_yx_sy invariants)
  by (metis CleanQ_RB_list_def UnCI frame frame_rb_weak_x_def rb_delta_head_incr set_append)
  

lemma CleanQ_CRB_frame_y_I1 :
  fixes rb rb' K
  assumes frame: "frame_rb_weak_y rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows "I1_rb_img rb K"
  using assms unfolding frame_rb_weak_y_def I1_rb_img_def CleanQ_RB_Invariants_def
  frame_rb_weak_left_def frame_rb_weak_right_def
  apply auto
  apply (smt CleanQ_RB_list_def UnE UnI1 Un_upper2 frame frame_weak_y_tl_delta invariants set_append subsetD)
  apply (smt CleanQ_RB_list_def UnE frame frame_rb_weak_right_def frame_weak_y_tl_delta invariants rb_delta_head_incr 
         set_append subsetD sup_ge1)
  apply (metis CleanQ_RB_list_def UnCI frame frame_weak_y_tl_delta invariants set_append)
  apply (metis (no_types) UnCI frame frame_rb_weak_y_notin_xy_yx_sx invariants)
  apply (metis CleanQ_RB_list_def UnCI frame frame_weak_y_hd_delta invariants set_append)
  by (metis frame frame_rb_weak_y_notin_xy_yx_sx invariants subsetD sup_ge2)


lemma frame_rb_weak_x_in_deltaxy_notin_txy:
  fixes rb rb' K
  assumes frame: "frame_rb_weak_x rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows "x \<in> set (rb_delta_tail_st (rTXY rb') (rTXY rb)) \<Longrightarrow> x \<notin> set (CleanQ_RB_list (rTXY rb))"
  using assms unfolding CleanQ_RB_Invariants_def frame_rb_weak_x_def
  by (metis CleanQ_RB_list_def I3_rb_img_def Int_iff distinct_append insert_absorb insert_not_empty 
      rb_delta_tail_incr) 


lemma frame_rb_weak_y_in_deltaxy_notin_txy:
  fixes rb rb' K
  assumes frame: "frame_rb_weak_y rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows "x \<in> set (rb_delta_tail_st (rTYX rb') (rTYX rb)) \<Longrightarrow> x \<notin> set (CleanQ_RB_list (rTYX rb))"
  using assms unfolding CleanQ_RB_Invariants_def frame_rb_weak_y_def
  by (metis CleanQ_RB_list_def I3_rb_img_def disjoint_iff_not_equal distinct_append rb_delta_tail_incr) 

lemma frame_rb_weak_x_in_sy_notin_txy:
  fixes rb rb' K
  assumes frame: "frame_rb_weak_x rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows" x \<in> rSY rb \<Longrightarrow> x \<in> set (CleanQ_RB_list (rTXY rb)) \<Longrightarrow> False"
  using assms unfolding CleanQ_RB_Invariants_def frame_rb_weak_x_def
  by (smt CleanQ_RB_list_def I2_rb_img_def I3_rb_img_def UnE Un_upper2 disjoint_iff_not_equal distinct_append 
      rb_delta_tail_incr set_append subsetD) 

lemma frame_rb_weak_y_in_sx_notin_tyx:
  fixes rb rb' K
  assumes frame: "frame_rb_weak_y rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows" x \<in> rSX rb \<Longrightarrow> x \<in> set (CleanQ_RB_list (rTYX rb)) \<Longrightarrow> False"
  using assms unfolding frame_rb_weak_y_def CleanQ_RB_Invariants_def
  by (smt CleanQ_RB_list_def I2_rb_img_def I3_rb_img_def UnE Un_upper2 disjoint_iff_not_equal 
      distinct_append rb_delta_tail_incr set_append subsetD)

lemma frame_rb_weak_y_in_sx_notin_txy:
  fixes rb rb' K
  assumes frame: "frame_rb_weak_y rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows" x \<in> rSX rb \<Longrightarrow> x \<in> set (CleanQ_RB_list (rTXY rb)) \<Longrightarrow> False"
  using assms unfolding frame_rb_weak_y_def CleanQ_RB_Invariants_def
  by (smt CleanQ_RB_list_def I2_rb_img_def UnE Un_commute Un_upper2 disjoint_iff_not_equal frame 
      frame_weak_y_hd_delta frame_weak_y_tl_delta invariants set_append subsetD) 

lemma frame_rb_weak_x_in_txy_notin_tyx:
  fixes rb rb' K
  assumes frame: "frame_rb_weak_x rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"  
  shows "x \<in> set (CleanQ_RB_list (rTXY rb)) \<Longrightarrow> x \<in> set (CleanQ_RB_list (rTYX rb)) \<Longrightarrow> False"
  using assms unfolding frame_rb_weak_x_def CleanQ_RB_Invariants_def
  by (smt CleanQ_RB_list_def I2_rb_img_def I3_rb_img_def Set.set_insert UnE disjoint_insert(1) 
      distinct_append rb_delta_head_incr rb_delta_tail_incr set_append subsetD sup.cobounded2 sup.commute)

lemma frame_rb_weak_x_sx_notin_yx:
  fixes rb rb' K
  assumes frame: "frame_rb_weak_x rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'" 
  shows "x \<in> rSX rb' \<Longrightarrow> x \<in> set (CleanQ_RB_list (rTYX rb)) \<Longrightarrow> False"
  using assms unfolding frame_rb_weak_x_def CleanQ_RB_Invariants_def
  by (smt CleanQ_RB_list_def I2_rb_img_def Int_iff Set.set_insert Un_iff disjoint_insert(1) 
      inf_sup_absorb rb_delta_head_incr rb_delta_tail_incr set_append)

lemma frame_rb_weak_y_sy_notin_xy:
  fixes rb rb' K
  assumes frame: "frame_rb_weak_y rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'" 
  shows "x \<in> rSY rb' \<Longrightarrow> x \<in> set (CleanQ_RB_list (rTXY rb)) \<Longrightarrow> False"
  using assms unfolding frame_rb_weak_y_def CleanQ_RB_Invariants_def
  by (smt CleanQ_RB_list_def I2_rb_img_def UnE disjoint_insert(1) insert_Diff rb_delta_head_incr 
      rb_delta_tail_incr set_append subsetD sup_ge1)


lemma CleanQ_CRB_frame_x_I2 :
  fixes rb rb' K
  assumes frame: "frame_rb_weak_x rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows "I2_rb_img rb"
  using assms unfolding frame_rb_weak_x_def CleanQ_RB_Invariants_def I2_rb_img_def
  apply auto
  apply (smt CleanQ_RB_list_def UnE UnI1 Un_upper2 disjoint_iff_not_equal frame frame_weak_x_tl_delta 
         invariants set_append subsetD)
  apply (metis CleanQ_RB_list_def UnCI disjoint_iff_not_equal rb_delta_tail_incr set_append)
  apply (meson frame frame_rb_weak_x_sx_notin_yx invariants)
  apply (meson frame frame_rb_weak_x_in_sy_notin_txy invariants)
  apply (smt CleanQ_RB_list_def Int_iff Set.set_insert Un_iff disjoint_insert(1) inf_sup_absorb 
      rb_delta_head_incr rb_delta_tail_incr set_append sup.commute) 
  by (meson frame frame_rb_weak_x_in_txy_notin_tyx invariants) 

 
lemma CleanQ_CRB_frame_y_I2 :
  fixes rb rb' K
  assumes frame: "frame_rb_weak_y rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows "I2_rb_img rb"
  using assms unfolding frame_rb_weak_y_def CleanQ_RB_Invariants_def I2_rb_img_def
  apply auto
  apply (smt CleanQ_RB_list_def UnE Un_commute Un_upper2 disjoint_iff_not_equal frame frame_weak_y_tl_delta 
      invariants set_append subsetD)
  apply (meson frame frame_rb_weak_y_in_sx_notin_txy invariants)
  apply (meson frame frame_rb_weak_y_in_sx_notin_tyx invariants)
  apply (meson frame frame_rb_weak_y_sy_notin_xy invariants)
  apply (metis CleanQ_RB_list_def UnCI disjoint_iff_not_equal rb_delta_tail_incr set_append)
  by (smt CleanQ_RB_list_def I3_rb_img_def UnE disjoint_insert(1) distinct_append insert_Diff 
      rb_delta_head_incr rb_delta_tail_incr set_append subsetD sup.commute sup_ge1)

lemma CleanQ_CRB_frame_x_I3 :
  fixes rb rb' K
  assumes frame: "frame_rb_weak_x rb' rb"
      and invariants : "CleanQ_RB_Invariants K rb'"
  shows "I3_rb_img rb"
  using assms unfolding frame_rb_weak_x_def CleanQ_RB_Invariants_def I3_rb_img_def
  by (smt CleanQ_RB_list_def I2_rb_img_def distinct_append inf_commute inf_left_commute inf_sup_absorb 
      inf_sup_distrib1 rb_delta_head_incr rb_delta_tail_incr set_append)

lemma CleanQ_CRB_frame_y_I3 :
  fixes rb rb' K
  assumes frame: "frame_rb_weak_y rb' rb"
      and invariants : "CleanQ_RB_Invariants K rb'"
  shows "I3_rb_img rb"
  using assms unfolding frame_rb_weak_y_def CleanQ_RB_Invariants_def I3_rb_img_def
  by (smt CleanQ_RB_list_def I2_rb_img_def distinct_append inf_commute inf_left_commute inf_sup_absorb 
      inf_sup_distrib1 rb_delta_head_incr rb_delta_tail_incr set_append)

lemma CleanQ_CRB_frame_x_I4 :
  fixes rb rb' K
  assumes frame: "frame_rb_weak_x rb' rb"
      and invariants : "CleanQ_RB_Invariants K rb'"
  shows "I4_rb_valid rb"
  using assms unfolding frame_rb_weak_x_def CleanQ_RB_Invariants_def I4_rb_valid_def
  by (simp add: frame_rb_weak_left_def frame_rb_weak_right_def)

  
lemma CleanQ_CRB_frame_y_I4 :
  fixes rb rb' K
  assumes frame: "frame_rb_weak_y rb' rb"
      and invariants : "CleanQ_RB_Invariants K rb'"
  shows "I4_rb_valid rb"
  using assms unfolding frame_rb_weak_y_def CleanQ_RB_Invariants_def I4_rb_valid_def
  by (simp add: frame_rb_weak_left_def frame_rb_weak_right_def)
  
lemma CleanQ_CRB_frame_x_I_all :
  fixes rb rb' K
  assumes frame: "frame_rb_weak_x rb' rb"
      and invariants : "CleanQ_RB_Invariants K rb'"
  shows "CleanQ_RB_Invariants K rb"
  using assms unfolding frame_rb_weak_x_def CleanQ_RB_Invariants_def
  by (meson CleanQ_CRB_frame_x_I1 CleanQ_CRB_frame_x_I2 CleanQ_CRB_frame_x_I3 CleanQ_CRB_frame_x_I4 
      frame invariants)

lemma CleanQ_CRB_frame_y_I_all :
  fixes rb rb' K
  assumes frame: "frame_rb_weak_y rb' rb"
      and invariants : "CleanQ_RB_Invariants K rb'"
  shows "CleanQ_RB_Invariants K rb"
  using assms unfolding frame_rb_weak_y_def CleanQ_RB_Invariants_def
  by (meson CleanQ_CRB_frame_y_I1 CleanQ_CRB_frame_y_I2 CleanQ_CRB_frame_y_I3 CleanQ_CRB_frame_y_I4 
      frame invariants)

(* ==================================================================================== *)
subsection \<open>Interference pairs\<close>
(* ==================================================================================== *)
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We are now showing the interference proofs for the different step. There are two threads
  in the system, each of which can execute the enqueue and dequeue operations independently.
  
  The system looks like this:

    \verb+ (enq_x | deq_x)  ||  (enq_y | deq_y)+

  While each of the four operations consists of two steps. reading/writing the buffer slot
  and updating the head/tail pointer respectively.

  We fix one side (X) and show that the other side cannot interfere with each of the
  possible interference pairs. The correctness of the other side follows by symmetry.
\<close>

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue X, Enqueue Y\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open> 
  The Enqueue operation has the form: \verb+{P} write_head {Q} increment_head {R}+.
  We show, that the predicates of the Hoare triples remain valid, regardless of the 
  operation of the other side.
\<close>


abbreviation "CleanQ_Enq_X_P K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> CleanQ_RB_enq_x_possible rb \<and> b \<in> rSX rb"
abbreviation "CleanQ_Enq_X_Q K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> CleanQ_RB_enq_x_possible rb \<and> b \<in> rSX rb \<and>  b = CleanQ_RB_read_head_x rb"
abbreviation "CleanQ_Enq_X_R K rb b \<equiv> CleanQ_RB_Invariants K rb"

abbreviation "CleanQ_Deq_X_P K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> CleanQ_RB_deq_x_possible rb"
abbreviation "CleanQ_Deq_X_Q K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> CleanQ_RB_deq_x_possible rb \<and> b = CleanQ_RB_read_tail_x rb"
abbreviation "CleanQ_Deq_X_R K rb b \<equiv> CleanQ_RB_Invariants K rb"

paragraph \<open>Y writes the descriptor ring\<close>

lemma CleanQ_CRB_Enqueue_X_P_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_Enq_X_P K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_Enq_X_P K \<acute>RingCRB bx  \<rbrace>"
  apply(vcg, simp add:CleanQ_RB_enq_y_write_inv_all CleanQ_RB_write_head_y_can_enq_x[symmetric])  
  by (simp add: CleanQ_RB_write_head_y_def)

lemma CleanQ_CRB_Enqueue_X_Q_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_Enq_X_Q K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_Enq_X_Q K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, simp add:CleanQ_RB_enq_y_write_inv_all CleanQ_RB_write_head_y_can_enq_x[symmetric])
  by(simp add: CleanQ_RB_write_head_y_def CleanQ_RB_read_head_x_def )

lemma CleanQ_CRB_Enqueue_X_R_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_Enq_X_R K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_Enq_X_R K \<acute>RingCRB bx \<rbrace>"
   by(vcg, simp add:CleanQ_RB_enq_y_write_inv_all)  

paragraph \<open>Y increments the head\<close>

lemma CleanQ_CRB_Enqueue_X_P_incr_head:
"\<Gamma>\<turnstile> \<lbrace>  rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_Enq_X_P K rb bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_Enq_X_P K \<acute>RingCRB bx  \<rbrace>"
  apply(vcg, auto)
  apply (meson CleanQ_RB_enq_y_inv_all CleanQ_RB_write_head_inv_all)
  apply (meson CleanQ_RB_enq_y_enq_x_possible CleanQ_RB_write_head_inv_all CleanQ_RB_write_head_y_can_enq_x)
  by (simp add: CleanQ_RB_enq_y_def CleanQ_RB_write_head_y_def)


lemma CleanQ_CRB_Enqueue_X_Q_incr_head:
"\<Gamma>\<turnstile> \<lbrace>  rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_Enq_X_Q K rb bx   \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_Enq_X_Q K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto)
  apply (meson CleanQ_RB_enq_y_inv_all CleanQ_RB_write_head_inv_all)
  apply (meson CleanQ_RB_enq_y_enq_x_possible CleanQ_RB_write_head_inv_all CleanQ_RB_write_head_y_can_enq_x)
  apply (simp add: CleanQ_RB_enq_y_def CleanQ_RB_write_head_y_def)
  by (simp add: CleanQ_RB_enq_y_def CleanQ_RB_read_head_x_def CleanQ_RB_write_head_y_def)
  
lemma CleanQ_CRB_Enqueue_X_R_incr_head:
"\<Gamma>\<turnstile> \<lbrace> rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_Enq_X_R K rb bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_Enq_X_R K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto)
  by (meson CleanQ_RB_enq_y_inv_all CleanQ_RB_write_head_inv_all)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue X, Dequeue X\<close>
(* ------------------------------------------------------------------------------------ *)

paragraph \<open>Y reads the descriptor ring\<close>

lemma CleanQ_CRB_Enqueue_X_P_read_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_Enq_X_P K \<acute>RingCRB bx  \<rbrace> 
     \<acute>b :== CleanQ_RB_read_tail_y \<acute>RingCRB 
  \<lbrace>  CleanQ_Enq_X_P K \<acute>RingCRB bx  \<rbrace>"
  by(vcg)

lemma CleanQ_CRB_Enqueue_X_Q_read_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_Enq_X_Q K \<acute>RingCRB bx  \<rbrace> 
     \<acute>b :== CleanQ_RB_read_tail_y \<acute>RingCRB
  \<lbrace>  CleanQ_Enq_X_Q K \<acute>RingCRB bx \<rbrace>"
  by(vcg)

lemma CleanQ_CRB_Enqueue_X_R_read_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_Enq_X_R K \<acute>RingCRB bx  \<rbrace> 
     \<acute>b :== CleanQ_RB_read_tail_y \<acute>RingCRB
  \<lbrace>  CleanQ_Enq_X_R K \<acute>RingCRB bx \<rbrace>"
   by(vcg)

paragraph \<open>Y increments the tail pointer\<close>

lemma CleanQ_CRB_Enqueue_X_P_incr_tail:
"\<Gamma>\<turnstile> \<lbrace>  b = CleanQ_RB_read_tail_y  \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_deq_y_possible \<acute>RingCRB \<and> CleanQ_Enq_X_P K \<acute>RingCRB bx  \<rbrace> 
      \<acute>RingCRB  :== CleanQ_RB_incr_tail_y b  \<acute>RingCRB 
  \<lbrace>  CleanQ_Enq_X_P K \<acute>RingCRB bx  \<rbrace>"
  apply(vcg, auto simp:CleanQ_RB_deq_y_all_inv CleanQ_RB_deq_y_enq_x_possible )  
  using CleanQ_RB_deq_y_no_change by blast

lemma CleanQ_CRB_Enqueue_X_Q_incr_tail:
"\<Gamma>\<turnstile> \<lbrace>  b = CleanQ_RB_read_tail_y  \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_deq_y_possible \<acute>RingCRB \<and> CleanQ_Enq_X_Q K \<acute>RingCRB bx  \<rbrace> 
     \<acute>RingCRB  :== CleanQ_RB_incr_tail_y b  \<acute>RingCRB 
  \<lbrace>  CleanQ_Enq_X_Q K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto simp:CleanQ_RB_deq_y_all_inv CleanQ_RB_deq_y_enq_x_possible ) 
  using CleanQ_RB_deq_y_no_change apply blast
  by (metis CleanQ_RB_Invariants_def CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def
            I2_rb_img_def I4_rb_valid_def disjoint_iff_not_equal hd_in_set prod.sel(1) 
            rb_deq_def rb_deq_list_was_head rb_deq_not_empty rb_valid_def) 

lemma CleanQ_CRB_Enqueue_X_R_incr_tail:
"\<Gamma>\<turnstile> \<lbrace>  b = CleanQ_RB_read_tail_y  \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_deq_y_possible \<acute>RingCRB \<and> CleanQ_Enq_X_R K \<acute>RingCRB bx  \<rbrace> 
     \<acute>RingCRB  :== CleanQ_RB_incr_tail_y b  \<acute>RingCRB 
  \<lbrace>  CleanQ_Enq_X_R K \<acute>RingCRB bx \<rbrace>"
  by(vcg, auto simp:CleanQ_RB_deq_y_all_inv CleanQ_RB_deq_y_enq_x_possible )





(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue X, Enqueue Y\<close>
(* ------------------------------------------------------------------------------------ *)

paragraph \<open>Y writes the descriptor ring\<close>

lemma CleanQ_CRB_Dequeue_X_P_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_Deq_X_P K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_Deq_X_P K \<acute>RingCRB bx  \<rbrace>"
  apply(vcg, simp add:CleanQ_RB_enq_y_write_inv_all CleanQ_RB_write_head_y_can_enq_x[symmetric])
  by (meson CleanQ_RB_write_head_y_can_deq_x)

lemma CleanQ_CRB_Dequeue_X_Q_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_Deq_X_Q K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_Deq_X_Q K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, simp add:CleanQ_RB_enq_y_write_inv_all CleanQ_RB_write_head_y_can_enq_x[symmetric]
                      CleanQ_RB_write_head_y_can_deq_x[symmetric] )
  apply(simp add: CleanQ_RB_read_tail_x_def CleanQ_RB_write_head_y_def )
  by (metis CleanQ_RB_Invariants_def CleanQ_RB_deq_x_possible_def I4_rb_valid_def 
            prod.sel(1) rb_deq_def rb_deq_list_was_head rb_enq_write_same rb_valid_def 
            rb_write_can_deq rb_write_preserves_valid)
 
lemma CleanQ_CRB_Dequeue_X_R_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_Deq_X_R K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_Deq_X_R K \<acute>RingCRB bx \<rbrace>"
  by(vcg, simp add:CleanQ_RB_enq_y_write_inv_all)  

paragraph \<open>Y increments the head pointer\<close>

lemma CleanQ_CRB_Dequeue_X_P_incr_head:
"\<Gamma>\<turnstile> \<lbrace>  rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_Deq_X_P K rb bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_Deq_X_P K \<acute>RingCRB bx  \<rbrace>"
  apply(vcg, simp)
  by (meson CleanQ_RB_enq_y_inv_all CleanQ_RB_write_head_inv_all  CleanQ_RB_enq_y_deq_x_possible CleanQ_RB_write_head_inv_all)
  
lemma CleanQ_CRB_Dequeue_X_Q_incr_head:
"\<Gamma>\<turnstile> \<lbrace>  rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_Deq_X_Q K rb bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_Deq_X_Q K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto) 
  apply (meson CleanQ_RB_enq_y_inv_all CleanQ_RB_write_head_inv_all)
  apply (meson CleanQ_RB_enq_y_deq_x_possible CleanQ_RB_write_head_inv_all) 
  unfolding CleanQ_RB_read_tail_x_def CleanQ_RB_write_head_y_def CleanQ_RB_enq_y_def
  unfolding rb_read_tail_def rb_write_head_def rb_enq_def
  by (simp add: rb_incr_head_def)
  

lemma CleanQ_CRB_Dequeue_X_R_incr_head:
"\<Gamma>\<turnstile> \<lbrace>  rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_Deq_X_R K rb bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_Deq_X_R K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto)
  by (meson CleanQ_RB_enq_y_inv_all CleanQ_RB_write_head_inv_all)
  



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue X, Dequeue X\<close>
(* ------------------------------------------------------------------------------------ *)

lemma CleanQ_RB_enq_interfernce_1 :
"\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RingCRB \<and> CleanQ_RB_Invariants K \<acute>RingCRB \<and> 
     enq =  CleanQ_RB_enq_x_possible \<acute>RingCRB \<and> deq =  CleanQ_RB_deq_x_possible \<acute>RingCRB \<and>
     CleanQ_RB_deq_y_possible \<acute>RingCRB \<and> enq2 = CleanQ_RB_enq_y_possible \<acute>RingCRB   \<rbrace> 
    \<acute>b :== (CleanQ_RB_read_tail_y \<acute>RingCRB) 
    \<lbrace> rb' = \<acute>RingCRB \<and> CleanQ_RB_Invariants K \<acute> RingCRB \<and>
      enq =  CleanQ_RB_enq_x_possible \<acute>RingCRB \<and> deq =  CleanQ_RB_deq_x_possible \<acute>RingCRB \<and>
     CleanQ_RB_deq_y_possible \<acute>RingCRB \<and> enq2 = CleanQ_RB_enq_y_possible \<acute>RingCRB   \<rbrace>"
  by(vcg)
  

lemma CleanQ_RB_enq_interfernce_2 :
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RingCRB \<and> CleanQ_RB_Invariants K \<acute> RingCRB  \<and>
        deq =  CleanQ_RB_deq_x_possible \<acute>RingCRB \<and>
       CleanQ_RB_deq_y_possible \<acute>RingCRB \<and> enq2 = CleanQ_RB_enq_y_possible \<acute>RingCRB  \<and>
         b = CleanQ_RB_read_tail_y \<acute>RingCRB  \<rbrace> 
      \<acute>RingCRB :== (CleanQ_RB_incr_tail_y b \<acute>RingCRB) 
      \<lbrace> CleanQ_RB_Invariants K \<acute> RingCRB \<and> 
        CleanQ_RB_enq_x_possible \<acute>RingCRB \<and> deq =  CleanQ_RB_deq_x_possible \<acute>RingCRB \<and>
       enq2 = CleanQ_RB_enq_y_possible \<acute>RingCRB  \<and>  b \<in> rSY \<acute>RingCRB 
       \<rbrace>"

  apply (vcg, simp add: CleanQ_RB_deq_y_all_inv)
  by(simp add: CleanQ_RB_deq_y_enq_x_possible CleanQ_RB_deq_y_deq_x_possible 
               CleanQ_RB_deq_y_enq_y_possible CleanQ_RB_deq_y_result CleanQ_RB_read_tail_y_def)


lemma CleanQ_RB_enq_interfernce_3 :
    "\<Gamma>\<turnstile> \<lbrace>  rb' = \<acute>RingCRB \<and> CleanQ_RB_Invariants K \<acute> RingCRB \<and>
           enq = CleanQ_RB_enq_x_possible \<acute>RingCRB \<and> deq =  CleanQ_RB_deq_x_possible \<acute>RingCRB \<and>
           CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> deq2 =  CleanQ_RB_deq_y_possible \<acute>RingCRB \<and>
           b \<in> rSY \<acute>RingCRB  \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_write_head_y b \<acute>RingCRB)
        \<lbrace> CleanQ_RB_Invariants K \<acute> RingCRB \<and> b \<in> rSY \<acute>RingCRB  \<and>
         enq = CleanQ_RB_enq_x_possible \<acute>RingCRB \<and> deq =  CleanQ_RB_deq_x_possible \<acute>RingCRB \<and>
         CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> deq2 = CleanQ_RB_deq_y_possible \<acute>RingCRB \<rbrace>"
  apply(vcg, simp add:CleanQ_RB_enq_y_write_can_enq CleanQ_RB_write_head_y_can_enq_deq_simps
                      CleanQ_RB_enq_y_write_inv_all)
  by(simp add:CleanQ_RB_write_head_y_def)

 

lemma CleanQ_RB_enq_interfernce_4 :
 "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RingCRB \<and> CleanQ_RB_Invariants K \<acute> RingCRB \<and>
        enq = CleanQ_RB_enq_x_possible \<acute>RingCRB \<and>
        CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> deq2 =  CleanQ_RB_deq_y_possible \<acute>RingCRB \<and>
        b \<in> rSY \<acute>RingCRB \<and> rb = (CleanQ_RB_write_head_y b \<acute>RingCRB)   \<rbrace>
        \<acute>RingCRB :== (CleanQ_RB_incr_head_y b rb) 
        \<lbrace> CleanQ_RB_Invariants K \<acute> RingCRB \<and> b \<notin> rSY \<acute>RingCRB \<and>
         enq = CleanQ_RB_enq_x_possible \<acute>RingCRB \<and> CleanQ_RB_deq_x_possible \<acute>RingCRB \<and>
         deq2 =  CleanQ_RB_deq_y_possible \<acute>RingCRB 
 \<rbrace>"
  apply(vcg, simp add:CleanQ_RB_enq_y_inv_all CleanQ_RB_enq_y_enq_x_possible)
  apply (simp add: CleanQ_RB_enq_y_result CleanQ_RB_enq_y_deq_x_possible)
  by (meson CleanQ_RB_enq_y_deq_y_possible)


end 