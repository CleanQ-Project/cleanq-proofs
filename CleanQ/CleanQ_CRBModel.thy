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

text \<open>
  The first part of the \verb+enqueue+ operation is to write head buffer element into
  the ring at the head position.
\<close>

definition CleanQ_RB_write_head_x :: "'a \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> 'a CleanQ_RB_State" 
  where "CleanQ_RB_write_head_x b rb = rb \<lparr>rTXY := rb_write_head b (rTXY rb) \<rparr>"

definition CleanQ_RB_write_head_y :: "'a \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> 'a CleanQ_RB_State" 
  where "CleanQ_RB_write_head_y b rb = rb \<lparr>rTYX := rb_write_head b (rTYX rb) \<rparr>"

text \<open>
  The second part is to increment the head pointer, this effectively transfers the 
  ownership of the buffer from the owning sets SX or SY to the transfer set TXY or TYX. 
\<close>

definition CleanQ_RB_incr_head_x :: "'a \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> 'a CleanQ_RB_State" 
  where "CleanQ_RB_incr_head_x b rb = rb \<lparr>rTXY := rb_incr_head (rTXY rb), 
                                          rSX := (rSX rb) - {b} \<rparr>"

definition CleanQ_RB_incr_head_y :: "'a \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> 'a CleanQ_RB_State" 
  where "CleanQ_RB_incr_head_y b rb = rb \<lparr> rTYX := rb_incr_head (rTYX rb), 
                                           rSY := (rSY rb) - {b} \<rparr>"


text \<open>
  We define helper functions to read the head pointer of the ring buffer and to check
  whether the head position of the ring is \verb+None+ or it contains some buffer.
\<close>

definition CleanQ_RB_read_head_x :: "'a CleanQ_RB_State \<Rightarrow> 'a " 
  where "CleanQ_RB_read_head_x rb = rb_read_head (rTXY rb)"

definition CleanQ_RB_read_head_y :: "'a CleanQ_RB_State \<Rightarrow> 'a " 
  where "CleanQ_RB_read_head_y rb = rb_read_head (rTYX rb)"

definition CleanQ_RB_head_none_x :: "'a CleanQ_RB_State \<Rightarrow> bool" 
  where "CleanQ_RB_head_none_x rb = rb_head_none (rTXY rb)"

definition CleanQ_RB_head_none_y :: "'a CleanQ_RB_State \<Rightarrow> bool" 
  where "CleanQ_RB_head_none_y rb = rb_head_none (rTYX rb)"


text \<open> 
  Writing the head location in the ring ensures that the head is not none. 
\<close>

lemma CleanQ_RB_head_write_x_not_none:
  "\<not>CleanQ_RB_head_none_x (CleanQ_RB_write_head_x b rb)"
  unfolding CleanQ_RB_head_none_x_def CleanQ_RB_write_head_x_def
  by (simp add: rb_write_head_not_none)

lemma CleanQ_RB_head_write_y_not_none:
  "\<not>CleanQ_RB_head_none_y (CleanQ_RB_write_head_y b rb)"
  unfolding CleanQ_RB_head_none_y_def CleanQ_RB_write_head_y_def
  by (simp add: rb_write_head_not_none)

lemma CleanQ_RB_write_head_read_head_x:
  "b = CleanQ_RB_read_head_x (CleanQ_RB_write_head_x b rb)"
  unfolding CleanQ_RB_read_head_x_def CleanQ_RB_write_head_x_def
  by (simp add: rb_read_head_def rb_write_head_element_read)

lemma CleanQ_RB_write_head_read_head_y:
  "b = CleanQ_RB_read_head_y (CleanQ_RB_write_head_y b rb)"
  unfolding CleanQ_RB_read_head_y_def CleanQ_RB_write_head_y_def
  by (simp add: rb_read_head_def rb_write_head_element_read)


text \<open>
  We first show, that the combination of the two operation, yields the original 
  \verb+enqueue+ operation of the sequential ring buffer model. We add those two to
  the simp set.
\<close>

lemma CleanQ_RB_enq_x_split_equal[simp]:
  "CleanQ_RB_incr_head_x b (CleanQ_RB_write_head_x b rb) = CleanQ_RB_enq_x b rb"
  unfolding CleanQ_RB_incr_head_x_def CleanQ_RB_write_head_x_def CleanQ_RB_enq_x_def
  rb_enq_def by simp

lemma CleanQ_RB_enq_y_split_equal[simp]:
  "CleanQ_RB_incr_head_y b (CleanQ_RB_write_head_y b rb) = CleanQ_RB_enq_y b rb"
  unfolding CleanQ_RB_incr_head_y_def CleanQ_RB_write_head_y_def CleanQ_RB_enq_y_def
  rb_enq_def by simp


text \<open>
  Secondly, we can show that if the head of the ring contains some buffer $b$, then 
  just incrementing the head pointer, results in an equivalent state as when we
  enqueue this buffer. Note, due to the definitions of reading the head element, 
  we need to have an additional assumption, that the head is actually not none. 

  We show that writing the head with the same element that currently there, yields the
  same state. Note, this is trivial, but a proof is required due to the definition of
  the read operation.
\<close>

lemma CleanQ_RB_write_head_x_equiv:
assumes notnone: "\<not>CleanQ_RB_head_none_x rb"  and buf: "b = (CleanQ_RB_read_head_x rb)"
  shows "CleanQ_RB_write_head_x b rb = rb"
  using assms 
  unfolding CleanQ_RB_write_head_x_def CleanQ_RB_head_none_x_def CleanQ_RB_read_head_x_def
  by (simp add: rb_write_head_same)

lemma CleanQ_RB_write_head_y_equiv:
assumes notnone: "\<not>CleanQ_RB_head_none_y rb"  and buf: "b = (CleanQ_RB_read_head_y rb)"
  shows "CleanQ_RB_write_head_y b rb = rb"
  using assms 
  unfolding CleanQ_RB_write_head_y_def CleanQ_RB_head_none_y_def CleanQ_RB_read_head_y_def
  by (simp add: rb_write_head_same)


text \<open>
  Using the state equivalence, we can now show that we can simply increment the head 
  which yields the same as if we were to do a full \verb+enqueue+ operation.
\<close>

lemma CleanQ_RB_enq_x_equiv_incr_head:
assumes notnone: "\<not>CleanQ_RB_head_none_x rb"  and buf: "b = (CleanQ_RB_read_head_x rb)"
  shows "CleanQ_RB_incr_head_x b rb = CleanQ_RB_enq_x b rb"
  by (metis CleanQ_RB_enq_x_split_equal CleanQ_RB_write_head_x_equiv buf notnone)

lemma CleanQ_RB_enq_y_equiv_incr_head:
assumes notnone: "\<not>CleanQ_RB_head_none_y rb"  and buf: "b = (CleanQ_RB_read_head_y rb)"
  shows "CleanQ_RB_incr_head_y b rb = CleanQ_RB_enq_y b rb"
  by (metis CleanQ_RB_enq_y_split_equal CleanQ_RB_write_head_y_equiv buf notnone)


text \<open>
  Just writing the head element in the ring, does not change the state when its lifted
  to the list model. 
\<close>

lemma CleanQ_RB_write_head_x_list[simp]:
  "CleanQ_RB_list (rTXY (CleanQ_RB_write_head_x b rb)) = CleanQ_RB_list (rTXY rb)"
  by (metis CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective rb_enq_write_same
            CleanQ_RB_State.update_convs(3) CleanQ_RB_write_head_x_def)
    
lemma CleanQ_RB_write_head_y_list[simp]:
 "CleanQ_RB_list (rTYX (CleanQ_RB_write_head_y b rb)) = CleanQ_RB_list (rTYX rb)"
  by (metis CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective rb_enq_write_same
            CleanQ_RB_State.update_convs(4) CleanQ_RB_write_head_y_def)


text \<open>
  The entire lifted state to the list model is not changed at all.  
\<close>

lemma CleanQ_RB_write_head_x_lift_full:
  "CleanQ_RB2List (CleanQ_RB_write_head_x b rb) = CleanQ_RB2List rb"
  unfolding CleanQ_RB2List_def by (simp, auto simp: CleanQ_RB_write_head_x_def)

lemma CleanQ_RB_write_head_y_lift_full:
  "CleanQ_RB2List (CleanQ_RB_write_head_y b rb) = CleanQ_RB2List rb"
  unfolding CleanQ_RB2List_def by (simp, auto simp: CleanQ_RB_write_head_y_def)


text \<open>
  Writing the head preserves all \verb+can_enq+ and \verb+can_deq+ predicates. 
\<close>

lemma CleanQ_RB_write_head_y_can_enq_x:
  "CleanQ_RB_enq_x_possible rb = CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_y b rb)"
  by (simp add: CleanQ_RB_write_head_y_def CleanQ_RB_enq_x_possible_def) 

lemma CleanQ_RB_write_head_y_can_deq_x:
 "CleanQ_RB_deq_x_possible rb = CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_y b rb)"
  by(simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_write_head_y_def rb_write_can_deq)

lemma CleanQ_RB_write_head_y_can_deq_y:
  "CleanQ_RB_deq_y_possible rb = CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_y b rb)"
  by (simp add: CleanQ_RB_deq_y_possible_def CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_write_head_y_can_enq_y:
 "CleanQ_RB_enq_y_possible rb = CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_y b rb)"
  by(simp add: CleanQ_RB_enq_y_possible_def CleanQ_RB_write_head_y_def rb_write_can_enq)


lemma CleanQ_RB_write_head_x_can_enq_x:
  "CleanQ_RB_enq_x_possible rb = CleanQ_RB_enq_x_possible (CleanQ_RB_write_head_x b rb)"
  by(simp add: CleanQ_RB_write_head_x_def CleanQ_RB_enq_x_possible_def rb_write_can_enq)

lemma CleanQ_RB_write_head_x_can_deq_x:
 "CleanQ_RB_deq_x_possible rb = CleanQ_RB_deq_x_possible (CleanQ_RB_write_head_x b rb)"
  by(simp add: CleanQ_RB_deq_x_possible_def CleanQ_RB_write_head_x_def rb_write_can_deq)

lemma CleanQ_RB_write_head_x_can_deq_y:
  "CleanQ_RB_deq_y_possible rb = CleanQ_RB_deq_y_possible (CleanQ_RB_write_head_x b rb)"
  by(simp add: CleanQ_RB_deq_y_possible_def CleanQ_RB_write_head_x_def rb_write_can_deq)

lemma CleanQ_RB_write_head_x_can_enq_y:
 "CleanQ_RB_enq_y_possible rb = CleanQ_RB_enq_y_possible (CleanQ_RB_write_head_x b rb)"
  by(simp add: CleanQ_RB_enq_y_possible_def CleanQ_RB_write_head_x_def rb_write_can_enq)



lemmas CleanQ_RB_write_head_y_can_enq_deq_simps = CleanQ_RB_write_head_y_can_enq_x 
                                                  CleanQ_RB_write_head_y_can_deq_x 
                                                  CleanQ_RB_write_head_y_can_deq_y 
                                                  CleanQ_RB_write_head_y_can_enq_y

lemmas CleanQ_RB_write_head_x_can_enq_deq_simps = CleanQ_RB_write_head_x_can_enq_x 
                                                  CleanQ_RB_write_head_x_can_deq_x 
                                                  CleanQ_RB_write_head_x_can_deq_y 
                                                  CleanQ_RB_write_head_x_can_enq_y
 

text \<open>
  Next we show that the write operation preserves the invariant. We show this individually, 
  plus also we show both ways, as a simple write to the ring, does not change anything
  in the observable state and thus also preserves the invariant.
\<close>

lemma CleanQ_RB_write_head_x_I1:
 "I1_rb_img rb K \<longleftrightarrow> I1_rb_img (CleanQ_RB_write_head_x b rb) K"
  by (simp add: CleanQ_RB_write_head_x_lift_full I1_rb_img_lift)

lemma CleanQ_RB_write_head_x_I2:
 "I2_rb_img rb \<longleftrightarrow> I2_rb_img (CleanQ_RB_write_head_x b rb)"
  by (simp add: CleanQ_RB_write_head_x_lift_full I2_rb_img_lift)

lemma CleanQ_RB_write_head_x_I3:
  "I3_rb_img rb \<longleftrightarrow> I3_rb_img (CleanQ_RB_write_head_x b rb)"
  by (simp add:  CleanQ_RB_write_head_x_lift_full I3_rb_img_lift)

lemma CleanQ_RB_write_head_x_I4:
  "I4_rb_valid rb \<longleftrightarrow> I4_rb_valid (CleanQ_RB_write_head_x b rb)"
  unfolding I4_rb_valid_def CleanQ_RB_write_head_x_def
  by(simp, meson rb_write_head_valid)

lemma CleanQ_RB_write_head_x_Invariant[simp]:
  "CleanQ_RB_Invariants K rb \<longleftrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_x b rb)"
  by (meson CleanQ_RB_Invariants_def CleanQ_RB_write_head_x_I1 CleanQ_RB_write_head_x_I2
            CleanQ_RB_write_head_x_I3 CleanQ_RB_write_head_x_I4)


lemma CleanQ_RB_write_head_y_I1:
 "I1_rb_img rb K \<longleftrightarrow> I1_rb_img (CleanQ_RB_write_head_y b rb) K"
  by (simp add: CleanQ_RB_write_head_y_lift_full I1_rb_img_lift)

lemma CleanQ_RB_write_head_y_I2:
 "I2_rb_img rb \<longleftrightarrow> I2_rb_img (CleanQ_RB_write_head_y b rb)"
  by (simp add: CleanQ_RB_write_head_y_lift_full I2_rb_img_lift)

lemma CleanQ_RB_write_head_y_I3:
  "I3_rb_img rb \<longleftrightarrow> I3_rb_img (CleanQ_RB_write_head_y b rb)"
  by (simp add:  CleanQ_RB_write_head_y_lift_full I3_rb_img_lift)

lemma CleanQ_RB_write_head_y_I4:
  "I4_rb_valid rb \<longleftrightarrow> I4_rb_valid (CleanQ_RB_write_head_y b rb)"
  unfolding I4_rb_valid_def CleanQ_RB_write_head_y_def
  by(simp, meson rb_write_head_valid)

lemma CleanQ_RB_write_head_y_Invariant[simp]:
  "CleanQ_RB_Invariants K rb \<longleftrightarrow> CleanQ_RB_Invariants K (CleanQ_RB_write_head_y b rb)"
  by (meson CleanQ_RB_Invariants_def CleanQ_RB_write_head_y_I1 CleanQ_RB_write_head_y_I2
            CleanQ_RB_write_head_y_I3 CleanQ_RB_write_head_y_I4)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Pre-Post Conditions for the Enqueue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  We now define the hoare triples for the enqueue operation. Those are needed to later
  for the interference proof. There are a total of three predicates for the enqueue
  operation in small step semantics, while the predicates P and R define the big 
  step semantics.

  \verb+{P} write_head {Q} incr_head {R}+ 

  We now provide abbreviations for each of the predicate P, Q, and R for the \verb+enqueue+
  operation as seen from Y and X.   
\<close>

paragraph \<open>Enqueue P\<close>

text \<open>
  The P predicate is the pre-condition for the \verb+enqueue+ operation. For the operation
  to succeed, the state must satisfy the Invariant plus an enqueue must be possible, i.e.
  there is space in the descriptor ring to hold the buffer. Lastly, the buffer to be 
  enqueued must be owned by the agent i.e. a member of the set SX or SY respectively.
  We provide two abbreviations for this, one for each side:\<close>

abbreviation "CleanQ_RB_enq_x_P K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> 
                                          CleanQ_RB_enq_x_possible rb \<and> b \<in> rSX rb"

abbreviation "CleanQ_RB_enq_y_P K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> 
                                          CleanQ_RB_enq_y_possible rb \<and> b \<in> rSY rb"

paragraph \<open>Enqueue Q\<close>

text \<open>
  The Q predicate is the post-condition for the write part of the  \verb+enqueue+ operation, 
  and the pre-condition of the increment part of the \verb+enqueue+ operation. The write
  operation does not transfer ownership of the buffer yet, thus the buffer remains in
  SX or SY respectively and the enqueue still remains possible. However, we now know, 
  that the buffer is written to the head location of the ring, and that this location
  is not \verb+None+.
\<close>

abbreviation "CleanQ_RB_enq_x_Q K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> 
                                          CleanQ_RB_enq_x_possible rb \<and> b \<in> rSX rb \<and> 
                                          b = CleanQ_RB_read_head_x rb \<and> 
                                          \<not>CleanQ_RB_head_none_x rb "

abbreviation "CleanQ_RB_enq_y_Q K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> 
                                          CleanQ_RB_enq_y_possible rb \<and> b \<in> rSY rb \<and>
                                           b = CleanQ_RB_read_head_y rb \<and> 
                                           \<not>CleanQ_RB_head_none_y rb "

paragraph \<open>Enqueue R\<close>


text \<open>
  The R predicate is the post condition for both, the increment head part as well as the
  full \verb+enqueue+ operation. We now that the buffer is now no longer in the owning 
  sets SX and SY. Note, we cannot make a state about whether it is in the ring, because
  the other side may have already taken it out. Also, we cannot make any statements
  about whether we can enqueue again.
\<close>

abbreviation "CleanQ_RB_enq_y_R K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> b \<notin> rSX rb"
abbreviation "CleanQ_RB_enq_x_R K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> b \<notin> rSY rb"







  


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




abbreviation "CleanQ_Deq_X_P K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> CleanQ_RB_deq_x_possible rb"
abbreviation "CleanQ_Deq_X_Q K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> CleanQ_RB_deq_x_possible rb \<and> b = CleanQ_RB_read_tail_x rb"
abbreviation "CleanQ_Deq_X_R K rb b \<equiv> CleanQ_RB_Invariants K rb"




(* ------------------------------------------------------------------------------------ *)
subsection \<open>Invariants are TRUE invariants\<close>
(* ------------------------------------------------------------------------------------ *)
text \<open>
  To show that the Invariants we defined are true invariants it has to hold at each
  step of the computation and not only at beginning and end. To show this
  we will show the invariant for each of the two steps of \verb+enqueue+ and \verb+dequeue+. 
\<close>



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Hoare Triples for the Enqueue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  We now show that the \verb+enqueue+ operation satisfies the pre and post conditions
  for the predicates P, Q and R. 
\<close>


paragraph \<open>Writing the Head Element\<close>

text \<open>
  We show the Hoare triple with \verb+{P) write_head {Q}+.
\<close>

lemma  CleanQ_RB_write_head_x_hoare:
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_P K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_write_head_x b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_enq_x_Q K \<acute> RingCRB b  \<rbrace>"                                                 
  apply(vcg, auto simp: CleanQ_RB_write_head_x_Invariant[symmetric] 
                        CleanQ_RB_write_head_x_can_enq_x[symmetric]
                        CleanQ_RB_write_head_read_head_x CleanQ_RB_head_write_x_not_none)
  by(simp add: CleanQ_RB_write_head_x_def)


lemma  CleanQ_RB_write_head_y_hoare:
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_y_P K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_write_head_y b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_enq_y_Q K \<acute> RingCRB b  \<rbrace>"                                                 
  apply(vcg, auto simp: CleanQ_RB_write_head_y_Invariant[symmetric] 
                        CleanQ_RB_write_head_y_can_enq_y[symmetric]
                        CleanQ_RB_write_head_read_head_y CleanQ_RB_head_write_y_not_none)
  by(simp add: CleanQ_RB_write_head_y_def)


paragraph \<open>Incrementing the Head Pointer\<close>

text \<open>
  We show the Hoare triple with \verb+{Q) incr_head {R}+.
\<close>

lemma  CleanQ_RB_incr_head_x_hoare:
  "\<Gamma>\<turnstile> \<lbrace>  CleanQ_RB_enq_x_Q K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_incr_head_x b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_enq_x_R K \<acute> RingCRB b  \<rbrace>"
  apply(vcg, simp add: CleanQ_RB_enq_x_equiv_incr_head CleanQ_RB_enq_x_inv_all)
  by (simp add: CleanQ_RB_enq_x_result)

lemma  CleanQ_RB_incr_head_y_hoare:
  "\<Gamma>\<turnstile> \<lbrace>  CleanQ_RB_enq_y_Q K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_incr_head_y b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_enq_y_R K \<acute> RingCRB b  \<rbrace>"
  apply(vcg, simp add: CleanQ_RB_enq_y_equiv_incr_head CleanQ_RB_enq_y_inv_all)
  by (simp add: CleanQ_RB_enq_y_result)


paragraph \<open>Full Enqueue Operation\<close>

text \<open>
  We show the Hoare triple with \verb+{P) enq {R}+.
\<close>

lemma CleanQ_RB_enq_x_hoare : 
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_P K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_write_head_x b \<acute>RingCRB) ;;
        \<acute>RingCRB :== (CleanQ_RB_incr_head_x b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_enq_x_R K \<acute>RingCRB b \<rbrace>"
  apply(vcg) using CleanQ_RB_enq_x_inv_all CleanQ_RB_enq_x_result by fastforce
 

lemma CleanQ_RB_enq_y_hoare : 
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_y_P K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_write_head_y b \<acute>RingCRB) ;;
        \<acute>RingCRB :== (CleanQ_RB_incr_head_y b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_enq_y_R K \<acute>RingCRB b \<rbrace>"
  apply(vcg) using CleanQ_RB_enq_y_inv_all CleanQ_RB_enq_y_result by fastforce



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Hoare Triples for the Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  We now show that the \verb+dequeue+ operation satisfies the pre and post conditions
  for the predicates P, Q and R. 
\<close>


paragraph \<open>Reading the Tail Element\<close>

text \<open>
  We show the Hoare triple with \verb+{P) read_tail {Q}+.
\<close>




paragraph \<open>Incrementing the Tail Pointer\<close>

text \<open>
  We show the Hoare triple with \verb+{Q) incr_tail {R}+.
\<close>



paragraph \<open>Full Dequeue Operation\<close>

text \<open>
  We show the Hoare triple with \verb+{P) deq {R}+.
\<close>



  


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



paragraph \<open>Y writes the descriptor ring\<close>

lemma CleanQ_CRB_Enqueue_X_P_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace>"
  apply(vcg, simp add: CleanQ_RB_write_head_y_can_enq_x[symmetric] CleanQ_RB_write_head_y_Invariant[symmetric])  
  by (simp add: CleanQ_RB_write_head_y_def)

lemma CleanQ_CRB_Enqueue_X_Q_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_Q K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_enq_x_Q K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto simp add: CleanQ_RB_write_head_y_can_enq_x[symmetric]
                            CleanQ_RB_write_head_y_Invariant[symmetric])
 
  apply (simp add: CleanQ_RB_write_head_y_def)
  apply (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_y_def)
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_y_def)


lemma CleanQ_CRB_Enqueue_X_R_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_R K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_enq_x_R K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto simp:CleanQ_RB_write_head_y_Invariant[symmetric])  
  by (simp add: CleanQ_RB_write_head_y_def)


  

paragraph \<open>Y increments the head\<close>

lemma CleanQ_CRB_Enqueue_X_P_incr_head:
"\<Gamma>\<turnstile> \<lbrace>  rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_RB_enq_x_P K rb bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace>"
  apply(vcg, auto)
    apply (meson CleanQ_RB_enq_y_inv_all CleanQ_RB_write_head_y_Invariant)
  apply (meson CleanQ_RB_enq_y_enq_x_possible CleanQ_RB_write_head_y_Invariant CleanQ_RB_write_head_y_can_enq_x)
  by (simp add: CleanQ_RB_enq_y_def CleanQ_RB_write_head_y_def)


lemma CleanQ_CRB_Enqueue_X_Q_incr_head:
"\<Gamma>\<turnstile> \<lbrace>  rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_RB_enq_x_Q K rb bx   \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_RB_enq_x_Q K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto)
  apply (meson CleanQ_RB_enq_y_inv_all CleanQ_RB_write_head_y_Invariant)
  apply (meson CleanQ_RB_enq_y_enq_x_possible CleanQ_RB_write_head_y_Invariant CleanQ_RB_write_head_y_can_enq_x)
    apply (simp add: CleanQ_RB_enq_y_def CleanQ_RB_write_head_y_def)
   apply (simp add: CleanQ_RB_enq_y_def CleanQ_RB_read_head_x_def CleanQ_RB_write_head_y_def)
  by (simp add: CleanQ_RB_enq_y_def CleanQ_RB_head_none_x_def CleanQ_RB_write_head_y_def)
  
  
lemma CleanQ_CRB_Enqueue_X_R_incr_head:
"\<Gamma>\<turnstile> \<lbrace> rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_RB_enq_x_R K rb bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_RB_enq_x_R K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto)
  apply (meson CleanQ_RB_enq_y_inv_all CleanQ_RB_write_head_y_Invariant)
  by (simp add: CleanQ_RB_enq_y_def CleanQ_RB_write_head_y_def)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue X, Dequeue X\<close>
(* ------------------------------------------------------------------------------------ *)

paragraph \<open>Y reads the descriptor ring\<close>

lemma CleanQ_CRB_Enqueue_X_P_read_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace> 
     \<acute>b :== CleanQ_RB_read_tail_y \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace>"
  by(vcg)

lemma CleanQ_CRB_Enqueue_X_Q_read_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_Q K \<acute>RingCRB bx  \<rbrace> 
     \<acute>b :== CleanQ_RB_read_tail_y \<acute>RingCRB
  \<lbrace>  CleanQ_RB_enq_x_Q K \<acute>RingCRB bx \<rbrace>"
  by(vcg)

lemma CleanQ_CRB_Enqueue_X_R_read_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_R K \<acute>RingCRB bx  \<rbrace> 
     \<acute>b :== CleanQ_RB_read_tail_y \<acute>RingCRB
  \<lbrace>  CleanQ_RB_enq_x_R K \<acute>RingCRB bx \<rbrace>"
   by(vcg)

paragraph \<open>Y increments the tail pointer\<close>

lemma CleanQ_CRB_Enqueue_X_P_incr_tail:
"\<Gamma>\<turnstile> \<lbrace>  b = CleanQ_RB_read_tail_y  \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_deq_y_possible \<acute>RingCRB \<and> CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace> 
      \<acute>RingCRB  :== CleanQ_RB_incr_tail_y b  \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace>"
  apply(vcg, auto simp:CleanQ_RB_deq_y_all_inv CleanQ_RB_deq_y_enq_x_possible )  
  using CleanQ_RB_deq_y_no_change by blast

lemma CleanQ_CRB_Enqueue_X_Q_incr_tail:
"\<Gamma>\<turnstile> \<lbrace>  b = CleanQ_RB_read_tail_y  \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_deq_y_possible \<acute>RingCRB \<and> CleanQ_RB_enq_x_Q K \<acute>RingCRB bx  \<rbrace> 
     \<acute>RingCRB  :== CleanQ_RB_incr_tail_y b  \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_enq_x_Q K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto simp:CleanQ_RB_deq_y_all_inv CleanQ_RB_deq_y_enq_x_possible ) 
  using CleanQ_RB_deq_y_no_change apply blast
  apply (metis CleanQ_RB_Invariants_def CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def I2_rb_img_def I4_rb_valid_def IntI empty_iff prod.sel(1) rb_deq_def rb_deq_list_was_in)
  by (metis CleanQ_RB_Invariants_def CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def I2_rb_img_def I4_rb_valid_def IntI empty_iff prod.sel(1) rb_deq_def rb_deq_list_was_in)

lemma CleanQ_CRB_Enqueue_X_R_incr_tail:
"\<Gamma>\<turnstile> \<lbrace>  b = CleanQ_RB_read_tail_y  \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_deq_y_possible \<acute>RingCRB \<and> CleanQ_RB_enq_x_R K \<acute>RingCRB bx  \<rbrace> 
     \<acute>RingCRB  :== CleanQ_RB_incr_tail_y b  \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_enq_x_R K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto simp:CleanQ_RB_deq_y_all_inv CleanQ_RB_deq_y_enq_x_possible )
  by (metis CleanQ_RB_Invariants_def CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def 
            I2_rb_img_def I4_rb_valid_def IntI empty_iff prod.sel(1) rb_deq_def rb_deq_list_was_in)





(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue X, Enqueue Y\<close>
(* ------------------------------------------------------------------------------------ *)

paragraph \<open>Y writes the descriptor ring\<close>

lemma CleanQ_CRB_Dequeue_X_P_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_Deq_X_P K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_Deq_X_P K \<acute>RingCRB bx  \<rbrace>"
  apply(vcg, auto)
  apply (meson CleanQ_RB_write_head_y_Invariant)
  by (meson CleanQ_RB_write_head_y_can_deq_x)

lemma CleanQ_CRB_Dequeue_X_Q_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_Deq_X_Q K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_Deq_X_Q K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, simp add: CleanQ_RB_write_head_y_can_enq_x[symmetric]
                      CleanQ_RB_write_head_y_can_deq_x[symmetric] )
  by (metis CleanQ_RB_Invariants_def CleanQ_RB_deq_x_possible_def CleanQ_RB_list_def 
            CleanQ_RB_read_tail_x_def CleanQ_RB_write_head_y_I4 CleanQ_RB_write_head_y_Invariant 
              CleanQ_RB_write_head_y_can_deq_x CleanQ_RB_write_head_y_list I4_rb_valid_def prod.sel(1) 
              rb_deq_def rb_deq_list_was_head rb_read_tail_def rb_valid_implies_ptr_valid)
 
lemma CleanQ_CRB_Dequeue_X_R_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_Deq_X_R K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_Deq_X_R K \<acute>RingCRB bx \<rbrace>"
  apply(vcg)  
  by (smt CleanQ_RB_write_head_y_Invariant Collect_cong hoarep.Basic mem_Collect_eq select_convs(1) 
          surjective update_convs(1))

paragraph \<open>Y increments the head pointer\<close>

lemma CleanQ_CRB_Dequeue_X_P_incr_head:
"\<Gamma>\<turnstile> \<lbrace>  rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_Deq_X_P K rb bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_Deq_X_P K \<acute>RingCRB bx  \<rbrace>"
  apply(vcg, simp)
  by (meson CleanQ_RB_enq_y_deq_x_possible CleanQ_RB_enq_y_inv_all CleanQ_RB_write_head_y_Invariant)
  

  
lemma CleanQ_CRB_Dequeue_X_Q_incr_head:
"\<Gamma>\<turnstile> \<lbrace>  rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_Deq_X_Q K rb bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_Deq_X_Q K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto) 
  apply (meson CleanQ_RB_enq_y_inv_all CleanQ_RB_write_head_y_Invariant)
  apply (meson CleanQ_RB_enq_y_deq_x_possible CleanQ_RB_write_head_y_Invariant)
  unfolding CleanQ_RB_read_tail_x_def CleanQ_RB_write_head_y_def CleanQ_RB_enq_y_def
  unfolding rb_read_tail_def rb_write_head_def rb_enq_def
  by (simp add: rb_incr_head_def)
  

lemma CleanQ_CRB_Dequeue_X_R_incr_head:
"\<Gamma>\<turnstile> \<lbrace>  rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_Deq_X_R K rb bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_Deq_X_R K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto)
  by (meson CleanQ_RB_enq_y_inv_all CleanQ_RB_write_head_y_Invariant)
  
  



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