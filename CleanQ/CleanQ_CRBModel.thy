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

lemma CleanQ_split_enq_x_equal:
  shows "CleanQ_RB_incr_head_x b (CleanQ_RB_write_head_x b rb) = CleanQ_RB_enq_x b rb"
  unfolding CleanQ_RB_incr_head_x_def CleanQ_RB_write_head_x_def CleanQ_RB_enq_x_def
  rb_enq_def by simp

lemma CleanQ_split_enq_y_equal:
  shows "CleanQ_RB_incr_head_y b (CleanQ_RB_write_head_y b rb) = CleanQ_RB_enq_y b rb"
  unfolding CleanQ_RB_incr_head_y_def CleanQ_RB_write_head_y_def CleanQ_RB_enq_y_def
  rb_enq_def by simp

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

lemma CleanQ_split_deq_y_equal:
  shows "(let b = CleanQ_RB_read_tail_y rb in CleanQ_RB_incr_tail_y b rb) = CleanQ_RB_deq_y rb"
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

lemma CleanQ_CRB_frame_x_I1 :
  fixes rb rb' K
  assumes frame: "frame_rb_weak_x rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows "I1_rb_img rb K"
  using assms unfolding frame_rb_weak_x_def 
  apply auto
  apply (metis CleanQ_RB_list_def UnCI UnE rb_delta_tail_incr set_append)
  apply (simp add: CleanQ_RB_list_def rb_delta_tail_incr)
  apply (metis CleanQ_RB_list_def UnCI UnE rb_delta_head_incr rb_delta_tail_incr set_append)
  apply (metis CleanQ_RB_list_def UnCI UnE rb_delta_head_incr set_append)
  apply (metis CleanQ_RB_list_def Int_iff UnE Un_commute inf_sup_absorb rb_delta_head_incr 
         rb_delta_tail_incr set_append)
  by (metis CleanQ_RB_list_def UnCI rb_delta_head_incr set_append)

lemma CleanQ_CRB_frame_y_I1 :
  fixes rb rb' K
  assumes frame: "frame_rb_weak_y rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows "I1_rb_img rb K"
  using assms unfolding frame_rb_weak_y_def 
  apply auto
  apply (metis CleanQ_RB_list_def UnCI UnE rb_delta_tail_incr set_append)
  apply (metis CleanQ_RB_list_def UnCI UnE rb_delta_head_incr rb_delta_tail_incr set_append)
  apply (simp add: CleanQ_RB_list_def rb_delta_tail_incr)
  apply (metis CleanQ_RB_list_def UnE UnI2 Un_commute rb_delta_head_incr set_append)
  apply (metis CleanQ_RB_list_def UnCI rb_delta_head_incr set_append)
  by (metis CleanQ_RB_list_def Int_iff UnE Un_commute inf_sup_absorb rb_delta_head_incr 
      rb_delta_tail_incr set_append)

lemma frame_rb_weak_x_in_deltaxy_notin_txy:
  fixes rb rb' K
  assumes frame: "frame_rb_weak_x rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows "x \<in> set (rb_delta_tail_st (rTXY rb') (rTXY rb)) \<Longrightarrow> x \<notin> set (CleanQ_RB_list (rTXY rb))"
  using assms apply simp unfolding rb_delta_tail_st_def CleanQ_RB_list_def
  by (metis (no_types, lifting) disjoint_iff_not_equal distinct_append frame_weak_x_tl_delta invariants rb_delta_tail_st_def)

lemma frame_rb_weak_y_in_deltaxy_notin_txy:
  fixes rb rb' K
  assumes frame: "frame_rb_weak_y rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows "x \<in> set (rb_delta_tail_st (rTYX rb') (rTYX rb)) \<Longrightarrow> x \<notin> set (CleanQ_RB_list (rTYX rb))"
  using assms apply simp unfolding rb_delta_tail_st_def CleanQ_RB_list_def
  by (metis (no_types, lifting) disjoint_iff_not_equal distinct_append frame_weak_y_tl_delta invariants 
      rb_delta_tail_st_def)

lemma frame_rb_weak_x_in_sy_notin_txy:
  fixes rb rb' K
  assumes frame: "frame_rb_weak_x rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows" x \<in> rSY rb \<Longrightarrow> x \<in> set (CleanQ_RB_list (rTXY rb)) \<Longrightarrow> False"
  by (smt CleanQ_RB_Invariants.elims(2) CleanQ_RB_list_def I2_rb_img.simps I3_rb_img.simps Int_iff 
      UnE disjoint_insert(1) distinct_append frame frame_weak_x_sy_delta frame_weak_x_tl_delta 
      inf_sup_absorb inf_sup_aci(5) insert_Diff invariants set_append)

lemma frame_rb_weak_y_in_sx_notin_tyx:
  fixes rb rb' K
  assumes frame: "frame_rb_weak_y rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows" x \<in> rSX rb \<Longrightarrow> x \<in> set (CleanQ_RB_list (rTYX rb)) \<Longrightarrow> False"
  by (smt CleanQ_RB_Invariants.elims(2) CleanQ_RB_list_def I2_rb_img.simps I3_rb_img.simps Int_iff 
      UnE disjoint_insert(1) distinct_append frame frame_weak_y_sx_delta frame_weak_y_tl_delta 
      inf_sup_absorb inf_sup_aci(5) insert_Diff invariants set_append)

lemma frame_rb_weak_y_in_sx_notin_txy:
  fixes rb rb' K
  assumes frame: "frame_rb_weak_y rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows" x \<in> rSX rb \<Longrightarrow> x \<in> set (CleanQ_RB_list (rTXY rb)) \<Longrightarrow> False"
  by (smt CleanQ_RB_Invariants.elims(2) CleanQ_RB_list_def I2_rb_img.elims(2) Int_iff UnE 
      Un_commute disjoint_iff_not_equal frame frame_weak_y_hd_delta frame_weak_y_sx_delta 
      frame_weak_y_sy frame_weak_y_tl_delta inf_sup_absorb invariants set_append)

lemma frame_rb_weak_x_in_txy_notin_tyx:
  fixes rb rb' K
  assumes frame: "frame_rb_weak_x rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"  
  shows "x \<in> set (CleanQ_RB_list (rTXY rb)) \<Longrightarrow> x \<in> set (CleanQ_RB_list (rTYX rb)) \<Longrightarrow> False"
  using frame unfolding frame_rb_weak_x_def
proof -
  assume a1: "rSX rb = rSX rb' \<and> frame_rb_weak_left (rTXY rb') (rTXY rb) \<and> frame_rb_weak_right (rTYX rb') (rTYX rb) \<and> rSY rb' \<union> set (rb_delta_tail_st (rTXY rb') (rTXY rb)) = set (rb_delta_head_st (rTYX rb') (rTYX rb)) \<union> rSY rb \<and> distinct (rb_delta_head_st (rTYX rb') (rTYX rb)) \<and> rSY rb \<inter> set (rb_delta_head_st (rTYX rb') (rTYX rb)) = {}"
  assume a2: "x \<in> set (CleanQ_RB_list (rTXY rb))"
  assume a3: "x \<in> set (CleanQ_RB_list (rTYX rb))"
  have f4: "\<And>a. a \<notin> set (CleanQ_RB_list (rTXY rb)) \<or> a \<in> set (CleanQ_RB_list (rTXY rb'))"
    by (metis (no_types) CleanQ_RB_list_def UnCI frame frame_weak_x_tl_delta invariants set_append)
  then have f5: "x \<notin> rSY rb'"
    using a2 by (meson CleanQ_RB_Invariants.elims(2) I2_rb_img.simps disjoint_iff_not_equal invariants)
  have "x \<notin> set (CleanQ_RB_list (rTYX rb'))"
    using f4 a2 by (meson CleanQ_RB_Invariants.elims(2) I2_rb_img.simps disjoint_iff_not_equal invariants)
  then show ?thesis
    by (smt CleanQ_RB_Invariants.elims(2) CleanQ_RB_list_def I3_rb_img.elims(2) Int_iff Set.set_insert 
        UnE a1 a2 a3 disjoint_insert(1) distinct_append f5 frame frame_weak_x_tl_delta inf_sup_absorb 
        invariants rb_delta_head_incr set_append)
qed 

lemma CleanQ_CRB_frame_x_I2 :
  fixes rb rb' K
  assumes frame: "frame_rb_weak_x rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows "I2_rb_img rb"
  using assms unfolding frame_rb_weak_x_def 
  apply auto
  apply (smt CleanQ_RB_list_def IntE UnE Un_commute disjoint_iff_not_equal inf_sup_absorb 
         rb_delta_tail_incr set_append)
  apply (metis CleanQ_RB_list_def UnCI disjoint_iff_not_equal rb_delta_tail_incr set_append)
  apply (smt CleanQ_RB_list_def Int_iff UnE disjoint_iff_not_equal inf_sup_absorb rb_delta_head_incr 
         rb_delta_tail_incr set_append)
  prefer 2
  apply (smt CleanQ_RB_list_def IntE UnE Un_commute disjoint_iff_not_equal inf_sup_absorb 
         rb_delta_head_incr rb_delta_tail_incr set_append)
  apply (meson frame frame_rb_weak_x_in_sy_notin_txy invariants)
  by (meson frame frame_rb_weak_x_in_txy_notin_tyx invariants)

lemma CleanQ_CRB_frame_y_I2 :
  fixes rb rb' K
  assumes frame: "frame_rb_weak_y rb' rb"
    and invariants : "CleanQ_RB_Invariants K rb'"
  shows "I2_rb_img rb"
  using assms unfolding frame_rb_weak_y_def 
  apply auto
  apply (smt CleanQ_RB_list_def IntE UnE Un_commute disjoint_iff_not_equal inf_sup_absorb 
         rb_delta_tail_incr set_append)
  prefer 2 apply (meson frame frame_rb_weak_y_in_sx_notin_tyx invariants) 
  prefer 3 apply (metis CleanQ_RB_list_def UnCI disjoint_iff_not_equal rb_delta_tail_incr set_append)
  apply (meson frame frame_rb_weak_y_in_sx_notin_txy invariants)
  apply (smt CleanQ_RB_list_def IntE UnE disjoint_iff_not_equal inf_sup_absorb rb_delta_head_incr 
          rb_delta_tail_incr set_append)
  by (smt CleanQ_RB_list_def Int_iff UnE Un_commute disjoint_iff_not_equal distinct_append 
      inf_sup_absorb rb_delta_head_incr rb_delta_tail_incr set_append)
  

end 