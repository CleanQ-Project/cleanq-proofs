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



section \<open>CleanQ Abstract Ring Buffer Model\<close>

text \<open>
  The second refinement is from unbounded lists to bounded buffer rings for transferring
  ownership between two agents. As a consequence, the \verb+enqueue+ operation may fail, 
  because there is no more space in the ring buffer. 
\<close>

theory CleanQ_RBModel 
(*<*) 
  imports Main "../Simpl/Vcg"  "../Complx/OG_Hoare" CleanQ_ListModel CleanQ_RB
(*>*)  
begin


(* ==================================================================================== *)
subsection \<open>CleanQ Abstract Ring Buffer Model State\<close>
(* ==================================================================================== *)

text \<open>
  We take the state of the CleanQ list model and refine it to use a bounded, circular
  buffer instead of the lists as transfer sets between the two agents. Again, there is
  one queue (ring buffer) going from $X$ to $Y$ and another one, for the opposit
  direction. Expressing the buffers owned by $X$ and $Y$ remain the same. 

  \<^item> rSX: this is the set of buffers owned by X.
  \<^item> rSY: this is the set of buffers owned by Y.
  \<^item> rTXY: this is a descriptor ring of buffers in transfer from X to Y.
  \<^item> rTYX: this is a descriptor ring of buffers in transfer from Y to X.
\<close>



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>System State\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  We now define the updated system state using \verb+Cleanq_RB+  for the transfer sets
  between $X$ and $Y$. 
 \<close>

record 'a CleanQ_RB_State =
  rSX  :: "'a set"
  rSY  :: "'a set"
  rTXY :: "'a CleanQ_RB"
  rTYX :: "'a CleanQ_RB"


text \<open>
  Like the abstract list model,  we do not specify the representation of the buffer 
  elements. This can be a single, fixed-sized page frame, a variable-sized base-limit 
  segment, or a set of memory locations. 
\<close>


(*<*)
(* Define some global variables to make Simpl/Complex proofs work *)
record 'g CleanQ_RB_State_vars = 
  RingRB_'  :: "nat CleanQ_RB_State"
(*>*)


(* ==================================================================================== *)
subsection \<open>State Lifting Function\<close>
(* ==================================================================================== *)

text \<open>
  The CleanQ RB model is a data refinement of the CleanQ List Model. We can define an
  interpretation function. That lifts the CleanQ RB model state into the CleanQ
  list model state by extracting a list of buffers as a subset of the ringbuffer. 
  We first define a function to convert the ringbuffer representation in to a list, which
  we use the \verb+nonzero_modulus+ locale to produce a list of indices into the bounded
  buffer ring and apply them to the \verb+ring+ function of the ringbuffer.
\<close>


text \<open>
  Then we use this conversion int he state lifting from the RB model to the list model.
\<close>

definition CleanQ_RB2List :: "'a CleanQ_RB_State  \<Rightarrow> 'a CleanQ_List_State"
  where "CleanQ_RB2List l = \<lparr> lSX = rSX l, lSY = rSY l, 
                               lTXY = CleanQ_RB_list (rTXY l), 
                               lTYX = CleanQ_RB_list (rTYX l) \<rparr>"



(* ==================================================================================== *)
subsection \<open>CleanQ RB Model Invariants\<close>
(* ==================================================================================== *)

text \<open>
  We now revisit the invariants of the CleanQ list model and specify additional invariants
  for the CleanQ Ring Buffer model. 
\<close>


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I1: Constant Union (Image)\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  The union of all sets is constant. We formulate this as an image for 
  \verb+CleanQ_List+ where we take the set of the transfer lists and apply the 
  union.
\<close>

fun I1_rb_img :: "'a CleanQ_RB_State \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1_rb_img rb K \<longleftrightarrow> ((rSX rb) \<union> (rSY rb) 
                                \<union> set (CleanQ_RB_list (rTXY rb)) 
                                \<union> set (CleanQ_RB_list (rTYX rb))) = K"

text \<open>
  We can show that the image of the invariant satisfies the list invariant I1 when
  we apply the lifting function \verb+CleanQ_RB2List+ to the model state. We prove
  this in the following lemma.
\<close>

lemma I1_rb_img_lift:
  "I1_rb_img R K = I1_list_img (CleanQ_RB2List R) K"
  unfolding CleanQ_RB2List_def by(simp)

lemma "I1_rb_img R K = I1 (CleanQ_List2Set (CleanQ_RB2List R)) K"
  unfolding CleanQ_RB2List_def CleanQ_List2Set_def by(simp)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I2: Pairwise Empty (Image)\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
 All pairwise intersections are empty. Again, we formulate this as an image for
 \verb+CleanQ_RB+ by extracting the list of buffers from the ring.
\<close>

fun I2_rb_img :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I2_rb_img rb \<longleftrightarrow> rSX rb \<inter> rSY rb = {} 
           \<and> rSX rb \<inter> set (CleanQ_RB_list (rTXY rb)) = {} 
           \<and> rSX rb \<inter> set (CleanQ_RB_list (rTYX rb)) = {} 
           \<and> rSY rb \<inter> set (CleanQ_RB_list (rTXY rb)) = {} 
           \<and> rSY rb \<inter> set (CleanQ_RB_list (rTYX rb)) = {} 
           \<and> set (CleanQ_RB_list (rTXY rb)) \<inter> set (CleanQ_RB_list (rTYX rb)) = {}"


text \<open>
  Finally, we can show that the image of the Invariant I2 is equivalent to the list 
  version of this invariant, when we lift the CleanQ RB State to the CleanQ List State. 
  We prove this in the following lemma:
\<close>

lemma I2_rb_img_lift:
  "I2_rb_img R = I2_list_img (CleanQ_RB2List R)"
  unfolding CleanQ_RB2List_def by(simp)


lemma "I2_rb_img R = I2 (CleanQ_List2Set (CleanQ_RB2List R))"
  unfolding CleanQ_RB2List_def CleanQ_List2Set_def by(simp)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I3: Distinct Transferlists\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  Next we provide an interpretation of the I3 invariant in the ring buffer representation. 
\<close>

fun I3_rb_img :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I3_rb_img st_list \<longleftrightarrow> distinct (CleanQ_RB_list (rTXY st_list)) 
                             \<and> distinct (CleanQ_RB_list (rTYX st_list))"


lemma I3_rb_img_lift:
  "I3_rb_img R = I3 (CleanQ_RB2List R)"
  unfolding CleanQ_RB2List_def by(simp)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I4: Valid Ringbuffers\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  For well-defined outcomes, we need to have well-defined ringbuffers in the state. 
  We define this Invariant to be the conjunction of the \verb+rb_valid+ predicates
  for both ringbuffers in the state.
\<close>

fun I4_rb_valid :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I4_rb_valid rb \<longleftrightarrow> ((rb_valid (rTXY rb)) \<and> (rb_valid (rTYX rb)))"

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Strong and Weak frame condition\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>The strong frame condition fixed the full state except for the part which should
      change. \<close>
definition frame_rb_strong :: "'a CleanQ_RB_State \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> bool"
  where "frame_rb_strong rb' rb \<longleftrightarrow> rb' = rb"

text \<open>
  Assuming a two concurrently acting agents, we can not assume that all of the RB state
  stays the same. In order to model this, we have to weaken the frame condition which
  we up to now implicitly used. \<close>
(* Need to express somehow that descriptors can be added by enq *)
definition frame_rb_weak_x :: "'a CleanQ_RB_State \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> bool"
  where "frame_rb_weak_x st' st \<longleftrightarrow>
   (\<exists>\<delta>tyx \<delta>txy.
    ring (rTXY st') = ring (rTXY st) \<and>
    size (rTXY st') = size (rTXY st) \<and>
    size (rTYX st') = size (rTYX st) \<and>
    rSX st' = rSX st \<and>
    CleanQ_RB_list (rTXY st') =  CleanQ_RB_list (rTXY st) @ \<delta>tyx \<and>
    \<delta>tyx @ CleanQ_RB_list (rTYX st') = CleanQ_RB_list (rTYX st) \<and>
    rSY st' = \<delta>txy \<union> rSY st - (set \<delta>tyx))" 

definition frame_rb_weak_y :: "'a CleanQ_RB_State \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> bool"
  where "frame_rb_weak_y st' st \<longleftrightarrow>
    head (rTYX st') = head (rTYX st) \<and>
    tail (rTXY st') = tail (rTXY st) \<and>
    ring (rTYX st') = ring (rTYX st) \<and>
    size (rTYX st') = size (rTYX st) \<and>
    size (rTXY st') = size (rTXY st) \<and>
    rSY st' = rSY st \<and>
    (\<exists>\<delta>hd \<delta>tl \<delta>dc.
        tail (rTYX st') + \<delta>tl = tail (rTYX st)\<and>
        head (rTXY st') + \<delta>hd = head (rTXY st)\<and>
        CleanQ_RB_list (rTXY st') =  \<delta>dc @ CleanQ_RB_list (rTXY st))" (*X adding something to ring*)

lemma frame_rb_s_w_x:
  "frame_rb_strong dev' dev \<Longrightarrow> frame_rb_weak_x dev' dev"
  by (smt Diff_empty Un_commute append_Nil2 frame_rb_strong_def 
      frame_rb_weak_x_def list.set(1) self_append_conv2 sup_bot.comm_neutral)

lemma frame_rb_s_w_y:
  "frame_rb_strong dev' dev \<Longrightarrow> frame_rb_weak_y dev' dev"
  by(simp add:frame_rb_strong_def frame_rb_weak_y_def)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>All CleanQ RB Invariants\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We combine all invariants for the abstract CleanQ RB model and define the unified 
  predicate \verb+CleanQ_RB_Invariants+.
\<close>

fun CleanQ_RB_Invariants :: "'a set \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> bool"
  where "CleanQ_RB_Invariants K rb \<longleftrightarrow> I1_rb_img rb K \<and> I2_rb_img rb \<and> I3_rb_img rb
                                       \<and> I4_rb_valid rb"


text \<open>
  Finally, we can show that when the CleanQ RB invariants are satisfied, this also
  satisfies the set invariants.
\<close>

lemma CleanQ_RB_Invariants_List_Invariants:
  "CleanQ_RB_Invariants K L \<Longrightarrow> CleanQ_List_Invariants K (CleanQ_RB2List L)"
  unfolding CleanQ_RB2List_def by simp


(*
text \<open>The list weak frame condition implies the ring buffer weak frame condition.\<close>
lemma frame_rb_weak_x_list_weak:
  fixes rb rb' K
  assumes I1: "CleanQ_RB_Invariants K rb'"
      and frame: "frame_rb_weak_x rb' rb"
    shows "frame_list_weak (lTXY (CLeanQ_RB2List rb'), lSY (CleanQ_RB2List rb'), lTYX (CleanQ_RB2List rb'), lSX (CleanQ_RB2List rb')) 
                           (lTXY (CLeanQ_RB2List rb), lSY (CleanQ_RB2List rb), lTYX (CleanQ_RB2List rb), lSX (CleanQ_RB2List rb))"
  unfolding CleanQ_RB2List_def
proof auto

  show "\<And>x. x \<in> rSX rb' \<Longrightarrow> x \<in> rSX rb" using frame by (simp add: frame_rb_weak_x_def)
  show "\<And>x. x \<in> rSX rb \<Longrightarrow> x \<in> rSX rb'" using frame by (simp add: frame_rb_weak_x_def)

    from frame obtain \<delta>hd \<delta>tl where
    dHd: "head (rTXY rb') + \<delta>hd = head (rTXY rb)" and
    dTl: "tail (rTYX rb') + \<delta>tl = tail (rTYX rb)"
      by (simp add: frame_rb_weak_x_def)


  define \<delta>txy where "\<delta>txy =  map (ring (rTXY rb')) \<delta>hd"
  define \<delta>bc where "\<delta>bc = slice (BF dev') (dn dev') (dn dev)"
  (* Somehow this does not seem to work
    from frame obtain \<delta>dc where
    dDc: "CleanQ_RB_list (rTXY rb') = \<delta>dc @ CleanQ_RB_list (rTXY rb)"  
      unfolding CleanQ_RB_list_def
  *)
    


qed
*) 
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

text \<open>
  The \verb+enqueue+ operation is analogous to the List operations except that the elements
  are written into a slot in the descriptor ring and then the pointers adapted accordingly. 
\<close>

definition CleanQ_RB_enq_x :: "'a \<Rightarrow> 'a CleanQ_RB_State  \<Rightarrow> 'a CleanQ_RB_State"
  where "CleanQ_RB_enq_x b rb = rb \<lparr> rSX := (rSX rb) - {b}, rTXY := rb_enq b (rTXY rb) \<rparr>"

definition CleanQ_RB_enq_y :: "'a \<Rightarrow> 'a CleanQ_RB_State  \<Rightarrow> 'a CleanQ_RB_State"
  where "CleanQ_RB_enq_y b rb = rb \<lparr> rSY := (rSY rb) - {b}, rTYX := rb_enq b (rTYX rb) \<rparr>"


text \<open>
  The enqueue operation cannot proceed if there is no space in the corresponding ring
  buffer.
\<close>

definition CleanQ_RB_enq_x_possible :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "CleanQ_RB_enq_x_possible rb \<longleftrightarrow> rb_can_enq (rTXY rb)"

definition CleanQ_RB_enq_y_possible :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "CleanQ_RB_enq_y_possible rb \<longleftrightarrow> rb_can_enq (rTYX rb)"


text \<open>
  Next we can show that if we can enqueue something into the bounded ring buffer, 
  the system behaves exactly like the list model, by showing the commutative 
  of the lifting function and the enqueue operation.
\<close>

lemma CleanQ_RB_enq_x_equal :
  assumes can_enq: "CleanQ_RB_enq_x_possible rb" 
      and invariants : "CleanQ_RB_Invariants K rb"
  shows "CleanQ_RB2List (CleanQ_RB_enq_x b rb) = CleanQ_List_enq_x b (CleanQ_RB2List rb)"  
  unfolding CleanQ_RB2List_def CleanQ_List_enq_x_def CleanQ_RB_enq_x_def
  using can_enq invariants  CleanQ_RB_enq_x_possible_def rb_enq_list_add
  by (auto simp add: CleanQ_RB_enq_x_possible_def rb_enq_list_add)

lemma CleanQ_RB_enq_y_equal :
  assumes can_enq: "CleanQ_RB_enq_y_possible rb" 
      and invariants : "CleanQ_RB_Invariants K rb"
  shows "CleanQ_RB2List (CleanQ_RB_enq_y b rb) = CleanQ_List_enq_y b (CleanQ_RB2List rb)"  
  unfolding CleanQ_RB2List_def CleanQ_List_enq_y_def CleanQ_RB_enq_y_def
  using can_enq invariants 
  by (simp add: CleanQ_RB_enq_y_possible_def rb_enq_list_add)


text \<open>
  We can now show where the buffer \verb+b+ ends up precisely, when we enqueue it into
  the ring buffer. A pre-requisit here, is that the buffer is owned by the agent, and
  that there is space to enqueue the buffer. We do this for X and Y separately.
\<close>

lemma CleanQ_RB_enq_x_result :
  assumes X_owned: "b \<in> rSX rb"  and  X_enq: "rb' = CleanQ_RB_enq_x b rb"
    and invariants : "CleanQ_RB_Invariants K rb"  
    and can_enq:  "CleanQ_RB_enq_x_possible rb" 
  shows  "b \<notin> rSX rb' \<and> b \<notin> rSY rb' \<and> b \<notin> set (CleanQ_RB_list (rTYX rb')) \<and>
          b \<in> set (CleanQ_RB_list (rTXY rb'))"
proof -
  from can_enq invariants X_enq have X1:
    "b \<notin> rSX rb'"
    unfolding CleanQ_RB_enq_x_def by(simp)
    
  from can_enq invariants X_enq have X2:
    "b \<notin> rSY rb'"
    using invariants X_owned unfolding CleanQ_RB_enq_x_def by auto

  from can_enq invariants X_enq have X3:
    " b \<notin> set (CleanQ_RB_list (rTYX rb'))"
    using invariants X_owned unfolding CleanQ_RB_enq_x_def by auto

    have X4:
    "b \<in> set (CleanQ_RB_list (rTXY rb'))"
     apply (subst X_enq)
      apply (simp add:CleanQ_RB_enq_x_def)
      using CleanQ_RB_enq_x_possible_def can_enq invariants rb_enq_list_add by fastforce
          
  show ?thesis
    using X1 X2 X3 X4  by(auto)
qed 


lemma CleanQ_RB_enq_y_result :
  assumes Y_owned: "b \<in> rSY rb"  and  Y_enq: "rb' = CleanQ_RB_enq_y b rb"
    and invariants : "CleanQ_RB_Invariants K rb"  
    and can_enq:  "CleanQ_RB_enq_y_possible rb" 
  shows  "b \<notin> rSX rb' \<and> b \<notin> rSY rb' \<and> b \<notin> set (CleanQ_RB_list (rTXY rb')) \<and>
          b \<in> set (CleanQ_RB_list (rTYX rb'))"
proof -
  from can_enq invariants Y_enq have X1:
    "b \<notin> rSY rb'"
    unfolding CleanQ_RB_enq_y_def by(simp)
    
  from can_enq invariants Y_enq have X2:
    "b \<notin> rSX rb'"
    using invariants Y_owned unfolding CleanQ_RB_enq_y_def by auto

  from can_enq invariants Y_enq have X3:
    " b \<notin> set (CleanQ_RB_list (rTXY rb'))"
    using invariants Y_owned unfolding CleanQ_RB_enq_y_def by auto

  have X4:
    "b \<in> set (CleanQ_RB_list (rTYX rb'))"
     apply (subst Y_enq)
      apply (simp add:CleanQ_RB_enq_y_def)
      using CleanQ_RB_enq_y_possible_def can_enq invariants rb_enq_list_add by fastforce
          
  show ?thesis
    using X1 X2 X3 X4 X4 by(auto)
qed 

text \<open>
  The two operations \verb+CleanQ_RB_enq_x+ and \verb+CleanQ_RB_enq_y+ transition
  the model state. Thus we need to prove that all invariants are preserved. We do this
  Individually first, then do the union. Note, the proofs are symmetric. 
\<close>

lemma CleanQ_RB_enq_x_I1 :
  fixes b
  assumes Inv: "CleanQ_RB_Invariants K rb"  and  X_owned: "b \<in> rSX rb" and
          can_enq: "CleanQ_RB_enq_x_possible rb" and
          X_enq: "rb' = CleanQ_RB_enq_x b rb"
    shows "I1_rb_img (rb') K"
  unfolding CleanQ_RB_enq_x_def 
  using Inv X_owned can_enq
  by (metis CleanQ_List_State.select_convs(1) CleanQ_List_enq_x_I1 CleanQ_RB2List_def 
      CleanQ_RB_Invariants.elims(2) CleanQ_RB_enq_x_equal I1_rb_img_lift X_enq)

lemma CleanQ_RB_enq_y_I1 :
  fixes b
  assumes Inv: "CleanQ_RB_Invariants K rb"  and  Y_owned: "b \<in> rSY rb" and
          can_enq: "CleanQ_RB_enq_y_possible rb" and
          Y_enq: "rb' = CleanQ_RB_enq_y b rb"
    shows "I1_rb_img (rb') K"
  unfolding CleanQ_RB_enq_y_def 
  by (metis CleanQ_List_Invariants.simps CleanQ_List_State.select_convs(2) CleanQ_List_enq_y_I1 
      CleanQ_RB2List_def CleanQ_RB_Invariants_List_Invariants CleanQ_RB_enq_y_equal I1_rb_img_lift Inv Y_enq Y_owned can_enq)

lemma CleanQ_RB_enq_x_I2 :
  assumes Inv: "CleanQ_RB_Invariants K rb"  and  X_owned: "b \<in> rSX rb" and
          X_enq: "rb' = CleanQ_RB_enq_x b rb" and
          can_enq: "CleanQ_RB_enq_x_possible rb"
    shows "I2_rb_img (rb')"
  unfolding CleanQ_RB_enq_x_def
  by (metis CleanQ_List_State.select_convs(1) CleanQ_List_enq_x_I2 CleanQ_RB2List_def 
      CleanQ_RB_Invariants.elims(2) CleanQ_RB_enq_x_equal I2_rb_img_lift Inv X_enq X_owned can_enq)

lemma CleanQ_RB_enq_y_I2 :
  assumes Inv: "CleanQ_RB_Invariants K rb"  and  Y_owned: "b \<in> rSY rb" and
          Y_enq: "rb' = CleanQ_RB_enq_y b rb" and
          can_enq: "CleanQ_RB_enq_y_possible rb"
    shows "I2_rb_img (rb')"
  unfolding CleanQ_RB_enq_y_def
  by (metis CleanQ_List_Invariants.simps CleanQ_List_State.select_convs(2) CleanQ_List_enq_y_I2 
      CleanQ_RB2List_def CleanQ_RB_Invariants_List_Invariants CleanQ_RB_enq_y_equal I2_rb_img_lift Inv Y_enq Y_owned can_enq)

lemma CleanQ_RB_enq_x_I3 :
  fixes K rb rb'
  assumes Inv: "CleanQ_RB_Invariants K rb"  and  X_owned: "b \<in> rSX rb" and
          X_enq: "rb' = CleanQ_RB_enq_x b rb" and
          can_enq: "CleanQ_RB_enq_x_possible rb"
  shows "I3_rb_img (rb')"
  using can_enq X_enq Inv
proof(auto)
  from Inv X_owned have b_before: "b \<notin> set (CleanQ_RB_list (rTXY rb))" by auto
  from X_owned Inv X_enq can_enq CleanQ_RB_enq_x_result have b_after: "b \<in> set (CleanQ_RB_list (rTXY rb'))"
    by metis
  from Inv b_before b_after have dist_before: "distinct (CleanQ_RB_list (rTXY rb))"  
    by simp
  from b_after dist_before have dist_after: "distinct (CleanQ_RB_list (rTXY rb) @ [b])"
    by (simp add: b_before)
  from can_enq Inv rb_enq_list_add have final: "CleanQ_RB_list (rTXY rb) @ [b] = CleanQ_RB_list (rb_enq b (rTXY rb))"
    by (simp add: rb_enq_list_add CleanQ_RB_enq_x_possible_def)

  show first: "distinct (CleanQ_RB_list (rTXY (CleanQ_RB_enq_x b rb)))" using Inv X_enq can_enq X_owned dist_after final rb_enq_list_add
    unfolding CleanQ_RB_enq_x_def
    by simp

  from CleanQ_RB_enq_x_result CleanQ_RB_enq_x_def X_enq have no_change: "rTYX rb = rTYX rb'"
    by (simp add: CleanQ_RB_enq_x_def)
  show "distinct (CleanQ_RB_list (rTYX (CleanQ_RB_enq_x b rb)))" using no_change
    using Inv X_enq by auto

qed

lemma CleanQ_RB_enq_y_I3 :
  fixes K rb rb'
  assumes Inv: "CleanQ_RB_Invariants K rb"  and  Y_owned: "b \<in> rSY rb" and
          Y_enq: "rb' = CleanQ_RB_enq_y b rb" and
          can_enq: "CleanQ_RB_enq_y_possible rb"
  shows "I3_rb_img (rb')"
  using can_enq Y_enq Inv
proof(auto)
  from Inv Y_owned have b_before: "b \<notin> set (CleanQ_RB_list (rTYX rb))" by auto
  from Y_owned Inv Y_enq can_enq CleanQ_RB_enq_y_result have b_after: "b \<in> set (CleanQ_RB_list (rTYX rb'))"
    by metis
  from Inv b_before b_after have dist_before: "distinct (CleanQ_RB_list (rTYX rb))"  
    by simp
  from b_after dist_before have dist_after: "distinct (CleanQ_RB_list (rTYX rb) @ [b])"
    by (simp add: b_before)
  from can_enq Inv rb_enq_list_add have final: "CleanQ_RB_list (rTYX rb) @ [b] = CleanQ_RB_list (rb_enq b (rTYX rb))"
    by (simp add: rb_enq_list_add CleanQ_RB_enq_y_possible_def)

  show first: "distinct (CleanQ_RB_list (rTYX (CleanQ_RB_enq_y b rb)))" using Inv Y_enq can_enq Y_owned dist_after final rb_enq_list_add
    unfolding CleanQ_RB_enq_y_def
    by simp

  from CleanQ_RB_enq_y_result CleanQ_RB_enq_y_def Y_enq have no_change: "rTXY rb = rTXY rb'"
    by (simp add: CleanQ_RB_enq_y_def)
  show "distinct (CleanQ_RB_list (rTXY (CleanQ_RB_enq_y b rb)))" using no_change
    using Inv Y_enq by auto

qed

lemma CleanQ_RB_enq_x_I4 :
 assumes Inv: "CleanQ_RB_Invariants K rb"  and  X_owned: "b \<in> rSX rb" and
         X_enq: "rb' = CleanQ_RB_enq_x b rb" and  can_enq: "CleanQ_RB_enq_x_possible rb"
  shows "I4_rb_valid rb'"
  apply(subst X_enq)
  using can_enq unfolding CleanQ_RB_enq_x_def CleanQ_RB_list_def CleanQ_RB_enq_x_possible_def
  using Inv by(simp add:rb_enq_remains_valid)


lemma CleanQ_RB_enq_y_I4 :
 assumes Inv: "CleanQ_RB_Invariants K rb"  and  X_owned: "b \<in> rSY rb" and
         Y_enq: "rb' = CleanQ_RB_enq_y b rb" and  can_enq: "CleanQ_RB_enq_y_possible rb"
  shows "I4_rb_valid rb'"
  apply(subst Y_enq)
  using can_enq unfolding CleanQ_RB_enq_y_def CleanQ_RB_list_def CleanQ_RB_enq_y_possible_def
  using Inv by(simp add:rb_enq_remains_valid)

lemma CleanQ_RB_enq_y_inv_all :
 assumes Inv: "CleanQ_RB_Invariants K rb"  and  Y_owned: "b \<in> rSY rb" and
         Y_enq: "rb' = CleanQ_RB_enq_y b rb" and  can_enq: "CleanQ_RB_enq_y_possible rb"
  shows "CleanQ_RB_Invariants K rb'"
  apply(subst Y_enq)
  using can_enq unfolding CleanQ_RB_enq_y_def CleanQ_RB_list_def CleanQ_RB_enq_y_possible_def
  by (metis CleanQ_RB_Invariants.elims(3) CleanQ_RB_enq_y_I1 CleanQ_RB_enq_y_I2 CleanQ_RB_enq_y_I3 
      CleanQ_RB_enq_y_I4 CleanQ_RB_enq_y_def Inv Y_owned can_enq)

lemma CleanQ_RB_enq_x_inv_all :
 assumes Inv: "CleanQ_RB_Invariants K rb"  and  X_owned: "b \<in> rSX rb" and
         X_enq: "rb' = CleanQ_RB_enq_x b rb" and  can_enq: "CleanQ_RB_enq_x_possible rb"
  shows "CleanQ_RB_Invariants K rb'"
  apply(subst X_enq)
  using can_enq unfolding CleanQ_RB_enq_x_def CleanQ_RB_list_def CleanQ_RB_enq_x_possible_def
  by (metis CleanQ_RB_Invariants.elims(3) CleanQ_RB_enq_x_I1 CleanQ_RB_enq_x_I2 
      CleanQ_RB_enq_x_I3 CleanQ_RB_enq_x_I4 CleanQ_RB_enq_x_def Inv X_owned can_enq)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  The \verb+dequeue+ operation is analogous to the List operations except that the elements
  are read from a slot in the descriptor ring and then the pointers adapted accordingly. 
\<close>

definition CleanQ_RB_deq_x :: "'a CleanQ_RB_State  \<Rightarrow> 'a CleanQ_RB_State"
  where "CleanQ_RB_deq_x rb = (let (b, rest) = rb_deq(rTYX rb) in 
                                  rb \<lparr> rSX := (rSX rb) \<union> {b}, rTYX := rest \<rparr>)"

definition CleanQ_RB_deq_y :: "'a CleanQ_RB_State  \<Rightarrow> 'a CleanQ_RB_State"
  where "CleanQ_RB_deq_y rb = (let (b, rest) = rb_deq(rTXY rb) in 
                                  rb \<lparr> rSY := (rSY rb) \<union> {b}, rTXY := rest \<rparr>)"


text \<open>
  The deqeueu operation cannot proceed if there is no element in the corresponding ring
  buffer.
\<close>

definition CleanQ_RB_deq_x_possible :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "CleanQ_RB_deq_x_possible rb \<longleftrightarrow> rb_can_deq (rTYX rb)"

definition CleanQ_RB_deq_y_possible :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "CleanQ_RB_deq_y_possible rb \<longleftrightarrow> rb_can_deq (rTXY rb)"


lemma CleanQ_RB_deq_x_equal :
  assumes can_deq: "CleanQ_RB_deq_x_possible rb" 
      and invariants : "CleanQ_RB_Invariants K rb"
  shows "CleanQ_RB2List (CleanQ_RB_deq_x rb) = CleanQ_List_deq_x (CleanQ_RB2List rb)"  
  unfolding CleanQ_RB2List_def CleanQ_RB_deq_x_def CleanQ_List_deq_x_def 
  using can_deq invariants
  by (simp add: CleanQ_RB_deq_x_possible_def prod.case_eq_if rb_deq_list_tail 
                rb_deq_list_was_head rb_valid_def)

lemma CleanQ_RB_deq_y_equal :
  assumes can_deq: "CleanQ_RB_deq_y_possible rb" 
      and invariants : "CleanQ_RB_Invariants K rb"
  shows "CleanQ_RB2List (CleanQ_RB_deq_y rb) = CleanQ_List_deq_y (CleanQ_RB2List rb)"  
  unfolding CleanQ_RB2List_def CleanQ_RB_deq_y_def CleanQ_List_deq_y_def 
  using can_deq invariants
  by (simp add: CleanQ_RB_deq_y_possible_def prod.case_eq_if rb_deq_list_tail 
                rb_deq_list_was_head rb_valid_def)

lemma CleanQ_RB_deq_x_no_change:
    assumes can_deq: "CleanQ_RB_deq_x_possible rb"  and  X_deq: "rb' = CleanQ_RB_deq_x rb"
  shows "rSY rb' = rSY rb \<and> rTXY rb' = rTXY rb"
  using can_deq X_deq unfolding CleanQ_RB_deq_x_def by (simp add: prod.case_eq_if)



lemma CleanQ_RB_deq_x_subsets :
  assumes can_deq: "CleanQ_RB_deq_x_possible rb"  and  X_deq: "rb' = CleanQ_RB_deq_x rb"
    and invariants : "CleanQ_RB_Invariants K rb" 
  shows "rSX rb \<subset> rSX rb' \<and> set (CleanQ_RB_list (rTYX rb')) \<subset> set (CleanQ_RB_list (rTYX rb))"
  apply(subst X_deq)+
  apply(simp add: CleanQ_RB_deq_x_def prod.case_eq_if)
  using can_deq invariants 
  by (metis CleanQ_RB_Invariants.elims(2) CleanQ_RB_deq_x_possible_def I2_rb_img.elims(2) 
            I3_rb_img.elims(2) I4_rb_valid.elims(2) dual_order.order_iff_strict insert_absorb 
            insert_disjoint(1) psubset_insert_iff rb_deq_list_was_in rb_deq_subset)


lemma CleanQ_RB_deq_x_result :
  assumes can_deq: "CleanQ_RB_deq_x_possible rb"  and  X_deq: "rb' = CleanQ_RB_deq_x rb"
    and invariants : "CleanQ_RB_Invariants K rb"  and buf: "b = (rb_read_tail (rTYX rb))"
  shows  "b \<in> rSX rb' \<and> b \<notin> rSY rb' \<and> b \<notin> set (CleanQ_RB_list (rTYX rb')) 
          \<and> b \<notin> set (CleanQ_RB_list (rTXY rb')) "
proof -

  have X1:"b \<in> rSX rb'"
    using buf X_deq unfolding CleanQ_RB_deq_x_def
    by(auto simp:rb_deq_def prod.case_eq_if) 

  from invariants buf have X2a:
    "b \<notin> rSY rb" 
    apply(auto simp:rb_read_tail_def)
    by (metis CleanQ_RB_deq_x_possible_def can_deq disjoint_iff_not_equal prod.sel(1) 
              rb_deq_def rb_deq_list_was_in rb_read_tail_def)

  have X2:"b \<notin> rSY rb'" 
    using invariants buf X_deq X2a unfolding CleanQ_RB_deq_x_def
    by(auto simp add:rb_deq_def rb_read_tail_def)
    

  have X3a:
    "rTYX (let (b, rest) = rb_deq (rTYX rb) in rb\<lparr>rSX := rSX rb \<union> {b}, rTYX := rest\<rparr>)
       = snd (rb_deq (rTYX rb))"
    by (simp add: prod.case_eq_if)

  have X3b:
    "b = (fst (rb_deq (rTYX rb)))"
    using buf unfolding rb_deq_def by simp

  have X3:"b \<notin> set (CleanQ_RB_list (rTYX rb'))"
    apply(simp add: X_deq CleanQ_RB_deq_x_def prod.case_eq_if)
    using can_deq invariants unfolding CleanQ_RB_deq_x_possible_def X3b
    by (simp add: rb_deq_list_not_in)

  have X4a:"b \<notin> set (CleanQ_RB_list (rTXY rb))"
    using invariants buf 
    apply(auto simp:rb_read_tail_def)
    by (metis CleanQ_RB_deq_x_possible_def buf can_deq disjoint_iff_not_equal 
              prod.sel(1) rb_deq_def rb_deq_list_was_in)

  have X4:"b \<notin> set (CleanQ_RB_list (rTXY rb'))"
     using buf X_deq can_deq X4a unfolding CleanQ_RB_deq_x_def CleanQ_RB_deq_x_possible_def
     by (metis CleanQ_List_State.ext_inject CleanQ_List_State.surjective 
               CleanQ_List_deq_x_upd CleanQ_RB2List_def CleanQ_RB_deq_x_equal  
               X_deq can_deq invariants )
    
  show ?thesis using X1 X2 X3 X4 by(simp)   
qed


lemma CleanQ_RB_deq_y_result :
  assumes can_deq: "CleanQ_RB_deq_y_possible rb"  and  Y_deq: "rb' = CleanQ_RB_deq_y rb"
    and invariants : "CleanQ_RB_Invariants K rb"  and buf: "b = rb_read_tail (rTXY rb)"
  shows  "b \<notin> rSX rb' \<and> b \<in> rSY rb' \<and> b \<notin> set (CleanQ_RB_list (rTYX rb')) 
          \<and> b \<notin> set (CleanQ_RB_list (rTXY rb')) "
proof -
  have X1:"b \<in> rSY rb'"
    using buf Y_deq unfolding CleanQ_RB_deq_y_def
    by (simp add: rb_deq_def rb_read_tail_def)
    
  have X2:"b \<notin> rSX rb'" 
    using invariants buf Y_deq unfolding CleanQ_RB_deq_y_def
    by (metis (no_types, lifting) CleanQ_List_State.ext_inject CleanQ_List_State.surjective 
              CleanQ_List_deq_y_upd CleanQ_RB2List_def CleanQ_RB_Invariants.elims(2) 
              CleanQ_RB_deq_y_possible_def CleanQ_RB_deq_y_equal I2_rb_img.elims(2) 
              I4_rb_valid.elims(2) Y_deq can_deq disjoint_iff_not_equal fstI rb_deq_def 
              rb_deq_list_was_in)
  have X3:"b \<notin> set (CleanQ_RB_list (rTXY rb'))"
    using buf Y_deq can_deq unfolding CleanQ_RB_deq_y_def CleanQ_RB_deq_y_possible_def
    apply(simp)
    by (metis CleanQ_List_State.ext_inject CleanQ_List_State.surjective 
              CleanQ_List_deq_y_upd CleanQ_RB2List_def CleanQ_RB_Invariants.elims(2) 
              CleanQ_RB_deq_y_equal I3_rb_img.elims(2) I4_rb_valid.elims(2) Y_deq can_deq 
              fstI invariants rb_deq_def rb_deq_list_not_in rb_deq_list_tail rb_valid_def)
    
  have X4:"b \<notin> set (CleanQ_RB_list (rTYX rb'))"
     using buf Y_deq can_deq unfolding CleanQ_RB_deq_y_def CleanQ_RB_deq_y_possible_def
    apply(simp)
     by (metis CleanQ_List_State.ext_inject CleanQ_List_State.surjective 
               CleanQ_List_deq_y_upd CleanQ_RB2List_def CleanQ_RB_Invariants.elims(2) 
               CleanQ_RB_deq_y_equal I2_rb_img.elims(2) I4_rb_valid.elims(2) Y_deq can_deq 
               disjoint_insert(1) fstI insert_Diff invariants rb_deq_def rb_deq_list_was_in )
    
  show ?thesis using X1 X2 X3 X4 by(simp) 
qed

lemma CleanQ_RB_deq_y_no_change:
    assumes can_deq: "CleanQ_RB_deq_y_possible rb"  and  Y_deq: "rb' = CleanQ_RB_deq_y rb"
  shows "rSX rb' = rSX rb \<and> rTYX rb' = rTYX rb"
  using can_deq Y_deq unfolding CleanQ_RB_deq_y_def by (simp add: prod.case_eq_if)



lemma CleanQ_RB_deq_y_subsets :
  assumes can_deq: "CleanQ_RB_deq_y_possible rb"  and  Y_deq: "rb' = CleanQ_RB_deq_y rb"
    and invariants : "CleanQ_RB_Invariants K rb" 
  shows "rSY rb \<subset> rSY rb' \<and> set (CleanQ_RB_list (rTXY rb')) \<subset> set (CleanQ_RB_list (rTXY rb))"
  apply(subst Y_deq)+
  apply(simp add: CleanQ_RB_deq_y_def prod.case_eq_if)
  using can_deq invariants 
  by (metis CleanQ_RB_Invariants.elims(2) CleanQ_RB_deq_y_possible_def I2_rb_img.elims(2) 
            I3_rb_img.elims(2) I4_rb_valid.elims(2) dual_order.order_iff_strict insert_absorb 
            insert_disjoint(1) psubset_insert_iff rb_deq_list_was_in rb_deq_subset)

  

(* -------------------------------------------------------------------------------------*)
subsubsection \<open>Invariants\<close>
(* -------------------------------------------------------------------------------------*)


lemma CleanQ_RB_deq_x_I1 :
  assumes can_deq: "CleanQ_RB_deq_x_possible rb"  and  X_deq: "rb' = CleanQ_RB_deq_x rb"
    and invariants : "CleanQ_RB_Invariants K rb"
  shows "I1_rb_img rb' K"
proof (simp)
  
  have X1: 
    "rSY rb' = rSY rb \<and> rTXY rb' = rTXY rb"
    using can_deq X_deq by(simp add:CleanQ_RB_deq_x_no_change)

  have X2:
    "rSX rb' \<union> set (CleanQ_RB_list (rTYX rb')) = rSX rb \<union> set (CleanQ_RB_list (rTYX rb))"
    apply(subst X_deq)+
    apply(simp add:CleanQ_RB_deq_x_def prod.case_eq_if)
    by (metis (no_types, lifting) CleanQ_RB_Invariants.elims(2) 
              CleanQ_RB_deq_x_possible_def I4_rb_valid.elims(2) Un_insert_right 
              can_deq empty_set insert_absorb insert_is_Un insert_not_empty invariants 
              list.simps(15) list_set_hd_tl_union rb_deq_list_tail rb_deq_list_was_head 
              rb_deq_list_was_in set_append rb_valid_def)

  show "rSX rb' \<union> rSY rb' \<union> set (CleanQ_RB_list (rTXY rb')) \<union> set (CleanQ_RB_list (rTYX rb')) = K"
    using X1 X2 invariants by(auto)
qed

lemma CleanQ_RB_deq_y_I1 :
  assumes can_deq: "CleanQ_RB_deq_y_possible rb"  and  Y_deq: "rb' = CleanQ_RB_deq_y rb"
    and invariants : "CleanQ_RB_Invariants K rb"
  shows "I1_rb_img rb' K"
proof (simp)
  
  have X1: 
    "rSX rb' = rSX rb \<and> rTYX rb' = rTYX rb"
    using can_deq Y_deq CleanQ_RB_deq_y_no_change by(auto)

  have X2:
    "rSY rb' \<union> set (CleanQ_RB_list (rTXY rb')) = rSY rb \<union> set (CleanQ_RB_list (rTXY rb))"
    apply(subst Y_deq)+
    apply(simp add:CleanQ_RB_deq_y_def prod.case_eq_if)
    by (metis (no_types, lifting) CleanQ_RB_Invariants.elims(2) 
              CleanQ_RB_deq_y_possible_def I4_rb_valid.elims(2) Un_insert_right 
              can_deq empty_set insert_absorb insert_is_Un insert_not_empty invariants 
              list.simps(15) list_set_hd_tl_union rb_deq_list_tail rb_deq_list_was_head 
              rb_deq_list_was_in set_append rb_valid_def)

  show "rSX rb' \<union> rSY rb' \<union> set (CleanQ_RB_list (rTXY rb')) \<union> set (CleanQ_RB_list (rTYX rb')) = K"
    using X1 X2 invariants by(auto)
qed



lemma CleanQ_RB_deq_x_I2 :
  assumes can_deq: "CleanQ_RB_deq_x_possible rb"  and  X_deq: "rb' = CleanQ_RB_deq_x rb"
    and invariants : "CleanQ_RB_Invariants K rb"
  shows "I2_rb_img rb'"
proof -
  have X1:
    "rSX rb' \<inter> rSY rb' = {}"
    apply(subst X_deq)+
    apply(simp add:CleanQ_RB_deq_x_def prod.case_eq_if) 
     using invariants
     by (metis CleanQ_RB_Invariants.elims(2) CleanQ_RB_deq_x_possible_def 
                I2_rb_img.elims(2) I4_rb_valid.elims(2) IntI can_deq empty_iff 
                rb_deq_list_was_in)
  (* ok that one should be rephrased... *)
  have X2: "rSX rb' \<inter> set (CleanQ_RB_list (rTXY rb')) = {}"
    apply(subst X_deq)+
    apply(simp add:CleanQ_RB_deq_x_def prod.case_eq_if)
    using can_deq invariants
    by (metis CleanQ_RB_Invariants.elims(2) CleanQ_RB_deq_x_possible_def 
              I2_rb_img.elims(2) I4_rb_valid.elims(2) insert_Diff insert_disjoint(1) 
              rb_deq_list_was_in)

  (* ok that one should be rephrased... *)
  have X3: "rSX rb' \<inter> set (CleanQ_RB_list (rTYX rb')) = {}"
    apply(subst X_deq)+
    apply(simp add:CleanQ_RB_deq_x_def prod.case_eq_if)
    using can_deq invariants
    by (smt CleanQ_RB_Invariants.elims(2) CleanQ_RB_deq_x_possible_def I2_rb_img.elims(2) 
            I3_rb_img.elims(2) I4_rb_valid.elims(2) Int_commute Int_iff empty_set insert_Diff 
            insert_disjoint(1) list_set_hd_tl_subtract rb_deq_list_not_in rb_deq_list_tail 
            rb_deq_list_was_head rb_deq_list_was_in rb_valid_def)

  have X4: "rSY rb' \<inter> set (CleanQ_RB_list (rTXY rb')) = {}" 
    using can_deq X_deq invariants CleanQ_RB_deq_x_no_change
    by (metis CleanQ_RB_Invariants.elims(2) I2_rb_img.elims(2))

  have X5: "rSY rb' \<inter> set (CleanQ_RB_list (rTYX rb')) = {}"
    using can_deq X_deq invariants CleanQ_RB_deq_x_no_change CleanQ_RB_deq_x_subsets
    by (metis (no_types, lifting) CleanQ_RB_Invariants.elims(2) I2_rb_img.elims(2) 
              inf.strict_order_iff inf_bot_right inf_left_commute)
   
  have X6: "set (CleanQ_RB_list (rTXY rb')) \<inter> set (CleanQ_RB_list (rTYX rb')) = {}"
    using can_deq X_deq invariants CleanQ_RB_deq_x_no_change CleanQ_RB_deq_x_subsets
    by (metis (no_types, lifting) CleanQ_RB_Invariants.elims(2) I2_rb_img.elims(2) 
              inf.strict_order_iff inf_bot_right inf_left_commute)

  from X1 X2 X3 X4 X5 X6  show "I2_rb_img rb'"
    by(auto)
qed

lemma CleanQ_RB_deq_y_I2 :
  assumes can_deq: "CleanQ_RB_deq_y_possible rb"  and  Y_deq: "rb' = CleanQ_RB_deq_y rb"
    and invariants : "CleanQ_RB_Invariants K rb"
  shows "I2_rb_img rb'"
proof -
  have X1:
    "rSX rb' \<inter> rSY rb' = {}"
    apply(subst Y_deq)+
    apply(simp add:CleanQ_RB_deq_y_def prod.case_eq_if) 
     using invariants
     by (metis CleanQ_RB_Invariants.elims(2) CleanQ_RB_deq_y_possible_def 
                I2_rb_img.elims(2) I4_rb_valid.elims(2) IntI can_deq empty_iff 
                rb_deq_list_was_in)

  (* ok that one should be rephrased... *)
  have X2: "rSX rb' \<inter> set (CleanQ_RB_list (rTXY rb')) = {}"
    apply(subst Y_deq)+
    apply(simp add:CleanQ_RB_deq_y_def prod.case_eq_if)
    using can_deq invariants
    by (smt CleanQ_RB_Invariants.elims(2) CleanQ_RB_deq_y_possible_def 
        I2_rb_img.elims(2) I3_rb_img.elims(2) I4_rb_valid.elims(2) disjoint_iff_not_equal
        psubsetD rb_deq_subset)

  (* ok that one should be rephrased... *)
  have X3: "rSX rb' \<inter> set (CleanQ_RB_list (rTYX rb')) = {}"
    using can_deq invariants CleanQ_RB_deq_y_no_change
    by (metis CleanQ_RB_Invariants.elims(2) I2_rb_img.elims(2) Y_deq)

  have X4: "rSY rb' \<inter> set (CleanQ_RB_list (rTYX rb')) = {}"
    apply(subst Y_deq)+
    apply(simp add:CleanQ_RB_deq_y_def prod.case_eq_if)
    using can_deq invariants
    by (metis CleanQ_RB_Invariants.elims(2) CleanQ_RB_deq_y_possible_def I2_rb_img.elims(2) 
        I4_rb_valid.elims(2) disjoint_insert(1) insert_Diff rb_deq_list_was_in)

  have X5: "rSY rb' \<inter> set (CleanQ_RB_list (rTXY rb')) = {}" 
    apply(subst Y_deq)+
    apply(simp add:CleanQ_RB_deq_y_def prod.case_eq_if)
    using can_deq invariants
    by (smt CleanQ_RB_Invariants.elims(2) CleanQ_RB_deq_y_possible_def I2_rb_img.elims(2) 
            I3_rb_img.elims(2) I4_rb_valid.elims(2) Int_commute Int_iff empty_set insert_Diff 
            insert_disjoint(1) list_set_hd_tl_subtract rb_deq_list_not_in rb_deq_list_tail 
            rb_deq_list_was_head rb_deq_list_was_in rb_valid_def)


  have X6: "set (CleanQ_RB_list (rTXY rb')) \<inter> set (CleanQ_RB_list (rTYX rb')) = {}"
    using can_deq Y_deq invariants CleanQ_RB_deq_y_no_change CleanQ_RB_deq_y_subsets
    by (smt CleanQ_RB_Invariants.elims(2) I2_rb_img.elims(2) disjoint_iff_not_equal psubsetD)

  from X1 X2 X3 X4 X5 X6  show "I2_rb_img rb'"
    by(auto)
qed


lemma CleanQ_RB_deq_x_I3 :
  assumes can_deq: "CleanQ_RB_deq_x_possible rb"  and  X_deq: "rb' = CleanQ_RB_deq_x rb"
    and invariants : "CleanQ_RB_Invariants K rb"
  shows "I3_rb_img rb'"
  using can_deq X_deq invariants
  by (metis CleanQ_List_deq_x_I3 CleanQ_RB_Invariants.elims(2)
            CleanQ_RB_deq_x_equal I3_rb_img_lift)

lemma CleanQ_RB_deq_y_I3 :
  assumes can_deq: "CleanQ_RB_deq_y_possible rb"  and  Y_deq: "rb' = CleanQ_RB_deq_y rb"
    and invariants : "CleanQ_RB_Invariants K rb"
  shows "I3_rb_img rb'"
  using can_deq Y_deq invariants
  by (metis CleanQ_List_deq_y_I3 CleanQ_RB_Invariants.elims(2)
            CleanQ_RB_deq_y_equal I3_rb_img_lift)

lemma CleanQ_RB_deq_x_I4 :
  assumes can_deq: "CleanQ_RB_deq_x_possible rb"  and  X_deq: "rb' = CleanQ_RB_deq_x rb"
    and invariants : "CleanQ_RB_Invariants K rb"
  shows "I4_rb_valid rb'"
  apply(subst X_deq)
  unfolding CleanQ_RB_deq_x_def CleanQ_RB_deq_x_possible_def 
  using can_deq invariants
  by(simp add: CleanQ_RB_deq_x_possible_def rb_deq_remains_valid prod.case_eq_if) 

lemma CleanQ_RB_deq_y_I4 :
  assumes can_deq: "CleanQ_RB_deq_y_possible rb"  and  Y_deq: "rb' = CleanQ_RB_deq_y rb"
    and invariants : "CleanQ_RB_Invariants K rb"
  shows "I4_rb_valid rb'"
  apply(subst Y_deq)
  unfolding CleanQ_RB_deq_y_def CleanQ_RB_deq_y_possible_def 
  using can_deq invariants
  by(simp add: CleanQ_RB_deq_y_possible_def rb_deq_remains_valid prod.case_eq_if) 

lemma CleanQ_RB_deq_x_all_inv :
  assumes can_deq: "CleanQ_RB_deq_x_possible rb"  and  X_deq: "rb' = CleanQ_RB_deq_x rb"
    and invariants : "CleanQ_RB_Invariants K rb"
  shows "CleanQ_RB_Invariants K rb'"
  apply(subst X_deq)
  unfolding CleanQ_RB_deq_x_possible_def
  using can_deq invariants CleanQ_RB_deq_x_I4 CleanQ_RB_deq_x_I3 CleanQ_RB_deq_x_I2 CleanQ_RB_deq_x_I1
  unfolding CleanQ_RB_deq_x_def
  by (metis CleanQ_RB_Invariants.elims(3))

lemma CleanQ_RB_deq_y_all_inv :
  assumes can_deq: "CleanQ_RB_deq_y_possible rb"  and  Y_deq: "rb' = CleanQ_RB_deq_y rb"
    and invariants : "CleanQ_RB_Invariants K rb"
  shows "CleanQ_RB_Invariants K rb'"
  apply(subst Y_deq)
  unfolding CleanQ_RB_deq_y_possible_def
  using can_deq invariants CleanQ_RB_deq_y_I4 CleanQ_RB_deq_y_I3 CleanQ_RB_deq_y_I2 CleanQ_RB_deq_y_I1
  unfolding CleanQ_RB_deq_y_def
  by (metis CleanQ_RB_Invariants.elims(3))

(* ==================================================================================== *)
subsection \<open>Pre- and post- conditions\<close>
(* ==================================================================================== *)


definition CleanQ_RB_enq_x_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_RB_State, 'a CleanQ_RB_State) Semantic.xstate set"
  where "CleanQ_RB_enq_x_pre K b =  Semantic.Normal ` {rb. CleanQ_RB_Invariants K rb \<and> CleanQ_RB_enq_x_possible rb \<and> b \<in> rSX rb }"

definition CleanQ_RB_enq_y_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_RB_State, 'a CleanQ_RB_State) Semantic.xstate set"
  where "CleanQ_RB_enq_y_pre K b = Semantic.Normal ` {rb. CleanQ_RB_Invariants K rb \<and> CleanQ_RB_enq_y_possible rb \<and> b \<in> rSY rb}"

definition CleanQ_RB_deq_x_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_RB_State, 'a CleanQ_RB_State) Semantic.xstate set"        
  where "CleanQ_RB_deq_x_pre K buf = Semantic.Normal ` {rb. CleanQ_RB_Invariants K rb \<and> CleanQ_RB_deq_x_possible rb \<and>
                                                        buf = rb_read_tail (rTYX rb)}"
definition CleanQ_RB_deq_y_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_RB_State, 'a CleanQ_RB_State) Semantic.xstate set"        
  where "CleanQ_RB_deq_y_pre K buf = Semantic.Normal ` {rb. CleanQ_RB_Invariants K rb \<and> CleanQ_RB_deq_y_possible rb \<and>
                                                        buf = rb_read_tail (rTXY rb)}"


  
end 

(*

text \<open>
  The third refinement is trying to get as close to the C implementation as possible.
  The two transfer queues are modeled as \verb+CleanQ_RB+. Two of these are combined
  to a \verb+CleanQ_QP+ which consists of an RX and TX queue. The full state of the
  system is compromised of two queue pairs and modeled in the \verb+CleanQ_RB_State+
  recrod. Ther are two queue pairs; one for the client and the other one for the server.
  The TX queue ring buffer of the client is the RX queue ring buffer of the server and 
  the RX queue ring buffer of the client is the TX queue ring buffer of the sever. While
  these are the same, each of these queue records has their own position in the ring buffer.
  In total there are 4 position pointers in to the two Ring buffers. The SX and TX
  sets are still the same as in the abstract model since we can not make any statement
  about the sets owned by each of the sides. 
\<close>

definition dir_rx :: nat
  where "dir_rx = 1"

definition dir_tx :: nat
  where "dir_tx = 2"

text \<open>Single queue. corresponds to \verb+ffq_queue+.\<close>
record 'a CleanQ_RB =
  ring :: "nat \<Rightarrow> 'a"
  pos :: nat
  direction :: nat
  size :: nat

text \<open>A queue pair. corresponds to \verb+ffq_qp+.\<close>
record 'a CleanQ_QP =
  rx :: "'a CleanQ_RB"
  tx :: "'a CleanQ_RB"

text \<open>The full state. corresponds to the whole program state.\<close>
record 'a CleanQ_RB_State =
  qTXY :: "'a CleanQ_QP"
  qTYX :: "'a CleanQ_QP"
  SX :: "'a set"
  SY :: "'a set"


(* Need modular intervals to specify ring buffer properties *)
(*<*)
locale modulus = nonzero_modulus +
  assumes fixN: "N = 64"
begin
(*>*)
(* ==================================================================================== *)
subsection \<open>CleanQ Abstract Ring Buffer Model Invariants\<close>
(* ==================================================================================== *)

text \<open>Helper definitions to define invariants.\<close>
text \<open>Get a list of all the entries between two positions in the ring buffer. We extract
      an interval from a to b in a ring buffer i.e. if we want to extract from entry 5 to 
      1 in a ring of size 6, this will return the entries 5,6, and 1. \<close>
definition slice :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
  where "slice buf s e = [buf ((s+i) mod N). i <- [0..< e \<ominus> s]]"

text \<open>Get a list of the entries fro the XY direction.\<close>
definition slice_xy :: "'a CleanQ_RB_State \<Rightarrow> 'a list"
  where "slice_xy st = slice (ring (tx (qTXY st))) (pos (rx (qTYX st))) (pos (tx (qTXY st)))"

text \<open>Get a list of the entries fro the YX direction.\<close>
definition slice_yx :: "'a CleanQ_RB_State \<Rightarrow> 'a list"
  where "slice_yx st = slice (ring (tx (qTYX st))) (pos (rx (qTXY st))) (pos (tx (qTYX st)))"

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Images of the previously defined invariants\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>Definition of I1 on the Ring buffer model: The union of all sets is constant.\<close>
fun I1_img :: "'a CleanQ_RB_State \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1_img rb K \<longleftrightarrow> ((SX rb) \<union> (SY rb) \<union> (set (slice_xy rb)) \<union> (set (slice_yx rb))) = K"

text \<open>Definition of I2 on the Ring buffer model: No Double Presenc.\<close>
fun I2_img :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I2_img rb \<longleftrightarrow>
    SX rb \<inter> SY rb = {} \<and> SX rb \<inter> set (slice_xy rb) = {} \<and> SX rb \<inter> set (slice_yx rb) = {} \<and> 
    SY rb \<inter> set (slice_xy rb) = {} \<and> SY rb \<inter> set (slice_yx rb) = {} \<and> 
    set (slice_xy rb) \<inter> set (slice_yx rb) = {}"

text \<open>Definition of I3 on the Ring buffer model: No duplicates in list.\<close>
fun I3_img :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I3_img rb \<longleftrightarrow> distinct ((slice_xy rb) @ (slice_yx rb))"


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I4: The ring buffers are the same\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  In order for the model to work with the C code, there needs to be shared state
  similar to the C code. For an IPC queue there are normally two shared memory
  regions which are used as ring buffers. In this proof the client TX ring buffer
  is the same as the server RX ring buffer and the server TX ring buffer is the
  same as the client RX ring buffer.
\<close>
fun I4 :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I4 st \<longleftrightarrow> (ring (tx (qTXY st))) = (ring (rx (qTYX st))) \<and>
                   (ring (tx (qTYX st))) = (ring (rx (qTXY st)))"

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I5: Ring buffers are in a valid state\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  A queue pair is in a valid state if the RX and TX queues have the right direction,
  The sizes of the ring buffers are fixed to some N and the position pointers are
  less than that N. This needs to be true for both queue pairs in \verb+CleanQ_RB_State+. 
\<close>
fun I5 :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I5 st \<longleftrightarrow> (direction (tx (qTXY st))) = dir_tx \<and>
                   (direction (tx (qTYX st))) = dir_tx \<and>
                   (direction (rx (qTXY st))) = dir_rx \<and>
                   (direction (rx (qTYX st))) = dir_rx \<and>
                   size (tx (qTYX st)) = N \<and>
                   size (tx (qTXY st)) = N \<and>
                   size (rx (qTYX st)) = N \<and>
                   size (rx (qTXY st)) = N \<and>
                   pos (tx (qTYX st)) < N \<and>
                   pos (tx (qTXY st)) < N \<and>
                   pos (rx (qTYX st)) < N \<and>
                   pos (rx (qTXY st)) < N "

(*Don't think there is an ordering invariant since there are only 2 pointers into the ring buffer *)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>CleanQ List Invariants\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We combine all invariants for the abstract CleanQ list model and define the predicate 
  \verb+CleanQ_List_Invariants+.
\<close>

fun CleanQ_RB_Invariants :: "'a set \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> bool"
  where "CleanQ_RB_Invariants K rb \<longleftrightarrow> I1_img rb K \<and> I2_img rb \<and> I3_img rb \<and> I4 rb \<and> I5 rb"


end (*Modulus end *)

end

*)