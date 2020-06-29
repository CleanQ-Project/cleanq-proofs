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
(*<*) imports  
    CleanQ_ListModel
    CleanQ_ModularIntervals
begin
(*>*)

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
subsubsection \<open>Bounded Descriptor Ring\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We first define the type of a the bounded, circular descriptor ring, which we call
  ring buffer (RB). A ring buffer has a well-defined size, or number of slots, which
  defines the amount of elements it can hold.  We define the ring buffer as a function
  from nat to the element. Head and tail define the valid elements in the ring.\<close>

record 'a CleanQ_RB =
  ring :: "nat \<Rightarrow> 'a"
  head :: nat
  tail :: nat
  size :: nat

text \<open>
  A ring buffer is valid if its head and tail pointers are within the size of the buffer,
  and the buffer needs a certain size. 
\<close>

definition rb_valid :: "'a CleanQ_RB \<Rightarrow> bool"
  where "rb_valid rb \<longleftrightarrow> (head rb < size rb) \<and> (tail rb < size rb) \<and> (size rb > 1)"


(*

This needs to get a proof to talk about the valid entries using modular intervals

definition rb_valid_entries :: "'a CleanQ_RB \<Rightarrow> nat list"
  where "rb_valid_entries rb = (nonzero_modulus.list_between 
                                       (size rb) (tail rb) (head rb))"

lemma 
  assumes sz: "size rb > 1" and  hh: "head rb < size rb" and ll: "tail rb < size rb"
  shows "rb_valid_entries rb = (if (tail rb) \<le> (head rb) then [(tail rb) ..< (head rb)]
                                else [0..<(head rb)] @ [(tail rb)..< (size rb)])"
proof(cases)
  assume norm: "(tail rb) \<le> (head rb)"
  then show ?thesis
  proof -
    have X1: "rb_valid_entries rb = [tail rb..<head rb]"
      sorry
    with norm X1 show ?thesis by(auto)
  qed
next
  assume norm: "\<not>(tail rb) \<le> (head rb)"
  then show ?thesis 
  proof -
    have X1: "rb_valid_entries rb = [0..<head rb] @ [tail rb..<size rb]"
      sorry
    with norm X1 show ?thesis by(auto)
  qed
qed

*)


text \<open>
  We say a queue is full, if the enqueue operation would lead to the case
  where the head pointer == tail pointer.
\<close>

definition rb_full :: "'a CleanQ_RB \<Rightarrow> bool"
  where "rb_full rb = ((((head rb) + 1) mod (size rb)) = (tail rb))"

definition rb_empty :: "'a CleanQ_RB \<Rightarrow> bool"
  where "rb_empty rb = ((head rb) = (tail rb))"


text \<open>
  A ringbuffer has a certain set of valid entries. We now provide definitions to 
  create the list of entries. Note, this is not [(tail rb) ..<(head rb)]. As there
  might be a wrap around (e.g. head = 4 tail = 8). We use the nonzero modulus
  locale to work out the elements.

  Using the head and tail pointer we can now define the list of valid entries of the 
  ring. We do this by a case distinction if head <= tail or the other way round.
\<close>

definition rb_valid_entries :: "'a CleanQ_RB \<Rightarrow> nat list"
  where "rb_valid_entries rb = (if (tail rb) \<le> (head rb) then [(tail rb) ..< (head rb)]
                                else [(tail rb)..< (size rb)] @ [0..<(head rb)])"


text \<open>
  We can now define lemmas to talk about the head and tail entries, and whether
  they are part of the valid entries.
\<close>

lemma rb_valid_entries_head :
  "(head rb) \<notin> set (rb_valid_entries rb)"
  unfolding rb_valid_entries_def by(auto)

lemma rb_valid_entries_tail1 :
  "head rb = tail rb \<Longrightarrow> (tail rb) \<notin> set (rb_valid_entries rb)"
  unfolding rb_valid_entries_def by(simp)

lemma rb_valid_entries_tail2 :
  "rb_valid rb \<Longrightarrow> head rb \<noteq> tail rb \<Longrightarrow> (tail rb) : set (rb_valid_entries rb)"
  unfolding rb_valid_entries_def rb_valid_def by(simp)

text \<open>
  Using the valid entries, we can define the buffer elements in the descriptor ring
  by mapping them onto the ring-function of the CleanQ RB:
\<close>

definition CleanQ_RB_list :: "'a CleanQ_RB \<Rightarrow> 'a list"
  where "CleanQ_RB_list rb = map (ring rb) (rb_valid_entries rb)"

text \<open>
  If the ring is valid, then the list is bounded by the size of the ring.
\<close>

lemma rb_valid_list_size:
  "rb_valid rb \<Longrightarrow> (length (CleanQ_RB_list rb) < size rb)"
  unfolding CleanQ_RB_list_def rb_valid_entries_def rb_valid_def
  by auto


text \<open>
 We can now show that the list of valid entries is empty, when the predicate 
 \verb+rb_empty+ is true.
\<close>

lemma 
  assumes valid: "rb_valid rb"
  shows "rb_empty rb \<longleftrightarrow> rb_valid_entries rb = []"
  using valid unfolding  rb_valid_entries_def rb_valid_def 
  by (metis Nil_is_append_conv  nat_less_le order.order_iff_strict
            rb_empty_def upt_eq_Cons_conv upt_rec)








(*
old proof using the modulo

proof
  show "rb_empty rb \<Longrightarrow> rb_valid_entries rb = []"
  proof -
    assume e: "rb_empty rb"
    from e have eq:  "((head rb) = (tail rb))"
      unfolding rb_empty_def by(simp)

    from sz have nz:
      "nonzero_modulus (size rb)"
      by (simp add: nonzero_modulus.intro)

    from eq nz have el:  
      "(nonzero_modulus.list_between (size rb) (tail rb) (head rb)) = []"
       using nonzero_modulus.uptol_eq[where N="size rb" and l="tail rb" and h="head rb"]
       by(auto)

    from el show ?thesis  
      unfolding rb_valid_entries_def by(simp)
  qed
next
  show "rb_valid_entries rb = [] \<Longrightarrow> rb_empty rb"
  proof - 
    assume e: "rb_valid_entries rb = []"

    from sz have nz:
      "nonzero_modulus (size rb)"
      by (simp add: nonzero_modulus.intro)    

    from e sz nz have eq:
      "(tail rb) = (head rb)"
      unfolding rb_valid_entries_def 
      using hh ll  nonzero_modulus.uptol_eq_both[where N="size rb" and l="tail rb" and h="head rb"]
      by(auto)

    from eq show ?thesis 
      unfolding rb_empty_def by(auto)
  qed
qed
*)


text \<open>
  We provide functions that increment the head and tail pointers of the queue.
\<close>

definition rb_incr_head :: "'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB"
  where "rb_incr_head rb = rb \<lparr> head := ((head rb) + 1) mod (size rb) \<rparr>"

definition rb_incr_tail :: "'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB"
  where "rb_incr_tail rb = rb \<lparr> tail := ((tail rb) + 1) mod (size rb) \<rparr>"

text \<open>
  The two functions that increment the head or tail either remove or add an entry to the
  list of valid entries:
\<close>

lemma rb_incr_tail_valid_entries:
assumes notempty: "\<not> rb_empty rb" and  valid: "rb_valid rb" 
  shows "rb_valid_entries rb = (tail rb) # rb_valid_entries (rb_incr_tail rb)"
  using notempty valid
  unfolding rb_valid_entries_def rb_incr_tail_def rb_empty_def rb_valid_def
  by (simp add: mod_Suc  upt_conv_Cons) 

lemma rb_incr_tail_valid_entries_tail:
  assumes notempty: "\<not> rb_empty rb" and  valid: "rb_valid rb"  
  shows "rb_valid_entries (rb_incr_tail rb) = tl (rb_valid_entries rb)"
  using  valid notempty by (simp add:rb_incr_tail_valid_entries)

lemma rb_incr_head_valid_entries:
assumes notfull: "\<not> rb_full rb" and  valid: "rb_valid rb"  
  shows "(rb_valid_entries rb) @ [(head rb)] = rb_valid_entries (rb_incr_head rb)"
  using notfull valid 
  unfolding rb_valid_entries_def rb_incr_head_def rb_full_def rb_valid_def
  apply(simp add: mod_Suc upt_Suc_append  upt_conv_Cons, auto)
  by (metis le_imp_less_Suc upt_Suc_append upt_rec)
  
lemma rb_incr_head_valid_entries_butlast:
assumes notfull: "\<not> rb_full rb" and  valid: "rb_valid rb"  
shows "(rb_valid_entries rb) = butlast (rb_valid_entries (rb_incr_head rb))"
   using  notfull valid by (metis butlast_snoc rb_incr_head_valid_entries)

text \<open>
  And finally, the incrementing the head or tail does not change the contents of 
  the ring. 
\<close>

lemma rb_incr_head_ring: 
  "(ring (rb_incr_head rb)) = ring rb"
  unfolding rb_incr_head_def by(auto)

lemma rb_incr_tail_ring: 
  "(ring (rb_incr_tail rb)) = ring rb"
  unfolding rb_incr_tail_def by(auto)


text \<open>
  Writing an entry into the ring buffer then corresponds to a function update. 
\<close>

definition rb_write :: "'a \<Rightarrow> 'a CleanQ_RB \<Rightarrow>'a CleanQ_RB"
  where "rb_write b rb = rb \<lparr> ring := (ring rb)((head rb) := b) \<rparr>"


text \<open>
  we can define functions to read the entries of the ring buffer:
\<close>

definition rb_read :: "nat \<Rightarrow> 'a CleanQ_RB \<Rightarrow> 'a"
  where "rb_read i rb = (ring rb) i"

definition rb_read_tail :: "'a CleanQ_RB \<Rightarrow> 'a"
  where "rb_read_tail rb = rb_read (tail rb) rb"


text \<open>
  Writing an entry preserves the list of valid entries as well as the validity of
  the ring buffer. 
\<close>
lemma rb_write_perserves_valid_entries:
  "rb_valid_entries rb = rb_valid_entries (rb_write b rb)"
  unfolding rb_write_def rb_valid_entries_def by(auto)

lemma rb_write_preserves_valid:
  "rb_valid rb \<Longrightarrow> rb_valid (rb_write b rb)"
  unfolding rb_valid_def rb_write_def by(auto)


text \<open>
  The enqueue operation is then the combination of the update and the increment
  of the head.
\<close>

definition rb_enq :: "'a \<Rightarrow> 'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB" 
  where "rb_enq b rb = rb_incr_head (rb_write b rb)"


text \<open>
  This produces the following updates to the structure:
\<close>

definition rb_enq_alt :: "'a \<Rightarrow> 'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB" 
  where "rb_enq_alt b rb = rb \<lparr> ring := (ring rb)((head rb) := b),
                                head := ((head rb) + 1) mod (size rb) \<rparr>"

lemma rb_enq_equiv:
  "rb_enq b rb = rb_enq_alt b rb"
  unfolding rb_enq_alt_def rb_enq_def rb_incr_head_def rb_write_def by(auto)


lemma rb_enq_remains_valid:
  assumes notfull: "\<not>rb_full rb" and  valid: "rb_valid rb"
  shows "rb_valid (rb_enq b rb)"
  using valid notfull unfolding rb_valid_def rb_enq_def rb_full_def rb_incr_head_def rb_write_def
  by(auto)

text \<open>
  
\<close>

definition rb_can_enq :: "'a CleanQ_RB \<Rightarrow> bool"
  where "rb_can_enq rb \<longleftrightarrow> \<not>(rb_full rb)"

lemma rb_enq_buf_ring :
  assumes notfull: "\<not> rb_full rb" and valid: "rb_valid rb" 
  shows "rb' = rb_enq b rb \<Longrightarrow> (ring (rb'))((head rb)) = b"
  unfolding rb_enq_def rb_incr_head_def rb_write_def by(auto)

lemma rb_enq_buf:
  assumes notfull: "\<not> rb_full rb" and valid: "rb_valid rb" 
  shows "rb' = rb_enq b rb \<Longrightarrow> rb_read (head rb) rb' = b"
  by (simp add: rb_enq_alt_def rb_enq_equiv rb_read_def)
  
  


text \<open>
  Doing the enqueue operation then behaves as adding the buffer to the end
  of the list.
\<close>

lemma rb_enq_valid_entries_incr_head:
assumes notfull: "\<not> rb_full rb" and valid: "rb_valid rb"  
shows "rb_valid_entries (rb_enq b rb) =  rb_valid_entries (rb_incr_head rb)"
  using notfull valid rb_write_perserves_valid_entries unfolding rb_enq_def
  by (metis rb_full_def rb_incr_head_valid_entries rb_write_def rb_write_preserves_valid 
            select_convs(2) select_convs(3) select_convs(4) surjective update_convs(1))


lemma rb_enq_valid_entries :
assumes notfull: "\<not> rb_full rb" and valid: "rb_valid rb"   
shows "rb_valid_entries (rb) @ [(head rb)] = rb_valid_entries (rb_enq b rb)"
  using notfull valid rb_write_perserves_valid_entries rb_enq_valid_entries_incr_head
  by (simp add: rb_enq_valid_entries_incr_head rb_incr_head_valid_entries)


lemma rb_enq_preserves_valid_entries:
  assumes notfull: "\<not> rb_full rb"  and valid: "rb_valid rb"   
  shows "\<forall>i \<in> set(rb_valid_entries rb). (ring (rb_enq b rb)) i = (ring rb) i"
proof -
  have X1: "\<And>i. (ring (rb_enq b rb)) i = ring (rb_incr_head (rb_write b rb)) i"
    unfolding rb_enq_def by(auto)
  have X2: "\<And>i. ring (rb_incr_head (rb_write b rb)) i =  ring (rb_write b rb) i"
    using rb_incr_head_ring by metis
  have X3: "(\<forall>i \<in> set(rb_valid_entries rb). (ring (rb_enq b rb)) i = (ring rb) i) 
               = (\<forall>i \<in> set(rb_valid_entries rb). (ring (rb_write b rb) i = (ring rb) i))"
    using X1 X2 by(auto)
      
  show ?thesis
    using X3 notfull valid 
    by (simp add: rb_valid_entries_head rb_write_def)
qed

lemma rb_enq_perserves_old_entries:
  assumes notfull: "\<not> rb_full rb"and valid: "rb_valid rb"   
  shows "(map (ring (rb_enq b rb)) (rb_valid_entries rb))
           = (map (ring rb) (rb_valid_entries rb))"
  using notfull valid
  by (simp add: rb_enq_preserves_valid_entries)


lemma rb_enq_list_add:
assumes notfull: "\<not> rb_full rb" and valid: "rb_valid rb"   
shows "CleanQ_RB_list(rb_enq b rb) = (CleanQ_RB_list rb) @ [b]"
proof -  
  have X0: "rb_valid_entries (rb_enq b rb) = rb_valid_entries (rb) @ [(head rb)]"
    using valid notfull rb_enq_valid_entries by fastforce

  have X1:
    "CleanQ_RB_list(rb_enq b rb) = map (ring (rb_enq b rb)) (rb_valid_entries (rb_enq b rb))"
    unfolding CleanQ_RB_list_def by simp

  have X2: "... =  map (ring (rb_enq b rb)) (rb_valid_entries (rb) @ [(head rb)])"
    by (simp add: X0)
  have X3: "... =  map (ring (rb_enq b rb)) (rb_valid_entries (rb)) @ map (ring (rb_enq b rb)) ([head rb])"
    by(auto)
  have X4: "... =  map (ring (rb_enq b rb)) (rb_valid_entries (rb)) @ [(ring (rb_enq b rb)) (head rb)]"
    by(auto)
  have X5: "... = map (ring rb) (rb_valid_entries (rb)) @ [(ring (rb_enq b rb)) (head rb)]"
    using notfull valid rb_enq_perserves_old_entries by(simp)

  have X6: "(ring (rb_enq b rb)) (head rb) = b"
    using notfull valid  by (simp add: rb_enq_buf_ring)

  have X7 : "(CleanQ_RB_list rb) = map (ring rb) (rb_valid_entries (rb))"
    unfolding CleanQ_RB_list_def by simp

  show ?thesis 
    using X1 X2 X3 X4 X5 X6 X7 by(auto)               
qed

text \<open>
 TODO: how is this best expressed ??
\<close>
definition rb_deq :: "'a CleanQ_RB \<Rightarrow> ('a \<times> 'a CleanQ_RB)"
  where "rb_deq rb = ((ring rb) (tail rb),  
                      rb \<lparr> tail := ((tail rb) + 1) mod (size rb) \<rparr> )"


lemma rb_deq_remains_valid:
  assumes notempty: "\<not>rb_empty rb" and  valid: "rb_valid rb"
  shows "rb_valid (snd (rb_deq rb))"
  using valid notempty unfolding rb_valid_def rb_deq_def
  by(simp)

lemma rb_deq_list_was_head :
  assumes notempty: "\<not>rb_empty rb" and  valid: "rb_valid rb"  
     and res: "rb' = rb_deq rb" 
   shows "(fst rb') = hd (CleanQ_RB_list rb)"
  using res notempty valid unfolding rb_deq_def CleanQ_RB_list_def 
  by (simp add: rb_incr_tail_valid_entries)

lemma rb_deq_list_was_in :
  assumes notempty: "\<not>rb_empty rb" and  valid: "rb_valid rb"  
     and res: "rb' = rb_deq rb" 
   shows "(fst rb') \<in> set (CleanQ_RB_list rb)"
  using res notempty valid unfolding rb_deq_def CleanQ_RB_list_def 
  by (simp add: rb_incr_tail_valid_entries)

lemma rb_deq_list_tail :
  assumes notempty: "\<not> rb_empty rb" and  valid: "rb_valid rb"   
  and  res: "rb' = rb_deq rb"
shows "CleanQ_RB_list (snd (rb')) = tl (CleanQ_RB_list rb)"
  using  res notempty valid unfolding rb_deq_def CleanQ_RB_list_def 
  apply (simp)
  by (metis Pair_inject map_tl rb_deq_def rb_incr_tail_def 
            rb_incr_tail_valid_entries_tail res)

lemma rb_deq_list_not_in :
  assumes notempty: "\<not>rb_empty rb" and  valid: "rb_valid rb"  
     and res: "rb' = rb_deq rb" and dist: "distinct (CleanQ_RB_list rb)"
shows "(fst rb') \<notin> set (CleanQ_RB_list (snd rb')) "
  using notempty valid res dist
  by (metis (no_types, lifting) CleanQ_RB_list_def distinct.simps(2) 
            fstI list.simps(9) map_tl rb_deq_def rb_deq_list_tail 
              rb_incr_tail_valid_entries rb_incr_tail_valid_entries_tail)

lemma rb_deq_subset :
  assumes notempty: "\<not>rb_empty rb" and  valid: "rb_valid rb"  
     and res: "rb' = rb_deq rb" and dist: "distinct (CleanQ_RB_list rb)"
   shows "set (CleanQ_RB_list (snd rb')) \<subset> set (CleanQ_RB_list rb) "
  using notempty valid res dist
  by (metis (no_types, lifting) CleanQ_RB_list_def insert_Diff insert_iff list.map(2) 
            list.simps(3) list_set_hd_tl_subtract order.not_eq_order_implies_strict 
            rb_deq_list_not_in rb_deq_list_tail rb_deq_list_was_head rb_deq_list_was_in 
            rb_incr_tail_valid_entries subsetI)
   


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
  we use the nonzero_modulus locale to produce a list of indices into the bounded
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
  where "CleanQ_RB_enq_x_possible rb \<longleftrightarrow> \<not>(rb_full (rTXY rb))"

definition CleanQ_RB_enq_y_possible :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "CleanQ_RB_enq_y_possible rb \<longleftrightarrow> \<not>(rb_full (rTYX rb))"


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
  using can_enq invariants 
  by (simp add: CleanQ_RB_enq_x_possible_def rb_enq_list_add)

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
  shows  "b \<notin> rSX rb' \<and> b \<notin> rSY rb' \<and> b \<notin> set (CleanQ_RB_list (rTYX rb')) 
          \<and> b = rb_read (head (rTXY rb)) (rTXY rb')  \<and> b \<in> set (CleanQ_RB_list (rTXY rb'))"
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

   from can_enq invariants X_enq have X4:
    "b = rb_read (head (rTXY rb)) (rTXY rb')"
     using X_owned unfolding CleanQ_RB_enq_x_def CleanQ_RB_enq_x_possible_def
     by (simp add: rb_enq_buf) 
     
    have X5:
    "b \<in> set (CleanQ_RB_list (rTXY rb'))"
     apply (subst X_enq)
      apply (simp add:CleanQ_RB_enq_x_def)
      using CleanQ_RB_enq_x_possible_def can_enq invariants rb_enq_list_add by fastforce
          
  show ?thesis
    using X1 X2 X3 X4 X5 by(auto)
qed 


lemma CleanQ_RB_enq_y_result :
  assumes Y_owned: "b \<in> rSY rb"  and  Y_enq: "rb' = CleanQ_RB_enq_y b rb"
    and invariants : "CleanQ_RB_Invariants K rb"  
    and can_enq:  "CleanQ_RB_enq_y_possible rb" 
  shows  "b \<notin> rSX rb' \<and> b \<notin> rSY rb' \<and> b \<notin> set (CleanQ_RB_list (rTXY rb')) 
          \<and> b = rb_read (head (rTYX rb)) (rTYX rb')  \<and> b \<in> set (CleanQ_RB_list (rTYX rb'))"
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

   from can_enq invariants Y_enq have X4:
    "b = rb_read (head (rTYX rb)) (rTYX rb')"
     using Y_owned unfolding CleanQ_RB_enq_y_def CleanQ_RB_enq_y_possible_def
     by (simp add: rb_enq_buf) 
     
    have X5:
    "b \<in> set (CleanQ_RB_list (rTYX rb'))"
     apply (subst Y_enq)
      apply (simp add:CleanQ_RB_enq_y_def)
      using CleanQ_RB_enq_y_possible_def can_enq invariants rb_enq_list_add by fastforce
          
  show ?thesis
    using X1 X2 X3 X4 X5 by(auto)
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


lemma CleanQ_RB_enq_y_I4 :
 assumes Inv: "CleanQ_RB_Invariants K rb"  and  X_owned: "b \<in> rSX rb" and
         X_enq: "rb' = CleanQ_RB_enq_x b rb" and  can_enq: "CleanQ_RB_enq_x_possible rb"
  shows "I4_rb_valid rb'"
  apply(subst X_enq)
  using can_enq unfolding CleanQ_RB_enq_x_def CleanQ_RB_list_def CleanQ_RB_enq_x_possible_def
  using Inv by(simp add:rb_enq_remains_valid)


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
  where "CleanQ_RB_deq_x_possible rb \<longleftrightarrow> \<not>(rb_empty (rTYX rb))"

definition CleanQ_RB_deq_y_possible :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "CleanQ_RB_deq_y_possible rb \<longleftrightarrow> \<not>(rb_empty (rTXY rb))"


lemma CleanQ_RB_deq_x_equal :
  assumes can_deq: "CleanQ_RB_deq_x_possible rb" 
      and invariants : "CleanQ_RB_Invariants K rb"
  shows "CleanQ_RB2List (CleanQ_RB_deq_x rb) = CleanQ_List_deq_x (CleanQ_RB2List rb)"  
  unfolding CleanQ_RB2List_def CleanQ_RB_deq_x_def CleanQ_List_deq_x_def 
  using can_deq invariants
  by (simp add: CleanQ_RB_deq_x_possible_def prod.case_eq_if rb_deq_list_tail 
                rb_deq_list_was_head)

lemma CleanQ_RB_deq_y_equal :
  assumes can_deq: "CleanQ_RB_deq_y_possible rb" 
      and invariants : "CleanQ_RB_Invariants K rb"
  shows "CleanQ_RB2List (CleanQ_RB_deq_y rb) = CleanQ_List_deq_y (CleanQ_RB2List rb)"  
  unfolding CleanQ_RB2List_def CleanQ_RB_deq_y_def CleanQ_List_deq_y_def 
  using can_deq invariants
  by (simp add: CleanQ_RB_deq_y_possible_def prod.case_eq_if rb_deq_list_tail 
                rb_deq_list_was_head)

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
    and invariants : "CleanQ_RB_Invariants K rb"  and buf: "b = rb_read (tail (rTYX rb)) (rTYX rb)"
  shows  "b \<in> rSX rb' \<and> b \<notin> rSY rb' \<and> b \<notin> set (CleanQ_RB_list (rTYX rb')) 
          \<and> b \<notin> set (CleanQ_RB_list (rTXY rb')) "
proof -

  have X1:"b \<in> rSX rb'"
    using buf X_deq unfolding CleanQ_RB_deq_x_def
    by (simp add: rb_deq_def rb_read_def)
    
  have X2:"b \<notin> rSY rb'" 
    using invariants buf X_deq unfolding CleanQ_RB_deq_x_def
    by (metis (no_types, lifting) CleanQ_List_State.ext_inject CleanQ_List_State.surjective 
              CleanQ_List_deq_x_upd CleanQ_RB2List_def CleanQ_RB_Invariants.elims(2) 
              CleanQ_RB_deq_x_possible_def CleanQ_RB_deq_x_equal I2_rb_img.elims(2) 
              I4_rb_valid.elims(2) X_deq can_deq disjoint_iff_not_equal fstI rb_deq_def 
              rb_deq_list_was_in rb_read_def)
  have X3:"b \<notin> set (CleanQ_RB_list (rTYX rb'))"
    using buf X_deq can_deq unfolding CleanQ_RB_deq_x_def CleanQ_RB_deq_x_possible_def
    apply(simp)
    by (metis CleanQ_List_State.ext_inject CleanQ_List_State.surjective 
              CleanQ_List_deq_x_upd CleanQ_RB2List_def CleanQ_RB_Invariants.elims(2) 
              CleanQ_RB_deq_x_equal I3_rb_img.elims(2) I4_rb_valid.elims(2) X_deq can_deq 
              fstI invariants rb_deq_def rb_deq_list_not_in rb_deq_list_tail rb_read_def)

  have X4:"b \<notin> set (CleanQ_RB_list (rTXY rb'))"
     using buf X_deq can_deq unfolding CleanQ_RB_deq_x_def CleanQ_RB_deq_x_possible_def
    apply(simp)
     by (metis CleanQ_List_State.ext_inject CleanQ_List_State.surjective 
               CleanQ_List_deq_x_upd CleanQ_RB2List_def CleanQ_RB_Invariants.elims(2) 
               CleanQ_RB_deq_x_equal I2_rb_img.elims(2) I4_rb_valid.elims(2) X_deq can_deq 
               disjoint_insert(1) fstI insert_Diff invariants rb_deq_def rb_deq_list_was_in 
               rb_read_def)
    
  show ?thesis using X1 X2 X3 X4 by(simp)   
qed


lemma CleanQ_RB_deq_y_result :
  assumes can_deq: "CleanQ_RB_deq_y_possible rb"  and  Y_deq: "rb' = CleanQ_RB_deq_y rb"
    and invariants : "CleanQ_RB_Invariants K rb"  and buf: "b = rb_read (tail (rTXY rb)) (rTXY rb)"
  shows  "b \<notin> rSX rb' \<and> b \<in> rSY rb' \<and> b \<notin> set (CleanQ_RB_list (rTYX rb')) 
          \<and> b \<notin> set (CleanQ_RB_list (rTXY rb')) "
proof -
  have X1:"b \<in> rSY rb'"
    using buf Y_deq unfolding CleanQ_RB_deq_y_def
    by (simp add: rb_deq_def rb_read_def)
    
  have X2:"b \<notin> rSX rb'" 
    using invariants buf Y_deq unfolding CleanQ_RB_deq_y_def
    by (metis (no_types, lifting) CleanQ_List_State.ext_inject CleanQ_List_State.surjective 
              CleanQ_List_deq_y_upd CleanQ_RB2List_def CleanQ_RB_Invariants.elims(2) 
              CleanQ_RB_deq_y_possible_def CleanQ_RB_deq_y_equal I2_rb_img.elims(2) 
              I4_rb_valid.elims(2) Y_deq can_deq disjoint_iff_not_equal fstI rb_deq_def 
              rb_deq_list_was_in rb_read_def)
  have X3:"b \<notin> set (CleanQ_RB_list (rTXY rb'))"
    using buf Y_deq can_deq unfolding CleanQ_RB_deq_y_def CleanQ_RB_deq_y_possible_def
    apply(simp)
    by (metis CleanQ_List_State.ext_inject CleanQ_List_State.surjective 
              CleanQ_List_deq_y_upd CleanQ_RB2List_def CleanQ_RB_Invariants.elims(2) 
              CleanQ_RB_deq_y_equal I3_rb_img.elims(2) I4_rb_valid.elims(2) Y_deq can_deq 
              fstI invariants rb_deq_def rb_deq_list_not_in rb_deq_list_tail rb_read_def)
    
  have X4:"b \<notin> set (CleanQ_RB_list (rTYX rb'))"
     using buf Y_deq can_deq unfolding CleanQ_RB_deq_y_def CleanQ_RB_deq_y_possible_def
    apply(simp)
     by (metis CleanQ_List_State.ext_inject CleanQ_List_State.surjective 
               CleanQ_List_deq_y_upd CleanQ_RB2List_def CleanQ_RB_Invariants.elims(2) 
               CleanQ_RB_deq_y_equal I2_rb_img.elims(2) I4_rb_valid.elims(2) Y_deq can_deq 
               disjoint_insert(1) fstI insert_Diff invariants rb_deq_def rb_deq_list_was_in 
               rb_read_def)
    
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
              rb_deq_list_was_in set_append)

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
              rb_deq_list_was_in set_append)

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
            rb_deq_list_was_head rb_deq_list_was_in)

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
  
  

(* ==================================================================================== *)
subsection \<open>Pre- and post- conditions\<close>
(* ==================================================================================== *)


definition CleanQ_RB_enq_x_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_RB_State, 'a CleanQ_RB_State) Semantic.xstate set"
  where "CleanQ_RB_enq_x_pre K b =  Semantic.Normal ` {rb. I1_rb_img rb K \<and> I2_rb_img rb \<and> I3_rb_img rb \<and> b \<in> rSX rb }"

definition CleanQ_RB_enq_y_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_RB_State, 'a CleanQ_RB_State) Semantic.xstate set"
  where "CleanQ_RB_enq_y_pre K b = Semantic.Normal ` {rb. I1_rb_img rb K \<and> I2_rb_img rb \<and> I3_rb_img rb \<and> b \<in> rSY rb}"

definition CleanQ_RB_deq_x_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_RB_State, 'a CleanQ_RB_State) Semantic.xstate set"        
  where "CleanQ_RB_deq_x_pre K buf = Semantic.Normal ` {rb. I1_rb_img rb K \<and> I2_rb_img rb \<and> I3_rb_img rb \<and>
                                                        CleanQ_RB_list  (rTYX rb) \<noteq> [] \<and> buf = ring (rTYX rb) (tail (rTYX rb))}"
definition CleanQ_RB_deq_y_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_RB_State, 'a CleanQ_RB_State) Semantic.xstate set"        
  where "CleanQ_RB_deq_y_pre K buf = Semantic.Normal ` {rb. I1_rb_img rb K \<and> I2_rb_img rb \<and> I3_rb_img rb \<and>
                                                        CleanQ_RB_list  (rTXY rb) \<noteq> [] \<and> buf = ring (rTXY rb) (tail (rTXY rb))}"


  
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
*)

end (*Modulus end *)

end

*)