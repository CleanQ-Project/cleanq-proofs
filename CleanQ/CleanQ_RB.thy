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



section \<open>Bounded Descriptor Ring\<close>

text \<open>
  In this theory, we define a ring buffer data structure. This forms a bounded list of
  buffer elements. As a consequence, the adding new elements to the data structure may
  fail, because there is no more space in the ring buffer. 
\<close>

theory CleanQ_RB 
(*<*) 
  imports CleanQ_ModularIntervals CleanQ_Utils
(*>*)
begin


(* ==================================================================================== *)
subsection \<open>Data Type Definition\<close>
(* ==================================================================================== *)

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
  and the buffer needs a certain size. Note, we require the size of the ring to be at
  least 2. By using the head and tail pointers, we need to be able to distinguish 
  a full from an empty ring buffer. This requires to `give up' one element to always
  distinguish the full and empty conditions below.
\<close>

definition rb_valid :: "'a CleanQ_RB \<Rightarrow> bool"
  where "rb_valid rb \<longleftrightarrow> (head rb < size rb) \<and> (tail rb < size rb) \<and> (size rb > 1)"


(* ==================================================================================== *)
subsection \<open>Full and Empty Predicates\<close>
(* ==================================================================================== *)

text \<open>
  We say a ring buffer is full, if the enqueue operation would lead to the case
  where the head pointer == tail pointer. 
\<close>

definition rb_full :: "'a CleanQ_RB \<Rightarrow> bool"
  where "rb_full rb = ((((head rb) + 1) mod (size rb)) = (tail rb))"

text \<open>
 
\<close>
lemma rb_full_no_modulo:
  assumes valid: "rb_valid rb"
    shows "rb_full rb \<longleftrightarrow> (if (head rb) + 1 = size rb  then tail rb = 0
                           else tail rb = head rb + 1)"
  using valid unfolding rb_full_def rb_valid_def by(auto)


text \<open>
  Likewise, the ring buffer is empty, if its head and tail pointers are equal. 
\<close>

definition rb_empty :: "'a CleanQ_RB \<Rightarrow> bool"
  where "rb_empty rb = ((head rb) = (tail rb))"

text \<open>
  Next we can show that the empty and full predicates imply the negation of eachother
\<close>

lemma rb_full_not_empty:
  "rb_valid rb \<Longrightarrow> rb_full rb \<Longrightarrow> \<not> rb_empty rb"
  apply(simp add:rb_full_no_modulo)
  unfolding rb_empty_def rb_valid_def by presburger

lemma rb_empty_not_full:
  "rb_valid rb \<Longrightarrow> rb_empty rb \<Longrightarrow> \<not> rb_full rb"
  apply(simp add:rb_full_no_modulo)
  unfolding rb_empty_def rb_valid_def by presburger

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
  they are part of the valid entries. First, the head is never part of the set of
  valid entries.
\<close>

lemma rb_valid_entries_head :
  "(head rb) \<notin> set (rb_valid_entries rb)"
  unfolding rb_valid_entries_def by(auto)

text \<open>
  Next, if the ring buffer is emtpy, then the tail is also not part of the set of
  valid entries. In fact, the set is the empty set.
\<close>

lemma rb_valid_entries_tail_empty1 :
  "head rb = tail rb \<Longrightarrow> (tail rb) \<notin> set (rb_valid_entries rb)"
  unfolding rb_valid_entries_def by(simp)

lemma rb_valid_entries_tail_emtpy2 :
  "rb_empty rb  \<Longrightarrow> (tail rb) \<notin> set (rb_valid_entries rb)"
  unfolding rb_empty_def rb_valid_entries_def by(simp)

lemma rb_valid_entries_empty_list :
  "rb_empty rb \<Longrightarrow> rb_valid_entries rb = []"
   unfolding rb_empty_def rb_valid_entries_def by(simp)

lemma rb_valid_entries_empty_list2 :
  "rb_valid rb \<Longrightarrow> rb_empty rb \<longleftrightarrow> rb_valid_entries rb = []"
   unfolding rb_empty_def rb_valid_entries_def rb_valid_def by(auto)

lemma rb_valid_entries_empty_set :
  "rb_empty rb \<Longrightarrow> set (rb_valid_entries rb) = {}"
   unfolding rb_empty_def rb_valid_entries_def by(simp)

lemma rb_valid_entries_empty_set2 :
  "rb_valid rb \<Longrightarrow> rb_empty rb \<longleftrightarrow> set (rb_valid_entries rb) = {}"
   unfolding rb_empty_def rb_valid_entries_def rb_valid_def by(auto)

text \<open>
  Finally, when the ring buffer is not empty then the tail is part of the set of 
  valid entries. The same applies if the ring buffer is full. 
\<close>

lemma rb_valid_entries_tail_not_empty1 :
  "rb_valid rb \<Longrightarrow> head rb \<noteq> tail rb \<Longrightarrow> (tail rb) \<in> set (rb_valid_entries rb)"
  unfolding rb_valid_entries_def rb_valid_def by(simp)

lemma rb_valid_entries_tail_not_empty2:
  "rb_valid rb \<Longrightarrow> \<not>rb_empty rb \<Longrightarrow> (tail rb) \<in> set (rb_valid_entries rb)"
  unfolding rb_valid_entries_def rb_valid_def rb_empty_def by(simp)

lemma rb_valid_entries_tail_not_empty3:
  "rb_valid rb \<Longrightarrow> rb_full rb \<Longrightarrow> (tail rb) \<in> set (rb_valid_entries rb)"
  using rb_full_not_empty rb_valid_entries_tail_not_empty2 by(auto)

text \<open>
  Moreover, we can show that if there are valid elements in the ring buffer, 
  then the tail is the first element (head) of the list of valid entries.
\<close>

lemma rb_valid_entries_tail_first1:
  "rb_valid rb \<Longrightarrow> \<not>rb_empty rb \<Longrightarrow> (tail rb) = hd (rb_valid_entries rb)"
  unfolding rb_valid_def rb_empty_def rb_valid_entries_def by(auto)

lemma rb_valid_entries_tail_first2:
  "rb_valid rb \<Longrightarrow> rb_full rb \<Longrightarrow> (tail rb) = hd (rb_valid_entries rb)"
  using rb_full_not_empty rb_valid_entries_tail_first1 by(auto)



(* ==================================================================================== *)
subsection \<open>Incrementing Tail and Head Pointers\<close>
(* ==================================================================================== *)

text \<open>
  We provide functions that increment the head and tail pointers of the queue. This
  effectively changes the set of valid entries of the ring buffer, and likewise also the
  valid buffers in the queue. Note we always use the modulo Operator.
\<close>

definition rb_incr_head :: "'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB"
  where "rb_incr_head rb = rb \<lparr> head := ((head rb) + 1) mod (size rb) \<rparr>"

definition rb_incr_tail :: "'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB"
  where "rb_incr_tail rb = rb \<lparr> tail := ((tail rb) + 1) mod (size rb) \<rparr>"

text \<open>
 We first show that the two increment functions are in fact preserving the valid predicate.
\<close>

lemma rb_incr_head_valid:
  "rb_valid rb \<Longrightarrow> rb_valid (rb_incr_head rb)"
  unfolding rb_valid_def rb_incr_head_def by(simp)

lemma rb_incr_tail_valid:
  "rb_valid rb \<Longrightarrow> rb_valid (rb_incr_tail rb)"
  unfolding rb_valid_def rb_incr_tail_def by(simp)


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

text \<open>
  When we increment the tail, then the original tail is no longer in the set of
  valid entries
\<close>

lemma rb_incr_tail_valid_entries_notin1:
assumes notempty: "\<not> rb_empty rb" and  valid: "rb_valid rb" 
  shows "(tail rb) \<notin> set(rb_valid_entries (rb_incr_tail rb))"
  using notempty valid apply(simp add:rb_incr_tail_valid_entries_tail)
  unfolding rb_valid_def rb_empty_def rb_valid_entries_def by(auto)

lemma rb_incr_tail_valid_entries_notin2:
assumes notempty: "\<not> rb_empty rb" and  valid: "rb_valid rb" 
  shows "hd (rb_valid_entries rb) \<notin> set (rb_valid_entries (rb_incr_tail rb))"
  using notempty valid rb_valid_entries_tail_first1 rb_incr_tail_valid_entries_notin1
  by fastforce
  
text \<open> 
  Incrementing the head then adds the current head pointer to the list of valid entries
\<close>

lemma rb_incr_head_valid_entries:
assumes notfull: "\<not> rb_full rb" and  valid: "rb_valid rb"  
  shows "rb_valid_entries (rb_incr_head rb) = (rb_valid_entries rb) @ [(head rb)]"
  using notfull valid 
  unfolding rb_valid_entries_def rb_incr_head_def rb_full_def rb_valid_def
  apply(simp add: mod_Suc upt_Suc_append  upt_conv_Cons, auto)
  by (metis le_imp_less_Suc upt_Suc_append upt_rec)
  
lemma rb_incr_head_valid_entries_butlast:
assumes notfull: "\<not> rb_full rb" and  valid: "rb_valid rb"  
  shows "(rb_valid_entries rb) = butlast (rb_valid_entries (rb_incr_head rb))"
  using notfull valid by (metis butlast_snoc rb_incr_head_valid_entries)

text \<open>
  The head elementis added to the set of valid entries, in fact at the end of the
  list.
\<close>

lemma rb_incr_head_valid_entries_head:
assumes notfull: "\<not> rb_full rb" and  valid: "rb_valid rb"  
  shows "head rb \<in> set (rb_valid_entries (rb_incr_head rb))"
  using notfull valid apply(subst rb_incr_head_valid_entries)
  by(auto)
  
lemma rb_incr_head_valid_entries_last:
assumes notfull: "\<not> rb_full rb" and  valid: "rb_valid rb"  
  shows "head rb  = last (rb_valid_entries (rb_incr_head rb))"
  using notfull valid apply(subst rb_incr_head_valid_entries)
  by(auto)


text \<open>
  And finally, the incrementing the head or tail pointers does not change the contents of 
  the ring. 
\<close>

lemma rb_incr_head_ring: 
  "(ring (rb_incr_head rb)) = ring rb"
  unfolding rb_incr_head_def by(auto)

lemma rb_incr_tail_ring: 
  "(ring (rb_incr_tail rb)) = ring rb"
  unfolding rb_incr_tail_def by(auto)


(* ==================================================================================== *)
subsection \<open>Writing Entries in the Descriptor Ring\<close>
(* ==================================================================================== *)

text \<open>
  Writing an entry into the ring buffer then corresponds to a function update. The update
  always modifies the element at the head position.
\<close>

definition rb_write :: "'a \<Rightarrow> 'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB"
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
  the ring buffer, as the head / tail pointers are not changed.
\<close>
lemma rb_write_perserves_valid_entries:
  "rb_valid_entries rb = rb_valid_entries (rb_write b rb)"
  unfolding rb_write_def rb_valid_entries_def by(auto)

lemma rb_write_preserves_valid:
  "rb_valid rb \<Longrightarrow> rb_valid (rb_write b rb)"
  unfolding rb_valid_def rb_write_def by(auto)


(* ==================================================================================== *)
subsection \<open>Enqueue Operation\<close>
(* ==================================================================================== *)


text \<open>
  We can only enqueue something in the ring buffer, if there is space in the ring
  buffer. In other words, the ring buffer is not full.
\<close>

definition rb_can_enq :: "'a CleanQ_RB \<Rightarrow> bool"
  where "rb_can_enq rb \<longleftrightarrow> \<not>(rb_full rb)"


text \<open>
  The enqueue operation is then the combination of the update and the increment
  of the head pointer. 
\<close>

definition rb_enq :: "'a \<Rightarrow> 'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB" 
  where "rb_enq b rb = rb_incr_head (rb_write b rb)"

text \<open>
  This is a function composition of the head increment and the write to the ring:
\<close>

definition rb_enq_fun :: "'a \<Rightarrow> 'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB" 
  where "rb_enq_fun b rb = ((rb_incr_head o rb_write b)) rb"

text \<open>
  This produces the following updates to the structure:
\<close>

definition rb_enq_alt :: "'a \<Rightarrow> 'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB" 
  where "rb_enq_alt b rb = rb \<lparr> ring := (ring rb)((head rb) := b),
                                head := ((head rb) + 1) mod (size rb) \<rparr>"

text \<open>
  And we can show that the three enqueue definitions are in fact equivalent:
\<close>

lemma rb_enq_equiv:
  "rb_enq b rb = rb_enq_alt b rb"
  unfolding rb_enq_alt_def rb_enq_def rb_incr_head_def rb_write_def by(auto)

lemma rb_enq_equiv_fun:
  "rb_enq b rb = rb_enq_fun b rb"
  unfolding rb_enq_fun_def rb_enq_def by(auto)


text \<open>
  The enqueue function preserves the validity predicate of the ring buffer. 
\<close>

lemma rb_enq_remains_valid:
assumes  valid: "rb_valid rb"
  shows "rb_valid (rb_enq b rb)"
  apply(subst rb_enq_equiv_fun)
  using valid rb_write_preserves_valid rb_incr_head_valid 
  unfolding rb_enq_fun_def by fastforce


text \<open>
  We can now show that the enqueue operation leaves the buffer in the old head 
  element. 
\<close>

lemma rb_enq_buf_ring :
  "rb' = rb_enq b rb \<Longrightarrow> (ring (rb'))((head rb)) = b"
  unfolding rb_enq_def rb_incr_head_def rb_write_def by(auto)

lemma rb_enq_buf:
 "rb' = rb_enq b rb \<Longrightarrow> rb_read (head rb) rb' = b"
  by (simp add: rb_enq_alt_def rb_enq_equiv rb_read_def)

lemma rb_enq_buf2:
  "rb_read (head rb) (rb_enq b rb) = b"
  by (simp add: rb_enq_alt_def rb_enq_equiv rb_read_def)

text \<open>
  Next we can talk about the effects on the set of valid entries in the ring buffer, 
  when we enqueue a new element to the ring buffer.
\<close>

lemma rb_enq_valid_entries_incr_head:
assumes notfull: "rb_can_enq rb" and valid: "rb_valid rb"  
shows "rb_valid_entries (rb_enq b rb) =  rb_valid_entries (rb_incr_head rb)"
  apply(subst rb_enq_equiv_fun)
  apply(subst rb_enq_fun_def)
  unfolding rb_write_def using notfull valid rb_write_perserves_valid_entries 
  by (simp add: rb_incr_head_def rb_valid_entries_def rb_enq_equiv_fun)


lemma rb_enq_valid_entries :
assumes notfull: "rb_can_enq rb" and valid: "rb_valid rb"   
shows "rb_valid_entries (rb_enq b rb) = rb_valid_entries (rb) @ [(head rb)]"
  using notfull valid rb_write_perserves_valid_entries rb_enq_valid_entries_incr_head
  by (simp add: rb_enq_valid_entries_incr_head rb_can_enq_def rb_incr_head_valid_entries)

text \<open>
  The enqueue operation preserves the already existing entries in the ring.
\<close>

lemma rb_enq_preserves_valid_entries:
  assumes notfull: "rb_can_enq rb"  and valid: "rb_valid rb"   
  shows "\<forall>i \<in> set(rb_valid_entries rb). (ring (rb_enq b rb)) i = (ring rb) i"
  by (simp add: rb_enq_def rb_incr_head_ring rb_valid_entries_head rb_write_def)


(* ==================================================================================== *)
subsection \<open>Dequeue Operation\<close>
(* ==================================================================================== *)

text \<open>
  We can only dequeue something in the ring buffer, if there is an element in the ring
  buffer. In other words, the ring buffer is not empty.
\<close>

definition rb_can_deq :: "'a CleanQ_RB \<Rightarrow> bool"
  where "rb_can_deq rb \<longleftrightarrow> \<not>(rb_empty rb)"

text \<open>
 The dequeue operation then returns a tuple of the removed element and the remainder
 of the queue. 

 TODO: how is this best expressed ??
\<close>

definition rb_deq :: "'a CleanQ_RB \<Rightarrow> ('a \<times> 'a CleanQ_RB)"
  where "rb_deq rb = (rb_read_tail rb, rb_incr_tail rb)"

text \<open>
  This produces the following updates to the structure:
\<close>

definition rb_deq_alt :: "'a CleanQ_RB \<Rightarrow> ('a \<times> 'a CleanQ_RB)"
  where "rb_deq_alt rb = ((ring rb) (tail rb),  
                      rb \<lparr> tail := ((tail rb) + 1) mod (size rb) \<rparr> )"

text \<open>
  We can show that the two dequeue definitions produce the same outcome
\<close>

lemma rb_deq_equiv:
  "rb_deq rb = rb_deq_alt rb"
  unfolding rb_deq_def rb_deq_alt_def rb_read_tail_def rb_incr_tail_def rb_read_def
  by(auto)
  
text \<open>
  The dequeue operation preserves the validity of the ring buffer.
\<close>

lemma rb_deq_remains_valid:
  assumes valid: "rb_valid rb" and notempty: "rb_can_deq rb"
  shows "rb_valid (snd (rb_deq rb))"
  unfolding rb_deq_def using rb_incr_tail_valid valid by(auto)
  

lemma rb_deq_buf:
  assumes valid: "rb_valid rb" and notempty: "rb_can_deq rb"
  shows "fst (rb_deq rb) \<longleftrightarrow> rb_read_tail rb"
  by(simp add: rb_deq_def)



(* ==================================================================================== *)
subsection \<open>Lifting Ring Buffers to Lists\<close>
(* ==================================================================================== *)

text \<open>
  Using the valid entries, we can define the buffer elements in the descriptor ring
  by mapping them onto the ring-function of the CleanQ RB:
\<close>

definition CleanQ_RB_list :: "'a CleanQ_RB \<Rightarrow> 'a list"
  where "CleanQ_RB_list rb = map (ring rb) (rb_valid_entries rb)"

text \<open>
  If the ring is valid, then the list is bounded by the size of the ring.
\<close>

lemma rb_list_size:
  "rb_valid rb \<Longrightarrow> (length (CleanQ_RB_list rb) < size rb)"
  unfolding CleanQ_RB_list_def rb_valid_entries_def rb_valid_def
  by auto


text \<open>
 We can now show that the list of valid entries is empty, when the predicate 
 \verb+rb_empty+ is true.
\<close>

lemma rb_list_empty:
  assumes valid: "rb_valid rb"
  shows "rb_empty rb \<longleftrightarrow> CleanQ_RB_list rb = []"
  unfolding  CleanQ_RB_list_def using valid rb_valid_entries_empty_list2 by(auto)


text \<open>
  Doing the enqueue operation then behaves as adding the buffer to the end
  of the list.
\<close>

lemma rb_enq_list_add:
assumes notfull: "rb_can_enq rb" and valid: "rb_valid rb"   
  shows "CleanQ_RB_list (rb_enq b rb) = (CleanQ_RB_list rb) @ [b]"
  using notfull valid unfolding CleanQ_RB_list_def
  by (simp add: rb_enq_buf_ring rb_enq_preserves_valid_entries rb_enq_valid_entries)


text \<open>
  The dequeue operation returns an element which is in the list of the original state,
  and the element is the head of this list.
\<close>

lemma rb_deq_list_was_head :
  assumes notempty: "rb_can_deq rb" and  valid: "rb_valid rb"  
     and res: "rb' = rb_deq rb" 
   shows "(fst rb') = hd (CleanQ_RB_list rb)"
  using notempty valid unfolding rb_deq_def CleanQ_RB_list_def 
  by (simp add: rb_can_deq_def rb_deq_alt_def rb_deq_equiv rb_incr_tail_valid_entries res)

lemma rb_deq_list_was_in :
  assumes notempty: "rb_can_deq rb" and  valid: "rb_valid rb"  
     and res: "rb' = rb_deq rb" 
   shows "(fst rb') \<in> set (CleanQ_RB_list rb)"
  using res notempty valid rb_deq_list_was_head rb_can_deq_def rb_list_empty by fastforce

text \<open>
  Likewise, the remainder of the state will be the tail of the original list. 
\<close>

lemma rb_deq_list_tail :
  assumes notempty: "rb_can_deq rb" and  valid: "rb_valid rb"   
  and  res: "rb' = rb_deq rb"
shows "CleanQ_RB_list (snd (rb')) = tl (CleanQ_RB_list rb)"
  using  res notempty valid unfolding rb_deq_def CleanQ_RB_list_def 
  by (simp add: map_tl rb_can_deq_def rb_incr_tail_ring rb_incr_tail_valid_entries_tail)


lemma rb_deq_list_not_in :
  assumes notempty: "rb_can_deq rb" and  valid: "rb_valid rb"  
     and res: "rb' = rb_deq rb" and dist: "distinct (CleanQ_RB_list rb)"
   shows "(fst rb') \<notin> set (CleanQ_RB_list (snd rb')) "
  using notempty valid res  
  apply(subst rb_deq_list_tail, simp_all)
  using rb_deq_list_was_head dist 
  by (metis distinct.simps(2) list.collapse rb_can_deq_def rb_list_empty)


lemma rb_deq_not_empty:
assumes notempty: "rb_can_deq rb" and  valid: "rb_valid rb" 
  shows "CleanQ_RB_list rb \<noteq> []"
  unfolding CleanQ_RB_list_def
  using valid notempty rb_can_deq_def rb_valid_entries_tail_not_empty2 by fastforce

lemma rb_deq_subset :
  assumes notempty: "rb_can_deq rb" and  valid: "rb_valid rb"  
     and res: "rb' = rb_deq rb" and dist: "distinct (CleanQ_RB_list rb)"
   shows "set (CleanQ_RB_list (snd rb')) \<subset> set (CleanQ_RB_list rb) " 
  using notempty valid res
  apply(simp add:rb_deq_list_tail)
  using dist rb_deq_not_empty list_set_hd_tl_union2 rb_deq_list_not_in 
        rb_deq_list_tail rb_deq_list_was_in 
  by fastforce
  
   
end