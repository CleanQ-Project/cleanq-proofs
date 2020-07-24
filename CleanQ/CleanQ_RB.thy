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

(* 

  Some comments regarding the definition of the Clean_RB below. 

  The current definition of the ring is as a function. 
    
    ring :: "nat \<Rightarrow> 'a"

  This is problematic, as the ring has its size and buffers outside of 0..<size are 
  not defined. 

  There are a few options how to deal with this:

    1) The ring is a partial function, i.e. it returns something for some inputs (Some 'a)
       and nothing otherwise (None)

        ring :: "nat \<rightharpoonup> 'a "
        ring :: "nat \<Rightarrow> 'a option"

    2) The ring returns a set of buffers for every index. If its within a defined range, 
       this is the single ton set {b::'a}, otherwise the emtpy set{} or UNIV is returned. 

        ring :: "nat \<Rightarrow> 'a set"

    3) Implement the own option type e.g. 

        datatype 'a buffer =  Nil | Buf 'a 
        ring :: "nat \<Rightarrow> 'a buffer"
*)

text \<open>
  We first define the type of a the bounded, circular descriptor ring, which we call
  ring buffer (RB). A ring buffer has a well-defined size, or number of slots, which
  defines the amount of elements it can hold.  We define the ring buffer as a function
  from nat to the element. Head and tail define the valid elements in the ring.\<close>

record 'a CleanQ_RB =
  ring :: "nat \<Rightarrow> 'a option"
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
  where "rb_valid rb \<longleftrightarrow> (head rb < size rb) \<and> (tail rb < size rb) \<and> (1 < size rb) \<and>
                         (\<forall>i < size rb. ring rb i \<noteq> None)"

(* setting the entries to be defined for all entries in the ring for now... somehow
   this should only be for the ones that are in the set of valid entries *)

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
  apply(simp add:rb_full_no_modulo rb_empty_def rb_valid_def)
  by (metis Suc_eq_plus1 less_irrefl_nat n_not_Suc_n)

lemma rb_empty_not_full:
  "rb_valid rb \<Longrightarrow> rb_empty rb \<Longrightarrow> \<not> rb_full rb"
  by(simp add:rb_full_no_modulo rb_empty_def rb_valid_def)


text \<open>
  A ringbuffer has a certain set of valid entries. We now provide definitions to 
  create the list of entries. Note, this is not [(tail rb) ..<(head rb)]. As there
  might be a wrap around (e.g. head = 4 tail = 8). We use the nonzero modulus
  locale to work out the elements.

  Using the head and tail pointer we can now define the list of valid entries of the 
  ring. We do this by a case distinction if head <= tail or the other way round.
\<close>

definition rb_valid_entries :: "'a CleanQ_RB \<Rightarrow> nat list"
  where "rb_valid_entries rb = (if (tail rb) \<le> (head rb) 
                                then [(tail rb) ..< (head rb)]
                                else [(tail rb)..< (size rb)] @ [0..<(head rb)])"

definition rb_invalid_entries :: "'a CleanQ_RB \<Rightarrow> nat list"
  where "rb_invalid_entries rb = (if (tail rb) \<le> (head rb) 
                                  then [(head rb) ..< (size rb)] @ [0 ..< (tail rb)]
                                  else [(head rb)..< (tail rb)])"


lemma rb_valid_invalid_entries_set:
  assumes valid: "rb_valid rb"
  shows "set (rb_valid_entries rb) \<union> set (rb_invalid_entries rb) = {0..<(size rb)}"
  using valid unfolding rb_valid_entries_def rb_invalid_entries_def rb_valid_def
  by auto


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


text \<open>
  Last we show that the number of valid entries is less than the size of the ring and
  the total number of valid and invalid entries is the size of the ring
\<close>

lemma rb_valid_entries_less_size:
  assumes valid: "rb_valid rb"
  shows "length (rb_valid_entries rb) < size rb"
  unfolding rb_valid_def rb_valid_entries_def 
proof auto
  show "tail rb \<le> head rb \<Longrightarrow> head rb - tail rb < CleanQ_RB.size rb" using valid
    by (simp add: less_imp_diff_less rb_valid_def)
  show "\<not> tail rb \<le> head rb \<Longrightarrow> CleanQ_RB.size rb - tail rb + head rb < CleanQ_RB.size rb" 
    using valid
    by (meson diff_less_mono2 less_diff_conv not_le_imp_less rb_valid_def)
qed

lemma rb_valid_invalid_entries_size:
  assumes valid: "rb_valid rb"
  shows "length (rb_valid_entries rb) + length (rb_invalid_entries rb) = size rb"
  unfolding rb_valid_def rb_valid_entries_def rb_invalid_entries_def
proof auto
  show "tail rb \<le> head rb \<Longrightarrow> head rb + (CleanQ_RB.size rb - head rb) = CleanQ_RB.size rb" 
    by (meson le_add_diff_inverse less_imp_le_nat rb_valid_def valid)

  show "\<not> tail rb \<le> head rb \<Longrightarrow> CleanQ_RB.size rb - tail rb + tail rb = CleanQ_RB.size rb" 
    by (meson diff_add less_le rb_valid_def valid)
qed

text \<open>
  All entries within the set of valid entries are defined.
\<close>

lemma rb_valid_entries_defined:
  assumes valid: "rb_valid rb"
  shows "\<forall>i \<in> set (rb_valid_entries rb). (ring rb) i \<noteq> None"
  using valid unfolding rb_valid_entries_def rb_valid_def
  by auto



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

definition rb_incr_tail_alt :: "'a CleanQ_RB \<Rightarrow> nat\<Rightarrow> 'a CleanQ_RB"
  where "rb_incr_tail_alt rb incr = rb \<lparr> tail := ((tail rb) + incr) mod (size rb) \<rparr>"
text \<open>
 We first show that the functions are in fact preserving the valid predicate.
\<close>

lemma rb_incr_head_valid:
  "rb_valid rb \<Longrightarrow> rb_valid (rb_incr_head rb)"
  unfolding rb_valid_def rb_incr_head_def by(simp)

lemma rb_incr_tail_valid:
  "rb_valid rb \<Longrightarrow> rb_valid (rb_incr_tail rb)"
  unfolding rb_valid_def rb_incr_tail_def by(simp)

lemma rb_incr_tail_alt_one_valid:
  shows "rb_valid rb \<Longrightarrow> rb_valid (rb_incr_tail_alt rb 1)"
  unfolding rb_valid_def rb_incr_tail_alt_def by simp

lemma rb_incr_tail_alt_delta_valid:
  assumes const_delta: "delta \<le> length (rb_valid_entries rb)" and 
          valid: "rb_valid rb"
  shows "rb_valid rb \<Longrightarrow> rb_valid (rb_incr_tail_alt rb delta)"
  unfolding rb_valid_def rb_incr_tail_alt_def
by simp

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
  where "rb_write b rb = rb \<lparr> ring := (ring rb)((head rb) := Some b) \<rparr>"


text \<open>
  we can define functions to read the entries of the ring buffer:
\<close>

definition rb_read :: "nat \<Rightarrow> 'a CleanQ_RB \<Rightarrow> 'a option"
  where "rb_read i rb = (ring rb) i"



definition rb_read_tail :: "'a CleanQ_RB \<Rightarrow> 'a"
  where "rb_read_tail rb = the (rb_read (tail rb) rb)"


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
  where "rb_enq_alt b rb = rb \<lparr> ring := (ring rb)((head rb) := Some b),
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
  "rb' = rb_enq b rb \<Longrightarrow> (ring (rb'))((head rb)) = Some b"
  by(simp add:rb_enq_equiv rb_enq_alt_def)

lemma rb_enq_buf_ring2 :
  "rb' = rb_enq b rb \<Longrightarrow> the ((ring (rb'))(head rb)) = b"
  by(simp add:rb_enq_equiv rb_enq_alt_def)

lemma rb_enq_buf:
 "rb' = rb_enq b rb \<Longrightarrow> rb_read (head rb) rb' = Some b"
  by (simp add: rb_enq_alt_def rb_enq_equiv rb_read_def)

lemma rb_enq_buf2:
 "rb' = rb_enq b rb \<Longrightarrow> the (rb_read (head rb) rb') = b"
  by (simp add: rb_enq_alt_def rb_enq_equiv rb_read_def)

lemma rb_enq_buf3:
  "rb_read (head rb) (rb_enq b rb) = Some b"
  by (simp add: rb_enq_alt_def rb_enq_equiv rb_read_def)

lemma rb_enq_buf4:
  "the (rb_read (head rb) (rb_enq b rb)) = b"
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
  where "rb_deq_alt rb = (the (rb_read (tail rb) rb),  
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

definition CleanQ_RB_list_opt :: "'a CleanQ_RB \<Rightarrow> ('a option) list"
  where "CleanQ_RB_list_opt rb = map (ring rb) (rb_valid_entries rb)"

definition CleanQ_RB_list :: "'a CleanQ_RB \<Rightarrow> 'a list"
  where "CleanQ_RB_list rb = map (the o ring rb) (rb_valid_entries rb)"

lemma rb_list_opt_elements_not_none:
  assumes valid : "rb_valid rb"
  shows "\<forall>e \<in> set (CleanQ_RB_list_opt rb). e \<noteq> None"
  unfolding CleanQ_RB_list_opt_def using valid rb_valid_entries_defined by(auto) 
 



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
  using notempty valid unfolding  CleanQ_RB_list_def res
  apply(simp add:rb_deq_alt_def rb_deq_equiv)
  by (simp add: rb_can_deq_def rb_incr_tail_valid_entries rb_read_def rb_valid_def)

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

(* ==================================================================================== *)
subsection \<open>Frame condition under concurrent operation of two sides\<close>
(* ==================================================================================== *)  

definition frame_rb_weak_left :: "'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB \<Rightarrow> bool"
  where "frame_rb_weak_left st' st \<longleftrightarrow>
    size st' = size st \<and>
    head st' = head st \<and>
    ring st' = ring st \<and>
    rb_valid st' \<and> rb_valid st \<and>
   (\<exists> \<delta>tl.
    (if (tail st') + \<delta>tl < (size st') then tail st' + \<delta>tl
     else (tail st') + \<delta>tl - (size st')) = tail st
  )" 

definition rb_delta_tail :: "'a CleanQ_RB \<Rightarrow> nat \<Rightarrow> nat list"
  where "rb_delta_tail rb delta = (if (tail rb + delta) < (size rb) then [(tail rb) ..< ((tail rb) + delta)]
                                   else [(tail rb)..< (size rb)] @ [0..< ((tail rb) + delta) mod (size rb)])"

lemma rb_delta_size_nonzero:
  fixes st' st 
  assumes frame: "frame_rb_weak_left st' st"
  shows "delta > 0 \<Longrightarrow> (rb_delta_tail st delta) \<noteq> []"
  using assms
  unfolding rb_delta_tail_def
by (simp add: frame_rb_weak_left_def rb_valid_def)

lemma rb_weak_list_delta_empty:
  fixes st' st 
  assumes frame: "frame_rb_weak_left st' st" and
          tl_asm:  "(tail st') + \<delta>tl = (tail st) \<and> \<delta>tl = 0"
  shows "tail st' = tail st \<Longrightarrow> rb_valid_entries st' = (rb_delta_tail st' \<delta>tl) @ (rb_valid_entries st)"
proof -
  from tl_asm have "\<delta>tl = 0" 
    by simp

  from tl_asm have tl: "tail st' = tail st"
    by simp

  from tl_asm have rb_delta: "rb_delta_tail st' \<delta>tl = rb_delta_tail st' 0" 
    unfolding rb_delta_tail_def 
    by auto

  from rb_delta have rb_delta_empty: "rb_delta_tail st' \<delta>tl = []"
    unfolding rb_delta_tail_def
    by (metis frame frame_rb_weak_left_def less_irrefl rb_valid_def tl tl_asm upt_rec)

  from rb_delta_empty have "rb_valid_entries st' = rb_valid_entries st"
    unfolding rb_valid_entries_def
    by (metis (no_types, hide_lams) frame frame_rb_weak_left_def tl)

  show ?thesis using rb_delta_empty
    by (simp add: \<open>rb_valid_entries st' = rb_valid_entries st\<close>)
qed

lemma rb_incr_tail_wrap:
  fixes rb
  assumes "rb_valid rb"
  shows "tail rb = (size rb -1) \<Longrightarrow> tail (rb_incr_tail_alt rb 1) = 0" 
  unfolding rb_incr_tail_alt_def
  by (metis assms le_add_diff_inverse2 less_imp_le_nat mod_self rb_valid_def select_convs(3) 
      surjective update_convs(3))

lemma rb_delta_one:
  fixes st st'
  assumes tail: "tail st = tail (rb_incr_tail_alt st' 1) \<and> head st = head st'"
  assumes valid: "rb_valid st'"
  shows "(rb_delta_tail st' 1) = [tail st']"
  unfolding rb_delta_tail_def rb_valid_def
proof auto
  have st_st_prime: "tail st' + 1 < CleanQ_RB.size st' \<Longrightarrow> (tail st' + 1) = tail st"
    using tail unfolding rb_incr_tail_alt_def
    by simp

  show "\<not> Suc (tail st') < CleanQ_RB.size st' \<Longrightarrow> [tail st'..<CleanQ_RB.size st'] @ [0..<Suc (tail st') mod CleanQ_RB.size st'] = [tail st']"
    by (metis Suc_lessI append.right_neutral mod_self rb_valid_def upt_0 upt_rec valid)
qed

lemma rb_delta_one_unfold:
  fixes st 
  assumes frame: "rb_valid st"
  assumes tl_hd: "(Suc (tail st)) \<le> head st" (* we can actually dequeue *)
  shows "[tail st..<head st] = tail st # [Suc (tail st) mod CleanQ_RB.size st..<head st]"
proof -
  from tl_hd frame have no_mod:"Suc (tail st) mod CleanQ_RB.size st = Suc (tail st)"
    by (metis Suc_lessI leD mod_less rb_valid_def)

  have core:"[Suc (tail st) mod CleanQ_RB.size st..<head st] = [Suc (tail st)..<head st]"
    using no_mod by auto 

  show ?thesis using core
    by (simp add: Suc_le_lessD tl_hd upt_conv_Cons)
qed

lemma rb_delta_one_tl_leq_hd:
  fixes st 
  assumes frame: "rb_valid st"
  assumes tl_hd: "tail st \<le> head st"
  assumes deq: "rb_can_deq st \<and> (tail st + 1) mod size st \<noteq> head st" (* we can actually dequeue *)
  shows "[tail st..<head st] = tail st # [Suc (tail st) mod CleanQ_RB.size st..<head st]"
  using rb_delta_one deq tl_hd frame unfolding rb_incr_tail_alt_def 
  by (metis Suc_leI le_less rb_can_deq_def rb_delta_one_unfold rb_empty_def)

(*
lemma rb_delta_one_tl_geq_hd:
  fixes st 
  assumes frame: "rb_valid st"
  assumes tl_hd: "tail st > head st"
  assumes deq: "rb_can_deq st \<and> (tail st + 1) mod size st \<noteq> head st" (* we can actually dequeue *)
  shows "[tail st..<size st] @ [0..< head st]  = tail st # [(Suc (tail st)) mod CleanQ_RB.size st..<size st] @ [0..< head st]"
  (* This seems to be wrong for the wrap around! Fix it!*)
  using rb_delta_one deq tl_hd frame unfolding rb_incr_tail_alt_def 
proof -

qed


lemma rb_weak_list_delta_one:
  fixes st' st 
  assumes frame: "frame_rb_weak_left st' st" and
          tail: "tail st = tail (rb_incr_tail_alt st' 1)" and
          deq: "rb_can_deq st'"
  shows  "rb_valid_entries st' = (rb_delta_tail st' 1) @ (rb_valid_entries st)"
  using rb_delta_one deq
proof -
  from frame tail have valid: "rb_valid st \<and> rb_valid st'"
    using frame_rb_weak_left_def by blast

  have delta: "rb_delta_tail st' (Suc 0) = [tail st']" using rb_delta_one frame tail
      unfolding frame_rb_weak_left_def by fastforce

  have tail_incr: "tail st = ((tail st' + 1) mod size st')" 
    using tail unfolding rb_incr_tail_alt_def by auto

  have head:"head st = head st'" using frame unfolding frame_rb_weak_left_def
    by simp

  have "rb_valid_entries st' = rb_delta_tail st' (Suc 0) @ rb_valid_entries st" 
    using tail_incr delta deq unfolding rb_delta_tail_def rb_valid_entries_def 
  proof auto
    from head have core1: "[tail st'..<head st'] = tail st' # [Suc (tail st') mod CleanQ_RB.size st'..<head st]" 
      using head valid rb_delta_one_unfold deq unfolding rb_can_deq_def apply simp 
      try



  qed



qed

*)


end