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
  In this theory, we define a ring buffer data structure. This forms a circular, bounded 
  list of buffer elements. As a consequence, the adding new elements to the data structure 
  or removing them may fail, because there is no more space in the ring buffer or it
  does not contain any elements.  
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
  from a nat, identifying the slot in the ring to maybe an element ('a option). This
  effectively forms a partial function which is only defined for elements within the 
  ring ($0..<size$) Head and tail define the valid elements in the ring.\<close>

record 'a CleanQ_RB =
  ring :: "nat \<Rightarrow> 'a option"
  head :: nat
  tail :: nat
  size :: nat


text \<open>
  The ring buffer has a certain set of valid entries. We now provide definitions to 
  create the list of entries which contain valid buffer elements. Note, this is not simply
  [(tail rb) ..<(head rb)]. As there might be a wrap around (e.g. head = 4 tail = 8). We 
  use the nonzero modulus locale to work out the elements.

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

text \<open>
  The list of valid and invalid entries are distinct.
\<close>

lemma rb_valid_entries_distinct:
  "distinct (rb_valid_entries rb)"
  unfolding rb_valid_entries_def by(auto)

lemma rb_invalid_entries_distinct:
  "distinct (rb_invalid_entries rb)"
  unfolding rb_invalid_entries_def by(auto)

text \<open>
  A ring buffer is valid if its head and tail pointers are within the size of the buffer,
  and the buffer needs a certain size. Note, we require the size of the ring to be at
  least 2. By using the head and tail pointers, we need to be able to distinguish 
  a full from an empty ring buffer. This requires to `give up' one element to always
  distinguish the full and empty conditions below. 

  Moreover, all slots in the ring, which are part of the valid entries must have a 
  defined content, i.e. are not \texttt+None+. 
\<close>

definition rb_valid :: "'a CleanQ_RB \<Rightarrow> bool"
  where "rb_valid rb \<longleftrightarrow> (head rb < size rb) \<and> (tail rb < size rb) \<and> (1 < size rb)
                           \<and> (\<forall>i \<in> set (rb_valid_entries rb). ring rb i \<noteq> None)"


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
  We can show that this is the same as taking the case distinction explicitly at the
  warp around:  
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
  Next we can show that the empty and full predicates imply the negation of each other
\<close>

lemma rb_full_not_empty:
  "rb_valid rb \<Longrightarrow> rb_full rb \<Longrightarrow> \<not> rb_empty rb"
  unfolding rb_valid_def rb_full_def rb_empty_def  
  by (metis One_nat_def Suc_eq_plus1 Suc_leI le_less mod_less mod_self n_not_Suc_n)

lemma rb_empty_not_full:
  "rb_valid rb \<Longrightarrow> rb_empty rb \<Longrightarrow> \<not> rb_full rb"
  by(simp add:rb_full_no_modulo rb_empty_def rb_valid_def)


(* ==================================================================================== *)
subsection \<open>Reasoning about valid entries\<close>
(* ==================================================================================== *)

text \<open>
  First, we can show that the union of the set of valid entries and invalid entries produce
  the set of entries from ${0..< size}$.
\<close>

lemma rb_valid_invalid_entries_set:
assumes valid: "rb_valid rb"
  shows "set (rb_valid_entries rb) \<union> set (rb_invalid_entries rb) = {0..<(size rb)}"
  using valid unfolding rb_valid_entries_def rb_invalid_entries_def rb_valid_def
  by auto


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>List and Set of Valid Entries\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  If the ring buffer is empty, then there are no valid entries, and thus the list of
  valid entries or the set thereof does not contain any elements. 
\<close>

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
  Similarly, if the ring buffer is empty, then the set of in valid entries
  is exactly the elements 0..<size. Note, this is not exactly the list [0..<size],
  but a permutation.
\<close>

lemma rb_invalid_entries_empty: 
  "rb_valid rb \<Longrightarrow> rb_empty rb \<Longrightarrow> set (rb_invalid_entries rb) = {0..< size rb}"
  unfolding rb_valid_def rb_empty_def rb_invalid_entries_def by(auto)


text \<open>
  If the ring buffer is not empty, then the list of valid entries is not empty.
\<close>

lemma rb_valid_entries_not_empty_list :
  "rb_valid rb \<Longrightarrow> \<not> rb_empty rb \<Longrightarrow> rb_valid_entries rb \<noteq> []"
   unfolding rb_empty_def rb_valid_entries_def rb_valid_def by(auto)

lemma rb_valid_entries_not_empty_list2 :
  "rb_valid rb \<Longrightarrow> \<not>rb_empty rb \<longleftrightarrow> rb_valid_entries rb \<noteq> []"
  unfolding rb_empty_def rb_valid_entries_def rb_valid_def by auto

lemma rb_valid_entries_not_empty_set :
  "rb_valid rb \<Longrightarrow> \<not>rb_empty rb \<Longrightarrow> set (rb_valid_entries rb) \<noteq> {}"
  using rb_valid_entries_not_empty_list by(auto)

text \<open>
  If the ring buffer is full, then the set of valid entries contains all slots but
  the head.
\<close>

lemma rb_valid_entries_full:
  "rb_valid rb \<Longrightarrow> rb_full rb \<Longrightarrow> set (rb_valid_entries rb) = {0..< size rb} - {head rb}"
  unfolding rb_valid_def rb_full_def rb_valid_entries_def
  apply(cases "tail rb \<le> head rb", simp_all)
  apply (metis (no_types, lifting) Diff_insert_absorb atLeast0_lessThan_Suc leD lessI 
                                   lessThan_atLeast0 lessThan_iff mod_Suc mod_if mod_self)
  using leD lessI lessThan_Suc lessThan_atLeast0 less_imp_le by fastforce



text \<open>
  Last we show that the number of valid entries is less than the size of the ring and
  the total number of valid and invalid entries is the size of the ring.
\<close>

lemma rb_valid_entries_less_size:
  "rb_valid rb \<Longrightarrow> length (rb_valid_entries rb) < size rb"
   unfolding rb_valid_def rb_valid_entries_def by(auto)

lemma rb_invalid_entries_less_size:
  "rb_valid rb \<Longrightarrow> length (rb_invalid_entries rb) \<le> size rb"
  unfolding rb_valid_def rb_invalid_entries_def by(auto)

lemma rb_valid_invalid_entries_size:
  "rb_valid rb \<Longrightarrow> length (rb_valid_entries rb) + length (rb_invalid_entries rb) = size rb"
  unfolding rb_valid_def rb_valid_entries_def rb_invalid_entries_def by(auto)

text \<open>
  We can express this as subset relations
\<close>

lemma rb_valid_entries_tail_subseteq:
  "set (tl (rb_valid_entries rb))  \<subseteq>  set ((rb_valid_entries rb))"
  by (metis list.set_sel(2) subsetI tl_Nil)

lemma rb_valid_entries_tail_subset:
  "rb_valid_entries rb \<noteq> [] \<Longrightarrow> set (tl (rb_valid_entries rb)) \<subset> set ((rb_valid_entries rb))"
  using list_set_hd_tl_subtract rb_valid_entries_distinct by fastforce

lemma rb_valid_entries_head_subseteq:
  "set (rb_valid_entries rb)  \<subseteq>  set ((rb_valid_entries rb) @ [x])"
  by(auto)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Head and Tail Elements\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We can now define lemmas to talk about the head and tail entries, and whether
  they are part of the valid entries. First, the head is never part of the set of
  valid entries, and always part of the st of invalid entries, in fact the first
  element thereof.
\<close>

lemma rb_valid_entries_head :
  "(head rb) \<notin> set (rb_valid_entries rb)"
  unfolding rb_valid_entries_def by(auto)

lemma rb_invalid_entries_head1 :
  "rb_valid rb \<Longrightarrow> head rb \<in> set (rb_invalid_entries rb)"
  unfolding rb_valid_def rb_invalid_entries_def by(auto)

lemma rb_invalid_entries_head2 :
  "rb_valid rb \<Longrightarrow> head rb = hd (rb_invalid_entries rb)"
  unfolding rb_valid_def rb_invalid_entries_def by(auto)


text \<open>
  Next, if the ring buffer is emtpy, then the tail is also not part of the set of
  valid entries. In fact, the set is the empty set.
\<close>

lemma rb_valid_entries_tail_empty1 :
  "rb_empty rb  \<Longrightarrow> (tail rb) \<notin> set (rb_valid_entries rb)"
  unfolding rb_empty_def rb_valid_entries_def by(simp)

lemma rb_valid_entries_tail_empty2 :
  "head rb = tail rb \<Longrightarrow> (tail rb) \<notin> set (rb_valid_entries rb)"
  using rb_valid_entries_tail_empty1 unfolding rb_empty_def by(auto)


text \<open>
  Finally, when the ring buffer is not empty then the tail is part of the set of 
  valid entries. The same applies if the ring buffer is full. 
\<close>

lemma rb_valid_entries_tail_not_empty1:
  "rb_valid rb \<Longrightarrow> \<not>rb_empty rb \<Longrightarrow> (tail rb) \<in> set (rb_valid_entries rb)"
  unfolding rb_valid_entries_def rb_valid_def rb_empty_def by(simp)

lemma rb_valid_entries_tail_not_empty2 :
  "rb_valid rb \<Longrightarrow> head rb \<noteq> tail rb \<Longrightarrow> (tail rb) \<in> set (rb_valid_entries rb)"
  using rb_valid_entries_tail_not_empty1 unfolding rb_empty_def by(auto)

lemma rb_valid_entries_tail_not_empty3:
  "rb_valid rb \<Longrightarrow> rb_full rb \<Longrightarrow> (tail rb) \<in> set (rb_valid_entries rb)"
  using rb_full_not_empty rb_valid_entries_tail_not_empty1 by(auto)



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
subsection \<open>Incrementing Tail and Head Pointers By One\<close>
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


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>The Ring is not Changed\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  First, the incrementing the head or tail pointers does not change the contents of 
  the ring. 
\<close>

lemma rb_incr_head_ring: 
  "(ring (rb_incr_head rb)) = ring rb"
  unfolding rb_incr_head_def by(auto)

lemma rb_incr_tail_ring: 
  "(ring (rb_incr_tail rb)) = ring rb"
  unfolding rb_incr_tail_def by(auto)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Incrementing the Tail Pointer\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  Incrementing the tail pointer reduces the list of valid entries by removing the head
  element from it. Thus the original list was the new list with the original tail pointer
  added:
\<close>

lemma rb_incr_tail_valid_entries:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid rb" 
  shows "rb_valid_entries rb = (tail rb) # rb_valid_entries (rb_incr_tail rb)"
  using notempty valid
  unfolding rb_valid_entries_def rb_incr_tail_def rb_empty_def rb_valid_def
  by (simp add: mod_Suc  upt_conv_Cons) 

text \<open>
  Rephrasing this, the new list of valid entries is the tail of the previous one.
\<close>

lemma rb_incr_tail_valid_entries_tail:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid rb"  
  shows "rb_valid_entries (rb_incr_tail rb) = tl (rb_valid_entries rb)"
  using valid notempty by (simp add:rb_incr_tail_valid_entries)


text\<open>
  The set of valid entries after the tail increment is a strict subset of the original
  set of valid entries.
\<close>

lemma rb_incr_tail_valid_entries_subset:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid rb"  
  shows "set (rb_valid_entries (rb_incr_tail rb)) \<subset> set (rb_valid_entries rb)"
  using notempty valid 
  by(simp add: rb_incr_tail_valid_entries_tail rb_valid_entries_not_empty_list 
               rb_valid_entries_tail_subset)


text \<open>
  When we increment the tail, then the original tail is no longer in the set of
  valid entries. The head here is the original tail pointer.
\<close>

lemma rb_incr_tail_valid_entries_notin1:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid rb" 
  shows "(tail rb) \<notin> set(rb_valid_entries (rb_incr_tail rb))"
  using notempty valid 
  apply(simp add:rb_incr_tail_valid_entries_tail)
  unfolding rb_valid_def rb_empty_def rb_valid_entries_def by(auto)

lemma rb_incr_tail_valid_entries_notin2:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid rb" 
  shows "hd (rb_valid_entries rb) \<notin> set (rb_valid_entries (rb_incr_tail rb))"
  using notempty valid rb_valid_entries_tail_first1 rb_incr_tail_valid_entries_notin1
  by fastforce

text \<open>
  Incrementing the tail pointer is preserving the validity invariant of the ring buffer
\<close>

lemma rb_incr_tail_valid:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid rb" 
shows "rb_valid (rb_incr_tail rb)"
  using valid apply(auto simp:rb_valid_def rb_incr_tail_def)
  by (metis Suc_eq_plus1 list.set_sel(2) list.simps(3) notempty rb_incr_tail_def 
            rb_incr_tail_valid_entries rb_incr_tail_valid_entries_tail valid)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Incrementing the Head Pointer\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open> 
  Incrementing the head then adds the current head pointer to the end of the  list of 
  valid entries,  and thus increasing the set of valid entries.
\<close>

lemma rb_incr_head_valid_entries:
assumes notfull: "\<not>rb_full rb"  and  valid: "rb_valid rb"  
  shows "rb_valid_entries (rb_incr_head rb) = (rb_valid_entries rb) @ [(head rb)]"
  using notfull valid 
  unfolding rb_valid_entries_def rb_incr_head_def rb_full_def rb_valid_def
  apply(simp add: mod_Suc upt_Suc_append  upt_conv_Cons, auto)
  by (metis le_imp_less_Suc upt_Suc_append upt_rec)


text \<open>
  By taking everything but the last element, we get the original list back. 
\<close>

lemma rb_incr_head_valid_entries_butlast:
assumes notfull: "\<not>rb_full rb"  and  valid: "rb_valid rb"  
  shows "(rb_valid_entries rb) = butlast (rb_valid_entries (rb_incr_head rb))"
  using notfull valid by (metis butlast_snoc rb_incr_head_valid_entries)


text \<open>
  The resulting set of valid entries is a strict super set of the original one.
\<close>

lemma rb_incr_head_valid_entries_superset:
assumes notempty: "\<not>rb_full rb"  and  valid: "rb_valid rb"  
  shows "set (rb_valid_entries rb) \<subset> set (rb_valid_entries (rb_incr_head rb))"
  using notempty valid 
  by(simp add:rb_incr_head_valid_entries psubset_insert_iff rb_valid_entries_head)


text \<open>
  The head element is added to the set of valid entries, in fact at the end of the
  list. 
\<close>
  
lemma rb_incr_head_valid_entries_last:
assumes notfull: "\<not> rb_full rb" and  valid: "rb_valid rb"  
  shows "head rb  = last (rb_valid_entries (rb_incr_head rb))"
  using notfull valid apply(subst rb_incr_head_valid_entries)
  by(auto)


text \<open>
  The original head pointer is now part of the set of valid entries.
\<close>

lemma rb_incr_head_valid_entries_headin:
assumes notfull: "\<not> rb_full rb" and  valid: "rb_valid rb"  
  shows "head rb \<in> set (rb_valid_entries (rb_incr_head rb))"
  using notfull valid apply(subst rb_incr_head_valid_entries)
  by(auto)

text \<open>
  Incrementing the head pointer preserves the validity invariant of the ring buffer.
  Note: we need to require that the element at the head of the ring is not None.
  In an enqueue operation this holds, as the element is written then the pointer updated.
\<close>

lemma rb_incr_head_valid:
assumes notfull: "\<not>rb_full rb"   and  valid: "rb_valid rb" 
  shows "(ring rb) (head rb) \<noteq> None \<Longrightarrow> rb_valid (rb_incr_head rb)"
  unfolding rb_valid_def
  apply(subst rb_incr_head_valid_entries)
  using valid by(auto simp:rb_valid_def rb_incr_head_def notfull)


(* ==================================================================================== *)
subsection \<open>Incrementing Tail and Head Pointers By N\<close>
(* ==================================================================================== *)


text \<open>
  In a concurrent setting, one side may increase the head or tail pointer several times
  before we actually see the update. We express this as an increment by n.
\<close>


definition rb_incr_head_n :: "nat \<Rightarrow> 'a CleanQ_RB \<Rightarrow>  'a CleanQ_RB"
  where "rb_incr_head_n n rb  = rb \<lparr> head := ((head rb) + n) mod (size rb) \<rparr>"

definition rb_incr_tail_n :: "nat \<Rightarrow> 'a CleanQ_RB \<Rightarrow>  'a CleanQ_RB"
  where "rb_incr_tail_n n rb  = rb \<lparr> tail := ((tail rb) + n) mod (size rb) \<rparr>"


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>The Ring is not Changed\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  Like with the single increment, the ring is not changed at all.
\<close>

lemma rb_incr_head_n_ring: 
  "(ring (rb_incr_head_n n rb)) = ring rb"
  unfolding rb_incr_head_n_def by(auto)

lemma rb_incr_tail_n_ring: 
  "(ring (rb_incr_tail_n n rb)) = ring rb"
  unfolding rb_incr_tail_n_def by(auto)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Increment by 0 or 1\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  Incrementing the head or tail pointer with 0 does not change the state of the ring.
  Note: it needs to be valid to ensure that the head or tail pointer is actually in 
  a valid range, otherwise the modulo operator will change the state.
\<close>

lemma rb_incr_head_0:
  "rb_valid rb \<Longrightarrow> rb_incr_head_n 0 rb = rb"
  unfolding rb_incr_head_n_def rb_incr_tail_def rb_valid_def by(auto)

lemma rb_incr_tail_0:
  "rb_valid rb \<Longrightarrow> rb_incr_tail_n 0 rb = rb"
  unfolding rb_incr_tail_n_def rb_incr_tail_def rb_valid_def by(auto)


text \<open>
  We can show that incremements to head and tail with N=1 are the same as the single
  increments above. 
\<close>

lemma rb_incr_head_1:
  "rb_incr_head_n 1 rb = rb_incr_head rb"
  unfolding rb_incr_head_n_def rb_incr_head_def by(auto)

lemma rb_incr_tail_1:
  "rb_incr_tail_n 1 rb = rb_incr_tail rb"
  unfolding rb_incr_tail_n_def rb_incr_tail_def by(auto)

text \<open>
  They also satisfy the validity constraints. As they are infact the same as above.
\<close>

lemma rb_incr_head_zero_valid:
  "rb_valid rb \<Longrightarrow> rb_valid (rb_incr_head_n 0 rb)"
  apply(subst rb_incr_head_0)
  by(auto)

lemma rb_incr_tail_zero_valid:
  "rb_valid rb \<Longrightarrow> rb_valid (rb_incr_tail_n 0 rb)"
  apply(subst rb_incr_tail_0)
  by(auto)  

lemma rb_incr_head_one_valid:
assumes notfull: "\<not>rb_full rb"  and  valid: "rb_valid rb" 
    and nextvalid: "(ring rb) (head rb) \<noteq> None"
shows "rb_valid rb \<Longrightarrow> rb_valid (rb_incr_head_n 1 rb)"
  apply(subst rb_incr_head_1)
  using rb_incr_head_valid notfull valid nextvalid by(simp)

lemma rb_incr_tail_one_valid:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid rb" 
shows "rb_valid rb \<Longrightarrow> rb_valid (rb_incr_tail_n 1 rb)"
  apply(subst rb_incr_tail_1)
  using notempty valid rb_incr_tail_valid  by(auto)



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>N-Fold Functional Composition\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We can show that this is just the functional composition of the \texttt+rb_incr_tail+.
\<close>

lemma rb_incr_tail_compow:
assumes valid: "rb_valid rb"
  shows "rb_incr_tail_n i rb = (rb_incr_tail ^^ i) rb"
proof (induct i)
  case 0
  then show ?case 
    using valid
    unfolding rb_incr_tail_n_def rb_incr_tail_def rb_valid_def by (auto)
next 
  fix i
  assume step: "rb_incr_tail_n i rb = (rb_incr_tail ^^ i) rb"

  have X1:
    "rb_incr_tail_n (Suc i) rb  =  rb_incr_tail_n i (rb_incr_tail rb)"
    apply(subst rb_incr_tail_1[symmetric])
    using valid unfolding rb_incr_tail_n_def rb_valid_def
    by (auto simp: add.commute mod_add_right_eq)

  have X2:
    " ... =  rb_incr_tail ((rb_incr_tail ^^ i) rb)"
    apply(simp add:step[symmetric])
    using valid unfolding rb_incr_tail_def rb_incr_tail_n_def rb_valid_def
    by (simp add: mod_Suc_eq mod_add_left_eq)
    
  show "rb_incr_tail_n  (Suc i) rb = (rb_incr_tail ^^ Suc i) rb"
    using X1 X2 by(auto simp add:funpow_Suc_right)
qed

lemma rb_incr_head_compow:
assumes valid: "rb_valid rb"
  shows "rb_incr_head_n i rb = (rb_incr_head ^^ i) rb"
proof (induct i)
  case 0
  then show ?case 
    using valid
    unfolding rb_incr_head_n_def rb_incr_head_def rb_valid_def by (auto)
next 
  fix i
  assume step: "rb_incr_head_n i rb = (rb_incr_head ^^ i) rb"

  have X1:
    "rb_incr_head_n (Suc i) rb  =  rb_incr_head_n i (rb_incr_head rb)"
    apply(subst rb_incr_head_1[symmetric])
    using valid unfolding rb_incr_head_n_def rb_valid_def
    by (auto simp: add.commute mod_add_right_eq)

  have X2:
    " ... =  rb_incr_head ((rb_incr_head ^^ i) rb)"
    apply(simp add:step[symmetric])
    using valid unfolding rb_incr_head_def rb_incr_head_n_def rb_valid_def
    by (simp add: mod_Suc_eq mod_add_left_eq)
    
  show "rb_incr_head_n  (Suc i) rb = (rb_incr_head ^^ Suc i) rb"
    using X1 X2 by(auto simp add:funpow_Suc_right)
qed



text \<open>
 We first show that the functions are in fact preserving the valid predicate.
\<close>



lemma 
assumes const_delta: "delta \<le> length (rb_valid_entries rb)"  and  valid: "rb_valid rb"
  shows "set (rb_valid_entries (rb_incr_tail_n delta rb)) \<subseteq> set (rb_valid_entries rb)"
  apply (cases "delta = 0")
   apply(simp add: rb_incr_tail_0 valid) 
  using const_delta valid  
  apply(subst rb_incr_tail_compow)
   apply(simp add:valid)
  
  using rb_valid_entries_distinct rb_incr_tail_valid_entries_subset valid const_delta
  
  oops
  

lemma rb_incr_tail_n_valid:
assumes const_delta: "delta \<le> length (rb_valid_entries rb)"  and  valid: "rb_valid rb"
    and notempty: "\<not>rb_empty rb"
  shows "rb_valid (rb_incr_tail_n delta rb)"
  unfolding rb_valid_def  rb_incr_tail_n_ring apply(auto) (* 4 goals *)
  using valid apply(simp add: rb_valid_def rb_incr_tail_n_def)
  using valid apply(simp add: rb_valid_def rb_incr_tail_n_def)
  using valid apply(simp add: rb_valid_def rb_incr_tail_n_def)
  using valid unfolding rb_valid_def
  using const_delta valid unfolding rb_valid_def rb_incr_tail_n_def
  apply(auto)
  oops
  
  

lemma rb_incr_tail_alt_delta_valid:
assumes const_delta: "delta \<le> length (rb_valid_entries rb)"  and  valid: "rb_valid rb"
    and notempty: "\<not>rb_empty rb"
  shows "rb_valid (rb_incr_tail_alt rb delta)"
  oops




(* ==================================================================================== *)
subsection \<open>Writing Entries in the Descriptor Ring\<close>
(* ==================================================================================== *)

text \<open>
  Writing an entry into the ring buffer then corresponds to a function update. The update
  always modifies the element at the head position.
\<close>

definition rb_write_head :: "'a \<Rightarrow> 'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB"
  where "rb_write_head b rb = rb \<lparr> ring := (ring rb)((head rb) := Some b) \<rparr>"


text \<open>
  we can define functions to read the entries of the ring buffer:
\<close>

definition rb_read_tail :: "'a CleanQ_RB \<Rightarrow> 'a"
  where "rb_read_tail rb = the (((ring rb) (tail rb)))"


text \<open>
  Writing an entry preserves the list of valid entries as well as the validity of
  the ring buffer, as the head / tail pointers are not changed.
\<close>

lemma rb_write_perserves_valid_entries:
  "rb_valid_entries rb = rb_valid_entries (rb_write_head b rb)"
  unfolding rb_write_head_def rb_valid_entries_def by(auto)

lemma rb_write_preserves_valid:
  "rb_valid rb \<Longrightarrow> rb_valid (rb_write_head b rb)"
  apply(auto simp: rb_valid_def rb_write_head_def)
  by (metis rb_write_head_def rb_write_perserves_valid_entries)
  
lemma rb_write_head_element_not_none:
assumes rw: "rb' = rb_write_head b rb"
 shows "  (ring rb') (head rb') \<noteq> None"
  using rw unfolding rb_write_head_def by(auto)

lemma rb_write_head_element:
assumes rw: "rb' = rb_write_head b rb"
 shows "  (ring rb') (head rb') = Some b"
  using rw unfolding rb_write_head_def by(auto)


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
  where "rb_enq b rb = rb_incr_head (rb_write_head b rb)"

text \<open>
  This is a function composition of the head increment and the write to the ring:
\<close>

definition rb_enq_fun :: "'a \<Rightarrow> 'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB" 
  where "rb_enq_fun b rb = ((rb_incr_head o rb_write_head b)) rb"

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
  unfolding rb_enq_alt_def rb_enq_def rb_incr_head_def rb_write_head_def by(auto)

lemma rb_enq_equiv_fun:
  "rb_enq b rb = rb_enq_fun b rb"
  unfolding rb_enq_fun_def rb_enq_def by(auto)


text \<open>
  The enqueue function preserves the validity predicate of the ring buffer. 
\<close>

lemma rb_enq_remains_valid:
assumes  valid: "rb_valid rb"  and  notfull: "rb_can_enq rb"
  shows "rb_valid (rb_enq b rb)"
  using valid rb_write_preserves_valid notfull rb_incr_head_valid rb_write_head_element_not_none
  unfolding rb_can_enq_def rb_enq_def
  by (metis ext_inject rb_full_def rb_write_head_def surjective update_convs(1))
  

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


(* 
lemma rb_enq_buf:
 "rb' = rb_enq b rb \<Longrightarrow> rb_read_tail (head rb) rb' = Some b"
  by (simp add: rb_enq_alt_def rb_enq_equiv rb_read_tail_def)

lemma rb_enq_buf2:
 "rb' = rb_enq b rb \<Longrightarrow> the (rb_read_tail (head rb) rb') = b"
  by (simp add: rb_enq_alt_def rb_enq_equiv rb_read_tail_def)

lemma rb_enq_buf3:
  "rb_read (head rb) (rb_enq b rb) = Some b"
  by (simp add: rb_enq_alt_def rb_enq_equiv rb_read_def)

lemma rb_enq_buf4:
  "the (rb_read (head rb) (rb_enq b rb)) = b"
  by (simp add: rb_enq_alt_def rb_enq_equiv rb_read_def)

*)

text \<open>
  Next we can talk about the effects on the set of valid entries in the ring buffer, 
  when we enqueue a new element to the ring buffer.
\<close>

lemma rb_enq_valid_entries_incr_head:
assumes notfull: "rb_can_enq rb" and valid: "rb_valid rb"  
shows "rb_valid_entries (rb_enq b rb) =  rb_valid_entries (rb_incr_head rb)"
  apply(subst rb_enq_equiv_fun)
  apply(subst rb_enq_fun_def)
  unfolding rb_write_head_def using notfull valid rb_write_perserves_valid_entries 
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
  by (simp add: rb_enq_def rb_incr_head_ring rb_valid_entries_head rb_write_head_def)


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
  where "rb_deq_alt rb = ( (rb_read_tail rb),  
                          rb \<lparr> tail := ((tail rb) + 1) mod (size rb) \<rparr> )"

text \<open>
  We can show that the two dequeue definitions produce the same outcome
\<close>

lemma rb_deq_equiv:
  "rb_deq rb = rb_deq_alt rb"
  unfolding rb_deq_def rb_deq_alt_def rb_read_tail_def rb_incr_tail_def rb_read_tail_def
  by(auto)
  
text \<open>
  The dequeue operation preserves the validity of the ring buffer.
\<close>

lemma rb_deq_remains_valid:
  assumes valid: "rb_valid rb" and notempty: "rb_can_deq rb"
  shows "rb_valid (snd (rb_deq rb))"
  unfolding rb_deq_def using rb_incr_tail_valid valid notempty rb_can_deq_def
  by(auto)
  

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
  using valid unfolding CleanQ_RB_list_opt_def rb_valid_def
  by(auto)


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
  by(simp add:rb_deq_alt_def rb_deq_equiv rb_can_deq_def rb_incr_tail_valid_entries 
              rb_read_tail_def)
  
  

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
  using valid notempty rb_can_deq_def rb_valid_entries_tail_not_empty1 by fastforce

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
  shows "tail rb = (size rb -1) \<Longrightarrow> tail (rb_incr_tail_n 1 rb) = 0" 
  unfolding rb_incr_tail_n_def
  by (metis assms le_add_diff_inverse2 less_imp_le_nat mod_self rb_valid_def select_convs(3) 
      surjective update_convs(3))

lemma rb_delta_one:
  fixes st st'
  assumes tail: "tail st = tail (rb_incr_tail_n 1 st') \<and> head st = head st'"
  assumes valid: "rb_valid st'"
  shows "(rb_delta_tail st' 1) = [tail st']"
  unfolding rb_delta_tail_def rb_valid_def
proof auto
  have st_st_prime: "tail st' + 1 < CleanQ_RB.size st' \<Longrightarrow> (tail st' + 1) = tail st"
    using tail unfolding rb_incr_tail_n_def
    by simp

  show "\<not> Suc (tail st') < CleanQ_RB.size st' \<Longrightarrow> [tail st'..<CleanQ_RB.size st'] @ [0..<Suc (tail st') mod CleanQ_RB.size st'] = [tail st']"
    by (metis Suc_lessI append.right_neutral mod_self rb_valid_def upt_0 upt_rec valid)
qed

lemma rb_delta_one_tl_leq_hd:
  fixes st 
  assumes frame: "rb_valid st"
  assumes tl_hd: "tail st \<le> head st"
  assumes deq: "rb_can_deq st" (* we can actually dequeue *)
  shows "[tail st..<head st] = tail st # [(Suc (tail st) mod (CleanQ_RB.size st))..<head st]"
  using rb_delta_one deq tl_hd frame deq unfolding rb_incr_tail_n_def 
  by (metis Suc_leI le_antisym mod_less not_less rb_can_deq_def rb_empty_def rb_valid_def upt_rec)


lemma rb_delta_one_tl_geq_hd:
  fixes st 
  assumes frame: "rb_valid st"
  assumes tl_hd: "tail st \<ge> head st"
  assumes deq: "rb_can_deq st" (* we can actually dequeue *)
  shows "[tail st..<size st] @ [0..< head st]  = tail st # [(Suc (tail st))..<size st] @ [0..< head st]"
  using rb_delta_one deq tl_hd frame unfolding rb_incr_tail_n_def 
  using mod_Suc rb_valid_def upt_rec
  by fastforce

lemma rb_weak_list_delta_one:
  fixes st' st 
  assumes frame: "frame_rb_weak_left st' st" and
          tail: "tail st = tail (rb_incr_tail_n 1 st')" and
          deq: "rb_can_deq st'"
  shows  "rb_valid_entries st' = (rb_delta_tail st' 1) @ (rb_valid_entries st)"
  using rb_delta_one deq
proof -
  from frame tail have valid: "rb_valid st \<and> rb_valid st'"
    using frame_rb_weak_left_def by blast

  have delta: "rb_delta_tail st' (Suc 0) = [tail st']" using rb_delta_one frame tail
      unfolding frame_rb_weak_left_def by fastforce

  have tail_incr: "tail st = ((tail st' + 1) mod size st')" 
    using tail unfolding rb_incr_tail_n_def by auto

  have head:"head st = head st'" using frame unfolding frame_rb_weak_left_def
    by simp

  show ?thesis 
    unfolding rb_delta_tail_def rb_valid_entries_def
    using tail_incr valid rb_delta_one_tl_leq_hd rb_delta_one_tl_geq_hd 
    unfolding rb_incr_tail_n_def
    apply simp
  proof -
    assume a1: "rb_valid st \<and> rb_valid st'"
    assume "tail st = Suc (tail st') mod CleanQ_RB.size st'"
    have f2: "head st = head st'"
      by (metis frame frame_rb_weak_left_def)
    have "CleanQ_RB.size st = CleanQ_RB.size st'"
      by (metis frame frame_rb_weak_left_def)
    then show "(Suc (tail st') < CleanQ_RB.size st' \<longrightarrow> (Suc (tail st') \<le> head st \<longrightarrow> 
               (tail st' \<le> head st' \<longrightarrow> [tail st'..<head st'] = tail st' # [Suc (tail st')..<head st]) \<and> 
               (\<not> tail st' \<le> head st' \<longrightarrow> [tail st'..<CleanQ_RB.size st'] @ [0..<head st'] = tail st' # [Suc (tail st')..<head st])) \<and> 
               (\<not> Suc (tail st') \<le> head st \<longrightarrow> (tail st' \<le> head st' \<longrightarrow> [tail st'..<head st'] = tail st' # [Suc (tail st')..<CleanQ_RB.size st] @ [0..<head st]) \<and> 
               (\<not> tail st' \<le> head st' \<longrightarrow> [tail st'..<CleanQ_RB.size st'] @ [0..<head st'] = tail st' # [Suc (tail st')..<CleanQ_RB.size st] @ [0..<head st]))) \<and> 
               (\<not> Suc (tail st') < CleanQ_RB.size st' \<longrightarrow> (Suc (tail st') mod CleanQ_RB.size st' \<le> head st \<longrightarrow> (tail st' \<le> head st' \<longrightarrow> [tail st'..<head st'] = 
               [tail st'..<CleanQ_RB.size st'] @ [0..<Suc (tail st') mod CleanQ_RB.size st'] @ [Suc (tail st') mod CleanQ_RB.size st'..<head st]) \<and> 
               (\<not> tail st' \<le> head st' \<longrightarrow> [0..<head st'] = [0..<Suc (tail st') mod CleanQ_RB.size st'] @ [Suc (tail st') mod CleanQ_RB.size st'..<head st])) \<and> 
               (\<not> Suc (tail st') mod CleanQ_RB.size st' \<le> head st \<longrightarrow> (tail st' \<le> head st' \<longrightarrow> [tail st'..<head st'] = 
               [tail st'..<CleanQ_RB.size st'] @ [0..<Suc (tail st') mod CleanQ_RB.size st'] @ [Suc (tail st') mod CleanQ_RB.size st'..<CleanQ_RB.size st] @ [0..<head st]) \<and> 
               (\<not> tail st' \<le> head st' \<longrightarrow> [0..<head st'] = [0..<Suc (tail st') mod CleanQ_RB.size st'] @ [Suc (tail st') mod CleanQ_RB.size st'..<CleanQ_RB.size st] @ [0..<head st])))"
      using f2 a1 by (metis (no_types) Suc_leD append.simps(1) append_Cons deq le_add2 le_add_same_cancel2 
                      le_antisym mod_self not_le not_less_eq_eq rb_can_deq_def rb_empty_def rb_valid_def upt_0 upt_conv_Cons)
  qed
qed

text \<open>
  Similar proofs but for delta larger than 1: TODO
\<close>

end