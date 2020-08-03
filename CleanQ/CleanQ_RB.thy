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

definition rb_valid_ptr :: "'a CleanQ_RB \<Rightarrow> bool"
  where "rb_valid_ptr rb \<longleftrightarrow> (head rb < size rb) \<and> (tail rb < size rb) \<and> (1 < size rb)"


definition rb_valid :: "'a CleanQ_RB \<Rightarrow> bool"
  where "rb_valid rb \<longleftrightarrow> rb_valid_ptr rb
                                 \<and> (\<forall>i \<in> set (rb_valid_entries rb). ring rb i \<noteq> None)"

lemma rb_valid_implies_ptr_valid:
  "rb_valid rb \<Longrightarrow> rb_valid_ptr rb"
  unfolding rb_valid_def by(auto)


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
assumes valid: "rb_valid_ptr rb"
  shows "rb_full rb \<longleftrightarrow> (if (head rb) + 1 = size rb  then tail rb = 0
                         else tail rb = head rb + 1)"
  using valid unfolding rb_full_def rb_valid_ptr_def by(auto)


text \<open>
  Likewise, the ring buffer is empty, if its head and tail pointers are equal. 
\<close>

definition rb_empty :: "'a CleanQ_RB \<Rightarrow> bool"
  where "rb_empty rb = ((head rb) = (tail rb))"

text \<open>
  Next we can show that the empty and full predicates imply the negation of each other
\<close>

lemma rb_full_not_empty:
  "rb_valid_ptr rb \<Longrightarrow> rb_full rb \<Longrightarrow> \<not> rb_empty rb"
  unfolding rb_valid_ptr_def rb_full_def rb_empty_def  
  by (metis One_nat_def Suc_eq_plus1 Suc_leI le_less mod_less mod_self n_not_Suc_n)

lemma rb_empty_not_full:
  "rb_valid_ptr rb \<Longrightarrow> rb_empty rb \<Longrightarrow> \<not> rb_full rb"
  by(simp add:rb_full_no_modulo rb_empty_def rb_valid_ptr_def)


(* ==================================================================================== *)
subsection \<open>Reasoning about valid entries\<close>
(* ==================================================================================== *)

text \<open>
  First, we can show that the union of the set of valid entries and invalid entries produce
  the set of entries from ${0..< size}$. We can further show, that the two sets have an 
  empty intersection, as both are distinct from one another. 
\<close>

lemma rb_valid_invalid_entries_union:
assumes valid: "rb_valid_ptr rb"
  shows "set (rb_valid_entries rb) \<union> set (rb_invalid_entries rb) = {0..<(size rb)}"
  using valid unfolding rb_valid_entries_def rb_invalid_entries_def rb_valid_ptr_def
  by auto

lemma rb_valid_invalid_entries_inter:
  "set (rb_valid_entries rb) \<inter> set (rb_invalid_entries rb) = {}"
  unfolding rb_valid_entries_def rb_invalid_entries_def
  by auto

text \<open>
  Taking the set difference between the set of all entries and the valid or invalid
  set we can obtain the respective other set.
\<close>

lemma rb_valid_invalid_entries_diff1:
assumes valid: "rb_valid_ptr rb"
  shows "set (rb_valid_entries rb) = {0..<(size rb)} - set (rb_invalid_entries rb)"
  using rb_valid_invalid_entries_union rb_valid_invalid_entries_inter valid by blast


lemma rb_valid_invalid_entries_diff2:
assumes valid: "rb_valid_ptr rb"
  shows "set (rb_invalid_entries rb) = {0..<(size rb)} - set (rb_valid_entries rb)"
  using rb_valid_invalid_entries_union rb_valid_invalid_entries_inter valid by blast


text \<open>
  The length of the lists sums up to the number of entries.
\<close>

lemma rb_valid_invalid_entries_lengths:
assumes valid: "rb_valid_ptr rb"
  shows "length (rb_valid_entries rb) + length (rb_invalid_entries rb) = (size rb)"
  using valid unfolding rb_valid_entries_def rb_invalid_entries_def rb_valid_ptr_def
  by(auto)

lemma rb_valid_invalid_entries_lengths2:
assumes valid: "rb_valid_ptr rb"
  shows "length (rb_valid_entries rb) + length (rb_invalid_entries rb) = length [0..< size rb]"
  using valid unfolding rb_valid_entries_def rb_invalid_entries_def rb_valid_ptr_def
  by(auto)


text \<open>
  Therefore, an element that is in the valid or invalid entries, cannot be part
  of the invalid or valid entries respectively.
\<close>

lemma rb_valid_entries_notin_invalid:
  "a \<in> set (rb_valid_entries rb) \<Longrightarrow> a \<notin> set (rb_invalid_entries rb)"
  using rb_valid_invalid_entries_inter by blast

lemma rb_inalid_entries_notin_valid:
  "a \<in> set (rb_invalid_entries rb) \<Longrightarrow> a \<notin> set (rb_valid_entries rb)"
  using  rb_valid_invalid_entries_inter by blast



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>List and Set of Valid Entries\<close>
(* ------------------------------------------------------------------------------------ *)


lemma rb_invalid_entries_never_empty_list :
  "rb_valid_ptr rb \<Longrightarrow> rb_invalid_entries rb \<noteq> []"
   unfolding rb_valid_ptr_def rb_invalid_entries_def by(simp)


text \<open>
  If the ring buffer is empty, then there are no valid entries, and thus the list of
  valid entries or the set thereof does not contain any elements. 
\<close>

lemma rb_valid_entries_empty_list :
  "rb_empty rb \<Longrightarrow> rb_valid_entries rb = []"
   unfolding rb_empty_def rb_valid_entries_def by(simp)

lemma rb_valid_entries_empty_list2 :
  "rb_valid_ptr rb \<Longrightarrow> rb_empty rb \<longleftrightarrow> rb_valid_entries rb = []"
   unfolding rb_empty_def rb_valid_entries_def rb_valid_ptr_def by(auto)

lemma rb_valid_entries_empty_list_length:
  "rb_valid_ptr rb \<Longrightarrow> length (rb_valid_entries rb) = 0 \<longleftrightarrow> rb_empty rb"
  apply(subst rb_valid_entries_empty_list2)
  by(auto)

lemma rb_valid_entries_empty_set :
  "rb_empty rb \<Longrightarrow> set (rb_valid_entries rb) = {}"
   unfolding rb_empty_def rb_valid_entries_def by(simp)

lemma rb_valid_entries_empty_set2 :
  "rb_valid_ptr rb \<Longrightarrow> rb_empty rb \<longleftrightarrow> set (rb_valid_entries rb) = {}"
  unfolding rb_empty_def rb_valid_entries_def rb_valid_ptr_def by(auto)


text \<open>
  Similarly, if the ring buffer is empty, then the set of in valid entries
  is exactly the elements 0..<size. Note, this is not exactly the list [0..<size],
  but a permutation.
\<close>

lemma rb_invalid_entries_empty: 
  "rb_valid_ptr rb \<Longrightarrow> rb_empty rb \<Longrightarrow> set (rb_invalid_entries rb) = {0..< size rb}"
  unfolding rb_valid_ptr_def rb_empty_def rb_invalid_entries_def by(auto)

lemma rb_invalid_entries_empty2: 
  "rb_valid_ptr rb \<Longrightarrow> rb_empty rb \<longleftrightarrow> set (rb_invalid_entries rb) = {0..< size rb}"
  using rb_valid_invalid_entries_inter rb_valid_invalid_entries_union
  by (metis inf_sup_absorb rb_invalid_entries_empty rb_valid_entries_empty_set2)


text \<open>
  If the ring buffer is not empty, then the list of valid entries is not empty.
\<close>

lemma rb_valid_entries_not_empty_list :
  "rb_valid_ptr rb \<Longrightarrow> \<not>rb_empty rb \<longleftrightarrow> rb_valid_entries rb \<noteq> []"
  unfolding rb_empty_def rb_valid_entries_def rb_valid_ptr_def by auto

lemma rb_valid_entries_not_empty_set :
  "rb_valid_ptr rb \<Longrightarrow> \<not>rb_empty rb \<longleftrightarrow> set (rb_valid_entries rb) \<noteq> {}"
  using rb_valid_entries_not_empty_list by(auto)


text \<open>
  If the ring buffer is full, then the set of valid entries contains all slots but
  the head.
\<close>

lemma rb_invalid_entries_full:
  "rb_valid_ptr rb \<Longrightarrow> rb_full rb \<longleftrightarrow> rb_invalid_entries rb = [head rb]"
  unfolding rb_invalid_entries_def rb_full_def 
  by (simp add: le_Suc_eq not_less rb_valid_ptr_def upt_rec)

lemma rb_invalid_entries_full2:
  "rb_valid_ptr rb \<Longrightarrow> rb_full rb \<Longrightarrow> rb_invalid_entries rb = [head rb]"
  unfolding rb_invalid_entries_def rb_full_def 
  by (metis rb_full_def rb_invalid_entries_def rb_invalid_entries_full)

lemma rb_valid_entries_full2:
  "rb_valid_ptr rb \<Longrightarrow> rb_full rb \<Longrightarrow> set (rb_valid_entries rb) = {0..< size rb} - {head rb}"
  apply(subst rb_valid_invalid_entries_diff1, simp)
  apply(subst rb_invalid_entries_full2, auto)
  done

lemma rb_valid_entries_full:
  "rb_valid_ptr rb \<Longrightarrow> rb_full rb \<longleftrightarrow> set (rb_valid_entries rb) = {0..< size rb} - {head rb}"
  apply(rule iffI, simp add:rb_valid_entries_full2)
proof -
  assume p1: "rb_valid_ptr rb"
  assume p2: "set (rb_valid_entries rb) = {0..<CleanQ_RB.size rb} - {head rb}"

  have X0:
    "{0..<CleanQ_RB.size rb} - {head rb} = {0..< (head rb)} \<union> {((head rb) + 1)..< size rb}"
    using p1 unfolding rb_valid_ptr_def by(auto)

  have X1:
    "{tail rb..<CleanQ_RB.size rb} = {Suc (head rb)..<CleanQ_RB.size rb}
       \<Longrightarrow> tail rb = Suc (head rb)"
    by (metis atLeastLessThan_empty_iff atLeastLessThan_inj(1) p1 rb_valid_ptr_def)

  have inter0: "tail rb > head rb \<Longrightarrow> {0..<head rb} \<inter> {tail rb..<CleanQ_RB.size rb} = {}"
    by(simp)
  have inter1: "{0..<head rb} \<inter> {Suc (head rb)..<CleanQ_RB.size rb} = {}"
    by simp

  from inter0 inter1 have X2:
    "tail rb > head rb
      \<Longrightarrow> {0..<head rb} \<union> {tail rb..<size rb} = {0..<head rb} \<union> {Suc (head rb)..<size rb} 
      \<Longrightarrow> {tail rb..<size rb} = {Suc (head rb)..<size rb} "
    by blast

  have X3:
    " \<not> tail rb \<le> head rb \<longleftrightarrow> tail rb > head rb"
    by(auto)

  have eq: "(head rb + 1) mod CleanQ_RB.size rb = tail rb"
    using p1 p2 unfolding X0  rb_valid_entries_def 
    apply(cases "tail rb \<le> head rb", simp_all add:rb_valid_ptr_def)
    apply (metis atLeastLessThan_empty atLeast_eq_iff ivl_disj_un_one(8) ivl_subset le0 
                 leD le_SucE mod_Suc mod_if  sup.cobounded2 sup_commute)
    apply (metis X1 X2 X3 sup_commute)
    done
 
  show "rb_full rb"
    using eq by(simp add:rb_full_def)
qed



text \<open>
  Last we show that the number of valid entries is less than the size of the ring and
  the total number of valid and invalid entries is the size of the ring.
\<close>

lemma rb_valid_entries_less_size:
  "rb_valid_ptr rb \<Longrightarrow> length (rb_valid_entries rb) < size rb"
  unfolding rb_valid_ptr_def rb_valid_entries_def  by(auto)

lemma rb_valid_entries_gt_zero:
  "length (rb_valid_entries rb) \<ge> 0"
   by(auto)

lemma rb_valid_entries_full_num:
  "rb_valid_ptr rb \<Longrightarrow> rb_full rb \<longleftrightarrow> length (rb_valid_entries rb) = size rb - 1"
  apply(rule iffI)
  using rb_invalid_entries_full rb_valid_invalid_entries_lengths apply fastforce
  unfolding rb_valid_entries_def rb_valid_ptr_def rb_full_def
  apply(cases " tail rb \<le> head rb ", auto)
  by (smt One_nat_def Suc_le_eq diff_0_eq_0 diff_Suc_1 diff_commute diff_diff_cancel 
          le_add_diff_inverse2 le_less mod_self)

lemma rb_valid_entries_empty_num:
  "rb_valid_ptr rb \<Longrightarrow> rb_empty rb \<longleftrightarrow> length (rb_valid_entries rb) = 0"
  using rb_valid_entries_empty_list rb_valid_invalid_entries_lengths
        rb_valid_entries_empty_list_length
  by auto

lemma rb_valid_entries_not_full_num:
  "rb_valid_ptr rb \<Longrightarrow> \<not> rb_full rb \<longleftrightarrow> length (rb_valid_entries rb) < size rb - 1"
  using rb_valid_entries_full_num rb_valid_entries_less_size by fastforce

lemma rb_valid_entries_not_empty_num:
  "rb_valid_ptr rb \<Longrightarrow> \<not>rb_empty rb \<longleftrightarrow> length (rb_valid_entries rb) > 0"
  using less_le rb_valid_entries_empty_list_length by fastforce

lemma rb_invalid_entries_less_size:
  "rb_valid_ptr rb \<Longrightarrow> length (rb_invalid_entries rb) \<le> size rb"
  unfolding rb_valid_ptr_def rb_invalid_entries_def by(auto)

lemma rb_invalid_entries_gt_zero:
  "rb_valid_ptr rb \<Longrightarrow> length (rb_invalid_entries rb) > 0"
  unfolding rb_valid_ptr_def rb_invalid_entries_def by(auto)

lemma rb_invalid_entries_full_num:
  "rb_valid_ptr rb \<Longrightarrow> rb_full rb \<longleftrightarrow> length (rb_invalid_entries rb) = 1"
  using rb_invalid_entries_full rb_valid_entries_full_num rb_valid_invalid_entries_lengths 
  by fastforce
  

lemma rb_invalid_entries_empty_num:
  "rb_valid_ptr rb \<Longrightarrow> rb_empty rb \<longleftrightarrow> length (rb_invalid_entries rb) = size rb"
  using rb_valid_entries_empty_list rb_valid_invalid_entries_lengths 
  using rb_valid_entries_empty_list_length by fastforce

lemma rb_invalid_entries_not_full_num:
  "rb_valid_ptr rb \<Longrightarrow> \<not> rb_full rb \<longleftrightarrow> length (rb_invalid_entries rb) > 1"
  apply(auto simp:rb_valid_ptr_def rb_full_def rb_invalid_entries_def)
  using less_diff_conv nat_neq_iff apply fastforce
  by (metis Nat.add_0_right Suc_lessI less_Suc_eq_le less_diff_conv less_irrefl_nat 
            mod_if mod_self plus_1_eq_Suc)

lemma rb_invalid_entries_not_empty_num:
  "rb_valid_ptr rb \<Longrightarrow> \<not>rb_empty rb \<longleftrightarrow> length (rb_invalid_entries rb) < size rb"
  using less_le rb_valid_entries_empty_list_length rb_valid_invalid_entries_lengths by fastforce

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
  "rb_valid_ptr rb \<Longrightarrow> head rb \<in> set (rb_invalid_entries rb)"
  unfolding rb_valid_ptr_def rb_invalid_entries_def by(auto)

lemma rb_invalid_entries_head2 :
  "rb_valid_ptr rb \<Longrightarrow> head rb = hd (rb_invalid_entries rb)"
  unfolding rb_valid_ptr_def rb_invalid_entries_def by(auto)

text \<open>
  Next, if the ring buffer is emtpy, then the tail is also not part of the set of
  valid entries. In fact, the set is the empty set.
\<close>

lemma rb_valid_entries_tail_empty1 :
  "rb_valid_ptr rb \<Longrightarrow> rb_empty rb  \<longleftrightarrow> (tail rb) \<notin> set (rb_valid_entries rb)"
  unfolding rb_empty_def rb_valid_entries_def rb_valid_ptr_def
  by(auto)
  
lemma rb_valid_entries_tail_empty2 :
  "rb_valid_ptr rb \<Longrightarrow> head rb = tail rb \<longleftrightarrow> (tail rb) \<notin> set (rb_valid_entries rb)"
  using rb_valid_entries_tail_empty1 unfolding rb_empty_def by(auto)

lemma rb_invalid_entries_tail_empty1 :
  "rb_valid_ptr rb \<Longrightarrow> rb_empty rb \<longleftrightarrow> (tail rb) \<in> set (rb_invalid_entries rb)"
  unfolding rb_empty_def rb_invalid_entries_def
  by (simp add: rb_valid_ptr_def)

lemma rb_invalid_entries_tail_empty2 :
  "rb_valid_ptr rb \<Longrightarrow> head rb = tail rb \<longleftrightarrow> (tail rb) \<in> set (rb_invalid_entries rb)"
  using rb_invalid_entries_tail_empty1 unfolding rb_empty_def by(auto)


text \<open>
  Finally, when the ring buffer is not empty then the tail is part of the set of 
  valid entries, and not part of the invalid entries.
   The same applies if the ring buffer is full. 
\<close>

lemma rb_valid_entries_tail_not_empty1:
  "rb_valid_ptr rb \<Longrightarrow> \<not>rb_empty rb \<longleftrightarrow> (tail rb) \<in> set (rb_valid_entries rb)"
  unfolding rb_valid_entries_def rb_valid_ptr_def rb_empty_def  by auto

lemma rb_valid_entries_tail_not_empty2 :
  "rb_valid_ptr rb \<Longrightarrow> head rb \<noteq> tail rb \<longleftrightarrow> (tail rb) \<in> set (rb_valid_entries rb)"
  using rb_valid_entries_tail_not_empty1 unfolding rb_empty_def by(auto)

lemma rb_valid_entries_tail_not_empty3:
  "rb_valid_ptr rb \<Longrightarrow> rb_full rb \<Longrightarrow> (tail rb) \<in> set (rb_valid_entries rb)"
  using rb_full_not_empty rb_valid_entries_tail_not_empty1 
  by blast

lemma rb_invalid_entries_tail_not_empty1:
  "rb_valid_ptr rb \<Longrightarrow> \<not>rb_empty rb \<longleftrightarrow> (tail rb) \<notin> set (rb_invalid_entries rb)"
  unfolding rb_invalid_entries_def rb_valid_ptr_def rb_empty_def 
  by (simp add: rb_invalid_entries_def)


lemma rb_invalid_entries_tail_not_empty2:
  "rb_valid_ptr rb \<Longrightarrow>  head rb \<noteq> tail rb \<longleftrightarrow> (tail rb) \<notin> set (rb_invalid_entries rb)"
  unfolding rb_invalid_entries_def rb_valid_ptr_def rb_empty_def by(simp)

lemma rb_invalid_entries_tail_not_empty3:
  "rb_valid_ptr rb \<Longrightarrow> rb_full rb \<Longrightarrow> (tail rb) \<notin> set (rb_invalid_entries rb)"
  using rb_full_not_empty rb_invalid_entries_tail_not_empty1 by(auto)


text \<open>
  Moreover, we can show that if there are valid elements in the ring buffer, 
  then the tail is the first element (head) of the list of valid entries.
\<close>

lemma rb_valid_entries_tail_first1:
  "rb_valid_ptr rb \<Longrightarrow> \<not>rb_empty rb \<Longrightarrow>(tail rb) = hd (rb_valid_entries rb)"
  unfolding rb_valid_ptr_def rb_empty_def rb_valid_entries_def by(auto)

lemma rb_valid_entries_tail_first2:
  "rb_valid_ptr rb \<Longrightarrow> rb_full rb \<Longrightarrow> (tail rb) = hd (rb_valid_entries rb)"
  using rb_full_not_empty rb_valid_entries_tail_first1 by(auto)

lemma rb_valid_entries_tail_first3:
  "rb_valid_entries rb \<noteq> [] \<Longrightarrow> (tail rb) = hd (rb_valid_entries rb) \<Longrightarrow> \<not>rb_empty rb "
  unfolding rb_empty_def rb_valid_entries_def by(auto)


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
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid_ptr rb" 
  shows "rb_valid_entries rb = (tail rb) # rb_valid_entries (rb_incr_tail rb)"
  using notempty valid
  unfolding rb_valid_entries_def rb_incr_tail_def rb_empty_def rb_valid_ptr_def
  by (simp add: mod_Suc  upt_conv_Cons) 

text \<open>
  Rephrasing this, the new list of valid entries is the tail of the previous one.
\<close>

lemma rb_incr_tail_valid_entries_tail:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid_ptr rb"  
  shows "rb_valid_entries (rb_incr_tail rb) = tl (rb_valid_entries rb)"
  using valid notempty by (simp add:rb_incr_tail_valid_entries)

lemma rb_incr_tail_valid_entries_drop:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid_ptr rb"  
  shows "rb_valid_entries (rb_incr_tail rb) = drop 1 (rb_valid_entries rb)"
  using valid notempty by (simp add:rb_incr_tail_valid_entries)

text \<open>
  Likewise, the set of invalid entries is being extended by the previous tail pointer
\<close>

lemma rb_incr_tail_invalid_entries:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid_ptr rb" 
  shows "rb_invalid_entries (rb_incr_tail rb) = rb_invalid_entries rb @ [tail rb]"
  using notempty valid mod_Suc
  unfolding rb_incr_tail_def rb_invalid_entries_def rb_empty_def rb_valid_ptr_def
  by (auto, metis less_Suc_eq_le upt_Suc)



text\<open>
  The set of valid entries after the tail increment is a strict subset of the original
  set of valid entries. Likewise, the set of invalid entries is a strict super set
  thereof. 
\<close>

lemma rb_incr_tail_valid_entries_subset:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid_ptr rb"  
  shows "set (rb_valid_entries (rb_incr_tail rb)) \<subset> set (rb_valid_entries rb)"
  using notempty valid 
  by(simp add: rb_incr_tail_valid_entries_tail rb_valid_entries_not_empty_list 
               rb_valid_entries_tail_subset)

lemma rb_incr_tail_invalid_entries_superset:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid_ptr rb"  
  shows "set (rb_invalid_entries rb) \<subset> set (rb_invalid_entries (rb_incr_tail rb))"
  apply(subst rb_incr_tail_invalid_entries)
  using notempty valid rb_invalid_entries_distinct rb_invalid_entries_tail_not_empty1
  by auto


text \<open>
  The length of the list of valid entries decrements by one when the tail pointer is
  increased. And vice versa, the length list of invalid entries is increased by one. 
\<close>

lemma rb_incr_tail_valid_entries_length1:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid_ptr rb"  
shows "length (rb_valid_entries (rb_incr_tail rb)) + 1 = length (rb_valid_entries rb)"
  apply(subst rb_incr_tail_valid_entries_tail)
  apply(simp_all add:notempty valid)
  using notempty valid rb_valid_entries_not_empty_list 
  by fastforce

lemma rb_incr_tail_valid_entries_length2:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid_ptr rb"  
shows "length (rb_valid_entries (rb_incr_tail rb)) = length (rb_valid_entries rb) - 1"
  using notempty valid rb_incr_tail_valid_entries_length1 
  by fastforce

lemma rb_incr_tail_invalid_entries_length:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid_ptr rb"  
shows "length (rb_invalid_entries (rb_incr_tail rb)) = length (rb_invalid_entries rb) + 1"
  apply(subst rb_incr_tail_invalid_entries)
  by(auto simp:notempty valid)


text \<open>
  When we increment the tail, then the original tail is no longer in the set of
  valid entries. The head here is the original tail pointer. Likewise, the tail
  pointer is added to the set of invalid entries.
\<close>

lemma rb_incr_tail_valid_entries_notin1:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid_ptr rb" 
  shows "(tail rb) \<notin> set (rb_valid_entries (rb_incr_tail rb))"
  using notempty valid 
  apply(simp add:rb_incr_tail_valid_entries_tail)
  unfolding rb_valid_ptr_def rb_empty_def rb_valid_entries_def by(auto)

lemma rb_incr_tail_valid_entries_notin2:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid_ptr rb" 
  shows "hd (rb_valid_entries rb) \<notin> set (rb_valid_entries (rb_incr_tail rb))"
  using notempty valid rb_valid_entries_tail_first1 rb_incr_tail_valid_entries_notin1
  by fastforce


lemma rb_incr_tail_invalid_entries_member:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid_ptr rb" 
  shows "(tail rb) \<in> set (rb_invalid_entries (rb_incr_tail rb))"
  using notempty valid 
  by(simp add:rb_incr_tail_invalid_entries)

lemma rb_incr_tail_valid_entries_member:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid_ptr rb" 
  shows "hd (rb_valid_entries rb) \<in> set (rb_invalid_entries (rb_incr_tail rb))"
  using notempty valid  rb_incr_tail_invalid_entries_member rb_valid_entries_tail_first1 
  by fastforce


text \<open>
  Incrementing the tail pointer is preserving the validity invariant of the ring buffer
\<close>


lemma rb_incr_tail_valid_ptr:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid_ptr rb" 
  shows "rb_valid_ptr (rb_incr_tail rb)"
  using valid notempty
  unfolding  rb_incr_tail_def rb_valid_ptr_def
  by(auto)

lemma rb_incr_tail_valid:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid rb" 
shows "rb_valid (rb_incr_tail rb)"
  using valid notempty unfolding  rb_incr_tail_def rb_valid_def
  apply(simp add:rb_incr_tail_valid_ptr)
  by (metis Suc_eq_plus1 list.sel(2) list.set_sel(2) rb_incr_tail_def 
            rb_incr_tail_valid_entries_tail rb_incr_tail_valid_ptr)



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Incrementing the Head Pointer\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open> 
  Incrementing the head then adds the current head pointer to the end of the  list of 
  valid entries,  and thus increasing the set of valid entries.
\<close>

lemma rb_incr_head_valid_entries:
assumes notfull: "\<not>rb_full rb"  and  valid: "rb_valid_ptr rb"  
  shows "rb_valid_entries (rb_incr_head rb) = (rb_valid_entries rb) @ [(head rb)]"
  using notfull valid 
  unfolding rb_valid_entries_def rb_incr_head_def rb_full_def rb_valid_ptr_def
  apply(simp add: mod_Suc upt_Suc_append  upt_conv_Cons, auto)
  by (metis le_imp_less_Suc upt_Suc_append upt_rec)


text \<open>
  Likewise, the head element is removed from the set of invalid entries, and the 
  remainder is the tail of the original list.
\<close>

lemma rb_incr_head_invalid_entries:
assumes notfull: "\<not>rb_full rb"  and  valid: "rb_valid_ptr rb"  
  shows "rb_invalid_entries (rb_incr_head rb) = tl (rb_invalid_entries rb)"
  using notfull valid mod_Suc
  unfolding rb_invalid_entries_def rb_incr_head_def rb_full_def rb_valid_ptr_def
  by auto
 

text \<open>
  By taking everything but the last element, we get the original list back. 
\<close>

lemma rb_incr_head_valid_entries_butlast:
assumes notfull: "\<not>rb_full rb"  and  valid: "rb_valid_ptr rb"  
  shows "(rb_valid_entries rb) = butlast (rb_valid_entries (rb_incr_head rb))"
  using notfull valid by (metis butlast_snoc rb_incr_head_valid_entries)


text \<open>
  The resulting set of valid entries is a strict super set of the original one.
  Whereas the set of invalid entries is a subset of the original one.
\<close>

lemma rb_incr_head_valid_entries_superset:
assumes notempty: "\<not>rb_full rb"  and  valid: "rb_valid_ptr rb"  
  shows "set (rb_valid_entries rb) \<subset> set (rb_valid_entries (rb_incr_head rb))"
  using notempty valid 
  by(simp add:rb_incr_head_valid_entries psubset_insert_iff rb_valid_entries_head)

lemma rb_incr_head_invalid_entries_superset:
assumes notempty: "\<not>rb_full rb"  and  valid: "rb_valid_ptr rb"  
shows "set (rb_invalid_entries (rb_incr_head rb)) \<subset> set (rb_invalid_entries rb)"
  apply(subst rb_incr_head_invalid_entries)
  apply(simp_all add:notempty valid)
  using notempty valid rb_invalid_entries_distinct rb_invalid_entries_never_empty_list
  by (metis distinct.simps(2) list.exhaust_sel list.set_sel(1) psubsetI set_subset_Cons)


text \<open>
  The length of the list of valid entries decrements by one when the tail pointer is
  increased.
\<close>

lemma rb_incr_head_valid_entries_length1:
assumes notempty: "\<not>rb_full rb"  and  valid: "rb_valid_ptr rb"  
  shows "length (rb_valid_entries rb) = length (rb_valid_entries (rb_incr_head rb)) - 1"
  using notempty valid 
  by(simp add:rb_incr_head_valid_entries psubset_insert_iff rb_valid_entries_head)

lemma rb_incr_head_valid_entries_length2:
assumes notempty: "\<not>rb_full rb"  and  valid: "rb_valid_ptr rb"  
  shows "length (rb_valid_entries (rb_incr_head rb)) = length (rb_valid_entries rb) + 1"
  apply(subst rb_incr_head_valid_entries)
  by(simp_all add: notempty valid)


lemma rb_incr_head_invalid_entries_length1:
assumes notfull: "\<not>rb_full rb"  and  valid: "rb_valid_ptr rb"  
  shows "length (rb_invalid_entries rb) = length (rb_invalid_entries (rb_incr_head rb)) + 1"
  using notfull valid rb_incr_head_invalid_entries 
  using rb_invalid_entries_never_empty_list by force

lemma rb_incr_head_invalid_entries_length2:
assumes notfull: "\<not>rb_full rb"  and  valid: "rb_valid_ptr rb"  
  shows "length (rb_invalid_entries (rb_incr_head rb)) = length (rb_invalid_entries rb) - 1"
  apply(subst rb_incr_head_invalid_entries)
  by(simp_all add: notfull valid)


text \<open>
  The head element is added to the set of valid entries, in fact at the end of the
  list. 
\<close>
  
lemma rb_incr_head_valid_entries_last:
assumes notfull: "\<not> rb_full rb" and  valid: "rb_valid_ptr rb"  
  shows "head rb  = last (rb_valid_entries (rb_incr_head rb))"
  using notfull valid apply(subst rb_incr_head_valid_entries)
  by(auto)


text \<open>
  The original head pointer is now part of the set of valid entries.
\<close>

lemma rb_incr_head_valid_entries_headin:
assumes notfull: "\<not> rb_full rb" and  valid: "rb_valid_ptr rb"  
  shows "head rb \<in> set (rb_valid_entries (rb_incr_head rb))"
  using notfull valid apply(subst rb_incr_head_valid_entries)
  by(auto)

text \<open>
  Incrementing the head pointer preserves the validity invariant of the ring buffer.
  Note: we need to require that the element at the head of the ring is not None.
  In an enqueue operation this holds, as the element is written then the pointer updated.
\<close>

lemma rb_incr_head_valid_ptr:
assumes notfull: "\<not>rb_full rb"   and  valid: "rb_valid_ptr rb" 
  shows "rb_valid_ptr (rb_incr_head rb)"
  using notfull valid  unfolding rb_valid_ptr_def rb_incr_head_def by(simp)
  

lemma rb_incr_head_valid:
assumes notfull: "\<not>rb_full rb"   and  valid: "rb_valid rb" 
  shows "(ring rb) (head rb) \<noteq> None \<Longrightarrow> rb_valid (rb_incr_head rb)"
  using notfull valid unfolding rb_valid_def
  by(simp add:rb_incr_head_valid_ptr rb_incr_head_valid_entries rb_incr_head_ring)



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

text \<open>
  We can define the increment N recursively as:
\<close>

primrec rb_incr_head_n_rec ::  "nat \<Rightarrow> 'a CleanQ_RB \<Rightarrow>  'a CleanQ_RB"
  where "rb_incr_head_n_rec 0 rb = rb" |
        "rb_incr_head_n_rec (Suc n) rb = rb_incr_head (rb_incr_head_n_rec n rb)"

primrec rb_incr_tail_n_rec ::  "nat \<Rightarrow> 'a CleanQ_RB \<Rightarrow>  'a CleanQ_RB"
  where "rb_incr_tail_n_rec 0 rb = rb" |
        "rb_incr_tail_n_rec (Suc n) rb = rb_incr_tail (rb_incr_tail_n_rec n rb)"


text \<open>
  We can now show that for any N, we can reach the next N by applying the single
  head or tail incrementors.
\<close>

lemma rb_incr_head_n_ind:
  shows "rb_incr_head_n (Suc n) rb = rb_incr_head (rb_incr_head_n n rb)"
  unfolding rb_incr_head_n_def rb_incr_head_def
  by (simp add: mod_Suc_eq)

lemma rb_incr_tail_n_ind:
  "rb_incr_tail_n (Suc n) rb = rb_incr_tail (rb_incr_tail_n n rb)"
  unfolding rb_incr_tail_n_def rb_incr_tail_def
  by (simp add: mod_Suc_eq)


text \<open>
  Using the lemmas above, we can show that the recursive definition produces the same
  result as the direct formulation. 
\<close>

lemma rb_incr_head_n_req_equiv:
assumes valid : "rb_valid_ptr rb"
  shows "rb_incr_head_n_rec n rb = rb_incr_head_n n rb"
  apply(induct n)
  using valid apply(simp add: rb_incr_head_n_rec_def rb_incr_head_n_def rb_valid_ptr_def)
  by (simp add: rb_incr_head_n_ind)

lemma rb_incr_tail_n_req_equiv:
assumes valid : "rb_valid_ptr rb"
  shows "rb_incr_tail_n_rec n rb = rb_incr_tail_n n rb"
  apply(induct n)
  using valid apply(simp add: rb_incr_tail_n_rec_def rb_incr_tail_n_def rb_valid_ptr_def)
  by (simp add: rb_incr_tail_n_ind)


text \<open>
  We can now move the tail or head pointers in several steps in one go. We can now
  move forward to show that if there is enough space or there are enough entries in
  the ring, then for any N less than this, the operation leaves the buffer in the 
  same valid state. 
\<close>

definition rb_can_incr_tail_n :: "nat \<Rightarrow> 'a CleanQ_RB \<Rightarrow> bool"
  where "rb_can_incr_tail_n n rb = (n \<le> length (rb_valid_entries rb))"

definition rb_can_incr_head_n :: "nat \<Rightarrow> 'a CleanQ_RB \<Rightarrow> bool"
  where "rb_can_incr_head_n n rb = (n < length (rb_invalid_entries rb))"


text \<open>
  The maximum amounts the head and tail pointers can be increased is given by the
  length of the list of valid entries
\<close>

definition rb_can_incr_tail_n_max :: "'a CleanQ_RB \<Rightarrow> nat"
  where "rb_can_incr_tail_n_max rb = length (rb_valid_entries rb)"

definition rb_can_incr_head_n_max :: "'a CleanQ_RB \<Rightarrow> nat"
  where "rb_can_incr_head_n_max rb = length (rb_invalid_entries rb) - 1"


text \<open>
  We can now define the delta sets when the tail or head pointer is increased in terms
  of the valid or invalid entries.
\<close>

definition rb_incr_head_n_delta :: "nat \<Rightarrow> 'a CleanQ_RB \<Rightarrow> nat list"
  where "rb_incr_head_n_delta n rb  = take n (rb_invalid_entries rb)"

definition rb_incr_tail_n_delta :: "nat \<Rightarrow> 'a CleanQ_RB \<Rightarrow> nat list"
  where "rb_incr_tail_n_delta n rb  = take n (rb_valid_entries rb)"



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

lemma rb_incr_head_n_size: 
  "(size (rb_incr_head_n n rb)) = size rb"
  unfolding rb_incr_head_n_def by(auto)

lemma rb_incr_tail_n_size: 
  "(size (rb_incr_tail_n n rb)) = size rb"
  unfolding rb_incr_tail_n_def by(auto)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>The Head/Tail is not Changed\<close>
(* ------------------------------------------------------------------------------------ *)

lemma rb_incr_head_n_tail: 
  "(tail (rb_incr_head_n n rb)) = tail rb"
  unfolding rb_incr_head_n_def by(auto)

lemma rb_incr_tail_n_head: 
  "(head (rb_incr_tail_n n rb)) = head rb"
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
  "rb_valid_ptr rb \<Longrightarrow> rb_incr_head_n 0 rb = rb"
  unfolding rb_incr_head_n_def rb_incr_tail_def rb_valid_ptr_def by(auto)

lemma rb_incr_tail_0:
  "rb_valid_ptr rb \<Longrightarrow> rb_incr_tail_n 0 rb = rb"
  unfolding rb_incr_tail_n_def rb_incr_tail_def rb_valid_ptr_def by(auto)


text \<open>
  Therefore, incrementing the tail and head is always possible, as it doesn't change the
   state of the ring.
\<close>

lemma rb_can_incr_tail_0:
  "rb_can_incr_tail_n 0 rb"
  unfolding rb_can_incr_tail_n_def by(auto)

lemma rb_can_incr_head_0:
  "rb_valid_ptr rb \<Longrightarrow> rb_can_incr_head_n 0 rb"
  unfolding rb_can_incr_head_n_def using rb_invalid_entries_gt_zero by(auto)


text \<open>
  If the maximum that can we increase the tail or head pointer is 0, then the ring
  is either full or empty.
\<close>

lemma rb_can_incr_tail_max_0_empty:
  "rb_valid_ptr rb \<Longrightarrow> rb_can_incr_tail_n_max rb = 0 \<longleftrightarrow> rb_empty rb"
  by (simp add: rb_valid_entries_empty_num rb_can_incr_tail_n_max_def)

lemma rb_can_incr_head_max_0_full:
  "rb_valid_ptr rb \<Longrightarrow> rb_can_incr_head_n_max rb = 0 \<longleftrightarrow> rb_full rb"
  unfolding rb_can_incr_head_n_max_def using rb_invalid_entries_not_full_num by fastforce


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
  If we can increment the tail or head by one, then this means the ring is not empty
  or full.
\<close>

lemma rb_can_incr_tail_1:
  "rb_valid_ptr rb \<Longrightarrow> rb_can_incr_tail_n 1 rb \<longleftrightarrow> \<not> rb_empty rb"
  unfolding rb_can_incr_tail_n_def using rb_valid_entries_not_empty_list less_Suc_eq_le 
  by auto

lemma rb_can_incr_head_1:
  "rb_valid_ptr rb \<Longrightarrow> rb_can_incr_head_n 1 rb \<longleftrightarrow> \<not> rb_full rb"
  unfolding rb_can_incr_head_n_def
  using rb_invalid_entries_full_num rb_invalid_entries_not_full_num by auto


text \<open>
  In fact, if the maximum to increase the tail and head pointers is bigger than 
  zero, then the ring is not empty or not full.  
\<close>

lemma rb_can_incr_max_not_empty:
  "rb_valid_ptr rb \<Longrightarrow> 0 < rb_can_incr_tail_n_max rb \<Longrightarrow> \<not> rb_empty rb"
  by (metis not_less_zero rb_can_incr_tail_n_max_def rb_valid_entries_empty_num)

lemma rb_can_incr_max_not_full:
  "rb_valid_ptr rb \<Longrightarrow> 0 < rb_can_incr_head_n_max rb \<Longrightarrow> \<not> rb_full rb"
  by (simp add: rb_can_incr_head_n_max_def rb_invalid_entries_full_num)


text \<open>
  They also satisfy the validity constraints. As they are in fact the same as above.
\<close>

lemma rb_incr_head_zero_valid_ptr:
  "rb_valid_ptr rb \<Longrightarrow> rb_valid_ptr (rb_incr_head_n 0 rb)"
  by(subst rb_incr_head_0, auto)

lemma rb_incr_head_zero_valid:
  "rb_valid rb \<Longrightarrow> rb_valid (rb_incr_head_n 0 rb)"
  by(subst rb_incr_head_0, auto simp:rb_valid_def)

lemma rb_incr_tail_zero_valid_ptr:
  "rb_valid rb \<Longrightarrow> rb_valid (rb_incr_tail_n 0 rb)"
  by(subst rb_incr_tail_0, auto simp:rb_valid_def)

lemma rb_incr_tail_zero_valid:
  "rb_valid rb \<Longrightarrow> rb_valid (rb_incr_tail_n 0 rb)"
  by(subst rb_incr_tail_0, auto simp:rb_valid_def)
  

lemma rb_incr_head_one_valid_ptr:
assumes notfull: "\<not>rb_full rb"  and  valid: "rb_valid_ptr rb" 
  shows "rb_valid_ptr (rb_incr_head_n 1 rb)"
  apply(subst rb_incr_head_1)
  using valid notfull rb_incr_head_valid_ptr by blast 

lemma rb_incr_head_one_valid:
assumes notfull: "\<not>rb_full rb"  and  valid: "rb_valid rb" 
    and nextvalid: "(ring rb) (head rb) \<noteq> None"
shows "rb_valid (rb_incr_head_n 1 rb)"
  apply(subst rb_incr_head_1)
  using valid  using  nextvalid notfull rb_incr_head_valid rb_valid_def by blast

lemma rb_incr_tail_one_valid_ptr:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid_ptr rb" 
shows "rb_valid_ptr (rb_incr_tail_n 1 rb)"
  apply(subst rb_incr_tail_1)
  using notempty valid rb_incr_tail_valid_ptr by auto

lemma rb_incr_tail_one_valid:
assumes notempty: "\<not>rb_empty rb"  and  valid: "rb_valid rb" 
shows "rb_valid rb \<Longrightarrow> rb_valid (rb_incr_tail_n 1 rb)"
  apply(subst rb_incr_tail_1)
  using notempty valid rb_incr_tail_valid  by(auto)


text \<open>
  The empty/full state is preserved if the head/tail pointer are increased by 0.
\<close>


lemma rb_incr_tail_0_preserves_empty:
  "rb_valid_ptr rb \<Longrightarrow> rb_empty rb \<longleftrightarrow> rb_empty (rb_incr_tail_n 0 rb)"
  by (simp add: rb_incr_tail_0)

lemma rb_incr_tail_0_preserves_full:
  "rb_valid_ptr rb \<Longrightarrow> rb_full rb \<longleftrightarrow> rb_full (rb_incr_tail_n 0 rb)" 
  by (simp add: rb_incr_tail_0)

lemma rb_incr_head_0_preserves_empty:
  "rb_valid_ptr rb \<Longrightarrow> rb_empty rb \<longleftrightarrow> rb_empty (rb_incr_head_n 0 rb)" 
  by (simp add: rb_incr_head_0)

lemma rb_incr_head_0_preserves_full:
  "rb_valid_ptr rb \<Longrightarrow> rb_full rb \<longleftrightarrow> rb_full (rb_incr_head_n 0 rb)" 
  by (simp add: rb_incr_head_0)


text \<open>
  The deltas for increments of the tail and head pointers with 0 or 1 are either empty,
  or just the tail or head pointers.
\<close>

lemma rb_incr_head_n_delta_0:
  "rb_incr_head_n_delta 0 rb = []"
  by(auto simp:rb_incr_head_n_delta_def)

lemma rb_incr_tail_n_delta_0:
  "rb_incr_tail_n_delta 0 rb = []"
  by(auto simp:rb_incr_tail_n_delta_def)


lemma rb_incr_head_n_delta_1:
  "rb_valid_ptr rb \<Longrightarrow> \<not>rb_full rb \<Longrightarrow> rb_incr_head_n_delta 1 rb = [head rb]"
  unfolding rb_incr_head_n_delta_def rb_invalid_entries_def rb_valid_ptr_def by simp

lemma rb_incr_tail_n_delta_1:
  "rb_valid_ptr rb \<Longrightarrow> \<not>rb_empty rb \<Longrightarrow> rb_incr_tail_n_delta 1 rb = [tail rb]"
  unfolding rb_incr_tail_n_delta_def rb_valid_entries_def rb_valid_ptr_def rb_empty_def
  by simp


lemma rb_incr_head_n_delta_valid_1:
 "rb_valid_ptr rb \<Longrightarrow> \<not>rb_full rb \<Longrightarrow>
  rb_valid_entries (rb_incr_head_n 1 rb) = rb_valid_entries rb @ rb_incr_head_n_delta 1 rb"
  by (metis rb_incr_head_1 rb_incr_head_n_delta_1 rb_incr_head_valid_entries)

lemma rb_incr_head_n_delta_invalid_1:
 "rb_valid_ptr rb \<Longrightarrow> \<not>rb_full rb \<Longrightarrow>
  rb_incr_head_n_delta 1 rb @ rb_invalid_entries (rb_incr_head_n 1 rb) = rb_invalid_entries rb"
  by (metis append_Cons append_Nil list.collapse rb_incr_head_1 rb_incr_head_invalid_entries
            rb_incr_head_n_delta_1 rb_invalid_entries_head2 rb_invalid_entries_never_empty_list)

lemma rb_incr_tail_n_delta_valid_1:
 "rb_valid_ptr rb \<Longrightarrow> \<not>rb_empty rb \<Longrightarrow>
  rb_incr_tail_n_delta 1 rb @ rb_valid_entries (rb_incr_tail_n 1 rb) = rb_valid_entries rb"
  by (metis append_Cons append_Nil list.exhaust_sel rb_incr_tail_1 rb_incr_tail_n_delta_1 
            rb_incr_tail_valid_entries_tail rb_valid_entries_empty_list2 
            rb_valid_entries_tail_first1)

lemma rb_incr_tail_n_delta_invalid_1:
 "rb_valid_ptr rb \<Longrightarrow> \<not>rb_empty rb \<Longrightarrow>
  rb_invalid_entries (rb_incr_tail_n 1 rb) = rb_invalid_entries rb @ rb_incr_tail_n_delta 1 rb"
  by (metis rb_incr_tail_1 rb_incr_tail_invalid_entries rb_incr_tail_n_delta_1)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>N-Fold Functional Composition\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  We can show that this is just the functional composition of the \texttt+rb_incr_tail+.
\<close>

lemma rb_incr_tail_n_rec_compow :
  "rb_incr_tail_n_rec i rb = (rb_incr_tail ^^ i) rb"
  by(induct i, auto simp add:rb_incr_tail_n_rec_def rb_incr_tail_def)

lemma rb_incr_tail_n_compow:
  "rb_valid_ptr rb \<Longrightarrow> rb_incr_tail_n i rb = (rb_incr_tail ^^ i) rb"
  by(simp add:rb_incr_tail_n_req_equiv[symmetric] rb_incr_tail_n_rec_compow)

lemma rb_incr_head_n_rec_compow :
  "rb_incr_head_n_rec i rb = (rb_incr_head ^^ i) rb"
  by(induct i, auto simp add:rb_incr_head_n_rec_def rb_incr_head_def)

lemma rb_incr_head_n_compow:
  "rb_valid_ptr rb \<Longrightarrow> rb_incr_head_n i rb = (rb_incr_head ^^ i) rb"
  by(simp add:rb_incr_head_n_req_equiv[symmetric] rb_incr_head_n_rec_compow)



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Increments by N > 1\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  If we can increment it (N+1) times, then it also goes for N times, of in fact any
  n < N.
\<close>

lemma rb_can_incr_tail_n_suc:
  "rb_can_incr_tail_n (Suc n) rb \<Longrightarrow> rb_can_incr_tail_n n rb"
  unfolding rb_can_incr_tail_n_def by(auto)

lemma rb_can_incr_head_n_suc:
  "rb_can_incr_head_n (Suc n) rb \<Longrightarrow> rb_can_incr_head_n n rb"
  unfolding rb_can_incr_head_n_def by(auto)

lemma rb_can_incr_tail_n_lt:
  "rb_can_incr_tail_n N rb \<Longrightarrow> n < N \<Longrightarrow> rb_can_incr_tail_n n rb"
  unfolding rb_can_incr_tail_n_def by(auto)

lemma rb_can_incr_head_n_lt:
  "rb_can_incr_head_n N rb \<Longrightarrow> n < N \<Longrightarrow> rb_can_incr_head_n n rb"
  unfolding rb_can_incr_head_n_def by(auto)


text \<open>
  Attempting to increase it by more than the size of the ring always results in False.
  The same with increasing it larger than the maximum possible number.
\<close>

lemma rb_can_incr_tail_n_large:
  "rb_valid_ptr rb \<Longrightarrow> n \<ge> size rb \<Longrightarrow> \<not> rb_can_incr_tail_n n rb"
  unfolding rb_can_incr_tail_n_def
  using rb_valid_entries_less_size by fastforce

lemma rb_can_incr_head_n_large:
  "rb_valid_ptr rb \<Longrightarrow> n \<ge> size rb \<Longrightarrow> \<not> rb_can_incr_head_n n rb"
  unfolding rb_can_incr_head_n_def
  using rb_invalid_entries_less_size by fastforce

lemma rb_can_incr_tail_n_exceeds:
  "rb_valid_ptr rb \<Longrightarrow> n > rb_can_incr_tail_n_max rb \<longleftrightarrow> \<not> rb_can_incr_tail_n n rb"
  unfolding rb_can_incr_tail_n_def rb_can_incr_tail_n_max_def
  using rb_valid_entries_less_size by fastforce

lemma rb_can_incr_head_n_exceeds:
  "rb_valid_ptr rb \<Longrightarrow> n > rb_can_incr_head_n_max rb \<longleftrightarrow> \<not> rb_can_incr_head_n n rb"
  unfolding rb_can_incr_head_n_def rb_can_incr_head_n_max_def
  by (metis One_nat_def Suc_pred not_less_eq rb_invalid_entries_gt_zero)
  

text \<open>
  For any number $N$ which is smaller than the maximum possible increase, we can 
  increase the head or tail pointer by this number $N$.
\<close>

lemma rb_can_incr_tail_n_lt_max:
  "n \<le> rb_can_incr_tail_n_max rb \<longleftrightarrow> rb_can_incr_tail_n n rb"
  unfolding rb_can_incr_tail_n_def rb_can_incr_tail_n_max_def
  using rb_valid_entries_less_size by fastforce

lemma rb_can_incr_head_n_lt_max:
  "rb_valid_ptr rb \<Longrightarrow> n \<le> rb_can_incr_head_n_max rb \<longleftrightarrow> rb_can_incr_head_n n rb"
  unfolding rb_can_incr_head_n_def rb_can_incr_head_n_max_def
  using order_trans rb_invalid_entries_gt_zero by fastforce


text \<open>
  If we increment the tail or head pointer to the maximum possible, the resulting
  state is either empty or full.
\<close>

lemma rb_incr_tail_n_max_empty:
  assumes valid: "rb_valid_ptr rb"  and  incrtail: "N = rb_can_incr_tail_n_max rb"
  shows "rb_empty (rb_incr_tail_n N rb)"
  using incrtail valid 
  unfolding rb_incr_tail_n_def rb_empty_def rb_can_incr_tail_n_max_def rb_valid_entries_def
  by(auto simp:rb_valid_ptr_def)
  

lemma rb_incr_head_n_max_full:
  assumes valid: "rb_valid_ptr rb"  and  incrhead: "N = rb_can_incr_head_n_max rb"
  shows "rb_full (rb_incr_head_n N rb)"
  using incrhead valid 
  unfolding rb_incr_head_n_def rb_full_def rb_can_incr_head_n_max_def rb_invalid_entries_def
  by(auto simp:rb_valid_ptr_def mod_Suc_eq)


text \<open>
  Likewise, if we do not increment the tail or head by the maximum amount, the ring is not
  empty  or full.
\<close>

lemma rb_incr_tail_n_not_empty:
assumes valid: "rb_valid_ptr rb"
  shows "n < rb_can_incr_tail_n_max rb \<Longrightarrow>  \<not>rb_empty (rb_incr_tail_n n rb)"
  using valid 
  unfolding rb_can_incr_tail_n_max_def rb_empty_def rb_incr_tail_n_def rb_valid_entries_def
  apply(cases " tail rb \<le> head rb")
  apply (simp_all add: add.commute leD le_diff_conv rb_valid_ptr_def)
  apply (metis leD less_diff_conv mod_less_eq_dividend)
  using less_diff_conv mod_if by auto

lemma rb_incr_head_n_not_full:
assumes valid: "rb_valid_ptr rb"
  shows "n < rb_can_incr_head_n_max rb \<Longrightarrow>  \<not>rb_full (rb_incr_head_n n rb)"
  using valid 
  unfolding rb_can_incr_head_n_max_def rb_full_def rb_incr_head_n_def rb_invalid_entries_def
  apply(cases " tail rb \<le> head rb")
  apply (simp_all add:  rb_valid_ptr_def)
  using less_diff_conv mod_if apply(auto)
  using less_diff_conv mod_if apply(auto)
  done


text \<open>
  For any increase in the tail or head pointer which is less or equal to the maximum, 
  the resulting ring buffer state remains valid. We do the proof by induction over n.
\<close>
lemma rb_incr_tail_n_valid_ptr:
assumes valid: "rb_valid_ptr rb"  and  incrtail: "N = rb_can_incr_tail_n_max rb"
shows "n \<le> N \<Longrightarrow> rb_valid_ptr (rb_incr_tail_n n rb)"
  apply(induct n, simp add: rb_incr_tail_0 valid)
  by (simp add: incrtail rb_incr_tail_n_ind rb_incr_tail_n_not_empty 
                rb_incr_tail_valid_ptr valid)

lemma rb_incr_tail_n_valid:
assumes valid: "rb_valid rb"  and  incrtail: "N = rb_can_incr_tail_n_max rb"
shows "n \<le> N \<Longrightarrow> rb_valid (rb_incr_tail_n n rb)"
  apply(induct n, simp add: rb_incr_tail_zero_valid_ptr valid)
  by (simp add: incrtail rb_incr_tail_n_ind rb_incr_tail_n_not_empty rb_incr_tail_valid 
                rb_valid_implies_ptr_valid valid)


lemma rb_incr_head_n_valid_ptr:
assumes valid: "rb_valid_ptr rb"  and  incrhead: "N = rb_can_incr_head_n_max rb"
  shows "n \<le> N \<Longrightarrow> rb_valid_ptr (rb_incr_head_n n rb)"
  apply(induct n, simp add: rb_incr_head_zero_valid_ptr valid)
  by (simp add: incrhead rb_incr_head_n_ind rb_incr_head_n_not_full 
                rb_incr_head_valid_ptr valid)

lemma rb_incr_head_n_valid:
assumes valid: "rb_valid rb"  and  incrhead: "N = rb_can_incr_head_n_max rb"
 shows "n \<le> N \<Longrightarrow> \<forall>i \<in> set (rb_incr_head_n_delta n rb). ring rb (i) = Some y \<Longrightarrow> rb_valid (rb_incr_head_n n rb)"
  apply(induct n, simp add: rb_incr_head_zero_valid valid)
  unfolding rb_valid_def
  apply(auto simp:incrhead rb_incr_head_n_valid_ptr rb_valid_implies_ptr_valid valid)
  unfolding rb_incr_head_n_ind rb_incr_head_n_delta_def 
  oops


text \<open>
  Incrementing the tail or head pointer by a fixed amount of 0 or 1 keeps the number
  of maximum values the same or it decrements by one.  
\<close>

lemma rb_incr_tail_n_max_0:
assumes valid: "rb_valid_ptr rb"  and  incrtail: "N = rb_can_incr_tail_n_max rb"
  shows "rb_can_incr_tail_n_max (rb_incr_tail_n 0 rb) = N"
  by (simp add: incrtail rb_incr_tail_0 valid)

lemma rb_incr_head_n_max_0:
assumes valid: "rb_valid_ptr rb"  and  incrtail: "N = rb_can_incr_head_n_max rb"
  shows "rb_can_incr_head_n_max (rb_incr_head_n 0 rb) = N"
  by (simp add: incrtail rb_incr_head_0 valid)


lemma rb_incr_tail_n_max_1:
assumes valid: "rb_valid_ptr rb"  and  incrtail: "N = rb_can_incr_tail_n_max rb"
    and ngeq0: "N > 0"
  shows "rb_can_incr_tail_n_max (rb_incr_tail_n 1 rb) = N - 1"
  apply(subst rb_incr_tail_1)
  unfolding rb_can_incr_tail_n_max_def
  apply(subst rb_incr_tail_valid_entries_length2)
  using ngeq0 incrtail
  apply (metis neq0_conv rb_can_incr_tail_n_max_def rb_valid_entries_empty_num valid)
  apply(simp add:valid)
  apply(simp add:incrtail rb_can_incr_tail_n_max_def)
  done

lemma rb_incr_head_n_max_1:
assumes valid: "rb_valid_ptr rb"  and  incrhead: "N = rb_can_incr_head_n_max rb"
    and ngeq0: "N > 0"
  shows "rb_can_incr_head_n_max (rb_incr_head_n 1 rb) = N - 1"
  apply(subst rb_incr_head_1)
  unfolding rb_can_incr_head_n_max_def
  apply(subst rb_incr_head_invalid_entries_length2)
  using incrhead ngeq0 rb_can_incr_head_1 rb_can_incr_head_n_lt_max valid apply fastforce
  using valid apply simp
  using incrhead unfolding rb_can_incr_head_n_max_def by(auto)

text \<open>
  Incrementing the tail or head pointer by a variable amount n < N, reduces the 
  maximum possible increas in the head or tail pointers.
\<close>

lemma rb_incr_tail_n_max_n:
assumes valid: "rb_valid_ptr rb"  and  incrtail: "N = rb_can_incr_tail_n_max rb"
  shows "n \<le> N \<Longrightarrow> rb_can_incr_tail_n_max (rb_incr_tail_n n rb) = N - n"
  apply(induct n, simp add: incrtail rb_incr_tail_0 valid)
  using valid incrtail
  by (metis Suc_eq_plus1 Suc_leD diff_diff_left not_le_imp_less not_less_eq_eq 
            rb_can_incr_tail_n_max_def rb_incr_tail_n_ind rb_incr_tail_n_not_empty 
            rb_incr_tail_n_valid_ptr rb_incr_tail_valid_entries_length2)


lemma rb_incr_head_n_max_n:
assumes valid: "rb_valid_ptr rb"  and  incrhead: "N = rb_can_incr_head_n_max rb"
    and leq: "n \<le> N"
  shows "n \<le> N \<Longrightarrow> rb_can_incr_head_n_max (rb_incr_head_n n rb) = N - n"
  apply(induct n, simp add: incrhead rb_incr_head_0 valid)
  by (metis (no_types, lifting) Suc_diff_le Suc_leD Suc_le_lessD diff_Suc_Suc 
            diff_add_inverse incrhead plus_1_eq_Suc rb_incr_head_1 rb_incr_head_n_ind 
            rb_incr_head_n_max_1 rb_incr_head_n_valid_ptr valid zero_less_diff)





text \<open>
  Next we can talk about the effects on the set of valid and invalid entries when we 
  increment the tail or head pointers by N.
\<close>

lemma rb_incr_tail_n_valid_drop:
assumes valid: "rb_valid_ptr rb"  and  canincr: "N = rb_can_incr_tail_n_max rb"
shows "n\<le> N \<Longrightarrow> rb_valid_entries (rb_incr_tail_n n rb) = drop n (rb_valid_entries rb)"
  apply(induct n, simp add: rb_incr_tail_0 valid)
  using valid canincr
  by (simp add: drop_Suc rb_incr_tail_n_ind rb_incr_tail_n_not_empty rb_incr_tail_n_valid_ptr 
                rb_incr_tail_valid_entries_tail tl_drop)


lemma rb_incr_tail_n_invalid_drop:
assumes valid: "rb_valid_ptr rb"  and  canincr: "N = rb_can_incr_tail_n_max rb"
    and len: "l = length (rb_invalid_entries rb)"
  shows  "n \<le> N \<Longrightarrow>  take (l) (rb_invalid_entries (rb_incr_tail_n n rb)) = (rb_invalid_entries rb)"
  apply(induct n, simp add: len rb_incr_tail_0 rb_valid_implies_ptr_valid valid)
  using valid canincr len  
  apply(subst rb_incr_tail_n_ind)
  apply(subst rb_incr_tail_invalid_entries)
  using Suc_le_lessD rb_incr_tail_n_not_empty apply blast  
  using Suc_leD rb_incr_tail_n_valid_ptr apply blast
  using take_all by force


lemma rb_incr_head_n_valid_drop:
assumes valid: "rb_valid_ptr rb"  and  canincr: "N = rb_can_incr_head_n_max rb"
   and len : "l = length (rb_valid_entries rb)"   
 shows  "n \<le> N \<Longrightarrow> take (l) (rb_valid_entries (rb_incr_head_n n rb)) = (rb_valid_entries rb)"
  apply(induct n, simp add: len rb_incr_head_0 valid)
  using valid canincr len 
  by (metis (no_types, lifting) Suc_eq_plus1 Suc_le_lessD less_Suc_eq not_less
            rb_incr_head_n_ind rb_incr_head_n_not_full rb_incr_head_n_valid_ptr 
            rb_incr_head_valid_entries_butlast rb_incr_head_valid_entries_length2 
            take_all take_butlast)

lemma rb_incr_head_n_invalid_drop:
assumes valid: "rb_valid_ptr rb"  and  canincr: "N = rb_can_incr_head_n_max rb"
  shows "n \<le> N \<Longrightarrow> rb_invalid_entries (rb_incr_head_n n rb) = drop n (rb_invalid_entries rb)"
  apply(induct n, simp add:rb_incr_head_0 rb_valid_implies_ptr_valid valid)  
  using valid canincr
  by (simp add: drop_Suc rb_incr_head_invalid_entries rb_incr_head_n_ind 
                rb_incr_head_n_not_full rb_incr_head_n_valid_ptr rb_valid_implies_ptr_valid tl_drop)


  
lemma rb_incr_head_n_delta_valid_entries:
 "rb_valid_ptr rb \<Longrightarrow> n \<le> rb_can_incr_head_n_max rb \<Longrightarrow>
  rb_valid_entries (rb_incr_head_n n rb) = rb_valid_entries rb @ rb_incr_head_n_delta n rb"
  apply(induct n, simp add: rb_incr_head_0 rb_incr_head_n_delta_0)
  apply(subst rb_incr_head_n_ind)
  apply(subst rb_incr_head_valid_entries)
  apply (simp add: rb_incr_head_n_not_full)
  apply (simp add: rb_incr_head_n_valid_ptr)
  unfolding rb_incr_head_n_delta_def
  by (metis Suc_leD append_eq_append_conv2 length_append less_imp_not_less not_less 
            rb_incr_head_n_invalid_drop rb_incr_head_n_size rb_incr_head_n_valid_ptr 
            rb_invalid_entries_head2 rb_valid_entries_less_size rb_valid_invalid_entries_lengths
            take_all take_hd_drop)

lemma rb_incr_head_n_delta_invalid_entries:
 "rb_valid_ptr rb \<Longrightarrow> n \<le> rb_can_incr_head_n_max rb \<Longrightarrow>
  rb_incr_head_n_delta n rb @ rb_invalid_entries (rb_incr_head_n n rb) = rb_invalid_entries rb"
  apply(induct n, simp add: rb_incr_head_0 rb_incr_head_n_delta_0)
  unfolding rb_incr_head_n_delta_def
  by (metis Suc_leD Suc_le_lessD append_take_drop_id drop_Suc rb_incr_head_invalid_entries 
            rb_incr_head_n_ind rb_incr_head_n_not_full rb_incr_head_n_valid_ptr 
            same_append_eq tl_drop)

lemma rb_incr_tail_n_delta_valid_entries:
 "rb_valid_ptr rb \<Longrightarrow> n \<le> rb_can_incr_tail_n_max rb \<Longrightarrow>
  rb_incr_tail_n_delta n rb @ rb_valid_entries (rb_incr_tail_n n rb) = rb_valid_entries rb"
  apply(induct n, simp add: rb_incr_tail_0 rb_incr_tail_n_delta_0)
  unfolding rb_incr_tail_n_delta_def
  by (simp add: rb_incr_tail_n_valid_drop)

lemma rb_incr_tail_n_delta_invalid_entries:
 "rb_valid_ptr rb \<Longrightarrow> n \<le> rb_can_incr_tail_n_max rb \<Longrightarrow>
  rb_invalid_entries (rb_incr_tail_n n rb) = rb_invalid_entries rb @ rb_incr_tail_n_delta n rb"
  apply(induct n, simp add: rb_incr_tail_0 rb_incr_tail_n_delta_0)
  unfolding rb_incr_tail_n_delta_def
  by (metis (no_types, hide_lams)  Suc_leD Suc_le_lessD add.commute 
      append_eq_append_conv2 plus_1_eq_Suc rb_can_incr_tail_n_max_def
      rb_incr_tail_1 rb_incr_tail_n_delta_def rb_incr_tail_n_delta_invalid_1 
      rb_incr_tail_n_ind rb_incr_tail_n_not_empty rb_incr_tail_n_valid_drop 
      rb_incr_tail_n_valid_ptr take_add)


(* some more lemmas follow, needs sorting *)


lemma rb_inct_tail_n_drop_first_n:
assumes valid: "rb_valid_ptr rb" 
  shows "rb_can_incr_tail_n n rb  \<Longrightarrow> rb_valid_entries (rb_incr_tail_n n rb) = drop n (rb_valid_entries rb)"
  apply(induct n, simp add: rb_incr_tail_0 valid)
  by (simp add: rb_can_incr_tail_n_lt_max rb_incr_tail_n_valid_drop valid)





text \<open>
  Incrementing the tail by N increases the maximum possible head increases by N,
  and vice versa
\<close>


lemma rb_incr_tail_n_max_head:
assumes valid: "rb_valid_ptr rb"  and  incrtail: "N = rb_can_incr_tail_n_max rb"
  shows "n \<le> N \<Longrightarrow> rb_can_incr_head_n_max (rb_incr_tail_n n rb) = rb_can_incr_head_n_max rb + n" 
  apply(induct n, simp add: rb_incr_tail_0 valid)
  using valid incrtail unfolding rb_can_incr_head_n_max_def
  by (metis Nat.add_diff_assoc2 Suc_eq_plus1 Suc_leD Suc_le_lessD Suc_pred add_Suc_right 
            le_add2 rb_incr_tail_invalid_entries_length rb_incr_tail_n_ind 
            rb_incr_tail_n_not_empty rb_incr_tail_n_valid_ptr rb_invalid_entries_gt_zero)

lemma rb_incr_tail_n_max_tail:
assumes valid: "rb_valid_ptr rb"  and  incrtail: "N = rb_can_incr_tail_n_max rb"
  shows "n \<le> N \<Longrightarrow> rb_can_incr_tail_n_max (rb_incr_tail_n n rb) = rb_can_incr_tail_n_max rb - n" 
  apply(induct n, simp add: rb_incr_tail_0 valid)
  using valid incrtail unfolding rb_can_incr_tail_n_max_def
  by (simp add: incrtail rb_incr_tail_n_valid_drop)
  
lemma rb_incr_head_n_max_tail:
assumes valid: "rb_valid_ptr rb"  and  incrhead: "N = rb_can_incr_head_n_max rb"
  shows "n \<le> N \<Longrightarrow> rb_can_incr_tail_n_max (rb_incr_head_n n rb) = rb_can_incr_tail_n_max rb + n"
  apply(induct n, simp add: rb_incr_head_0 valid)
  using valid incrhead unfolding rb_can_incr_head_n_max_def
  by (simp add: rb_can_incr_head_n_max_def rb_can_incr_tail_n_max_def rb_incr_head_n_ind 
                rb_incr_head_n_not_full rb_incr_head_n_valid_ptr 
                rb_incr_head_valid_entries_length2)

lemma rb_incr_head_n_max_head:
assumes valid: "rb_valid_ptr rb"  and  incrhead: "N = rb_can_incr_head_n_max rb"
  shows "n \<le> N \<Longrightarrow> rb_can_incr_head_n_max (rb_incr_head_n n rb) = rb_can_incr_head_n_max rb - n"
  apply(induct n, simp add: rb_incr_head_0 valid)
  using valid incrhead unfolding rb_can_incr_head_n_max_def
  by (metis diff_Suc_eq_diff_pred  length_drop rb_can_incr_head_n_max_def 
            rb_incr_head_n_max_n)






lemma 
assumes const_delta: "delta \<le> length (rb_valid_entries rb)"  and  valid: "rb_valid rb"
  shows "set (rb_valid_entries (rb_incr_tail_n delta rb)) \<subseteq> set (rb_valid_entries rb)"
  using const_delta valid rb_inct_tail_n_drop_first_n 
  by (simp add: rb_inct_tail_n_drop_first_n rb_can_incr_tail_n_def rb_valid_def set_drop_subset)
  


  

lemma rb_incr_head_n_ind_invalid:
  assumes valid: "rb_valid rb" and
          incr: "rb_can_incr_head_n 1 rb"
  shows "rb_invalid_entries rb = [head rb] @ rb_invalid_entries (rb_incr_head_n 1 rb)"
  by (metis append_Cons append_Nil incr list.exhaust_sel rb_can_incr_head_1 rb_incr_head_1 
      rb_incr_head_invalid_entries rb_invalid_entries_head2 rb_invalid_entries_never_empty_list 
      rb_valid_def valid)

(*
lemma rb_incr_head_n_ind_invalid2:
  assumes valid: "rb_valid rb" and
          incr: "rb_can_incr_head_n 2 rb"
  shows "rb_invalid_entries rb = [head rb, head (rb_incr_head_n 1 rb)] @ rb_invalid_entries (rb_incr_head_n 2 rb)"
proof -
  from rb_incr_head_n_ind_invalid assms 
  have "rb_invalid_entries rb = [head rb] @ [head (rb_incr_head_n 1 rb)] @ rb_invalid_entries (rb_incr_head_n 2 rb)"
  
qed
*)

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
  apply(auto simp: rb_valid_def rb_write_head_def rb_valid_ptr_def)
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
assumes notfull: "rb_can_enq rb" and valid: "rb_valid_ptr rb"  
shows "rb_valid_entries (rb_enq b rb) =  rb_valid_entries (rb_incr_head rb)"
  apply(subst rb_enq_equiv_fun)
  apply(subst rb_enq_fun_def)
  unfolding rb_write_head_def using notfull valid rb_write_perserves_valid_entries 
  by (simp add: rb_incr_head_def rb_valid_entries_def rb_enq_equiv_fun)


lemma rb_enq_valid_entries :
assumes notfull: "rb_can_enq rb" and valid: "rb_valid_ptr rb"   
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
  "rb_valid_ptr rb \<Longrightarrow> (length (CleanQ_RB_list rb) < size rb)"
  unfolding CleanQ_RB_list_def rb_valid_entries_def rb_valid_ptr_def
  by auto


text \<open>
 We can now show that the list of valid entries is empty, when the predicate 
 \verb+rb_empty+ is true.
\<close>

lemma rb_list_empty:
  assumes valid: "rb_valid_ptr rb"
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
  by (simp add: rb_enq_buf_ring rb_enq_preserves_valid_entries rb_enq_valid_entries 
                rb_valid_def)


text \<open>
  The dequeue operation returns an element which is in the list of the original state,
  and the element is the head of this list.
\<close>

lemma rb_deq_list_was_head :
  assumes notempty: "rb_can_deq rb" and  valid: "rb_valid_ptr rb"  
     and res: "rb' = rb_deq rb" 
   shows "(fst rb') = hd (CleanQ_RB_list rb)"
  using notempty valid unfolding  CleanQ_RB_list_def res
  by(simp add:rb_deq_alt_def rb_deq_equiv rb_can_deq_def rb_incr_tail_valid_entries 
              rb_read_tail_def)
  
  

lemma rb_deq_list_was_in :
  assumes notempty: "rb_can_deq rb" and  valid: "rb_valid rb"  
     and res: "rb' = rb_deq rb" 
   shows "(fst rb') \<in> set (CleanQ_RB_list rb)"
  using res notempty valid rb_deq_list_was_head rb_can_deq_def rb_list_empty rb_valid_def
  by fastforce

text \<open>
  Likewise, the remainder of the state will be the tail of the original list. 
\<close>

lemma rb_deq_list_tail :
  assumes notempty: "rb_can_deq rb" and  valid: "rb_valid_ptr rb"   
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
  using rb_deq_list_was_head dist  rb_valid_def
  apply blast  
  by (metis dist distinct.simps(2) equals0D hd_Cons_tl rb_deq_list_was_head 
            rb_valid_implies_ptr_valid set_empty tl_Nil)
  

lemma rb_deq_not_empty:
assumes notempty: "rb_can_deq rb" and  valid: "rb_valid rb" 
  shows "CleanQ_RB_list rb \<noteq> []"
  unfolding CleanQ_RB_list_def
  using valid notempty rb_can_deq_def rb_valid_entries_tail_not_empty1 rb_valid_def by fastforce

lemma rb_deq_subset :
  assumes notempty: "rb_can_deq rb" and  valid: "rb_valid rb"  
     and res: "rb' = rb_deq rb" and dist: "distinct (CleanQ_RB_list rb)"
   shows "set (CleanQ_RB_list (snd rb')) \<subset> set (CleanQ_RB_list rb) " 
  using notempty valid res
  apply(simp add:rb_deq_list_tail)
  using dist rb_deq_not_empty list_set_hd_tl_union2 rb_deq_list_not_in 
        rb_deq_list_tail rb_deq_list_was_in rb_valid_def
  by fastforce


(* ==================================================================================== *)
subsection \<open>Frame condition under concurrent operation of two sides\<close>
(* ==================================================================================== *)  

text \<open>
  This is the frame condition for the left side i.e. the side which enqueues buffers into this
  particular RB. This means in the frame condition the head is fixed, but the tail can move
  according how the model permits it.  
\<close>

definition frame_rb_weak_left :: "'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB \<Rightarrow> bool"
  where "frame_rb_weak_left st' st \<longleftrightarrow>
    size st' = size st \<and>
    head st' = head st \<and>
    ring st' = ring st \<and>
    rb_valid st' \<and> rb_valid st \<and>
   (\<exists> \<delta>tl.
    (if (tail st') + \<delta>tl < (size st') then tail st' + \<delta>tl
     else ((tail st') + \<delta>tl) mod (size st')) = tail st
  )" 

lemma frame_rb_weak_left_state:
  assumes frame: "frame_rb_weak_left st' st" and
          head: "tail st = tail (rb_incr_tail_n n st')" and
          incr: "rb_can_incr_tail_n n st'"
  shows "st = rb_incr_tail_n n st'"
  using assms unfolding frame_rb_weak_left_def rb_incr_tail_n_def
  by simp

text \<open>
  To talk about the previously introduced delta, we need some lemmas  
\<close>

definition rb_delta_tail :: "nat \<Rightarrow> 'a CleanQ_RB \<Rightarrow> nat list"
  where "rb_delta_tail n rb = take n (rb_valid_entries rb)" 

lemma rb_take_tail:
  assumes tail: "rb_can_incr_tail_n 1 st' \<and> tail st' \<le> head st'" and
          frame: "frame_rb_weak_left st' st" and
          valid: "rb_valid_ptr st'"
   shows "[tail st' ..< head st'] = [tail st'] @ ([tail (rb_incr_tail_n 1 st') ..< head st'])"
  using tail frame valid
  unfolding rb_incr_tail_n_def
  apply(simp) 
  by (metis Suc_leI le_antisym mod_less not_less rb_can_incr_tail_1 rb_empty_def 
            rb_valid_ptr_def tail upt_rec)

lemma rb_take_tail2:
  assumes tail: "rb_can_incr_tail_n n st' \<and> tail st' \<le> head st'" and
          frame: "frame_rb_weak_left st' st" and
          valid: "rb_valid_ptr st'"
   shows "take n [tail st' ..< head st'] = take n ([tail st'] @ ([tail (rb_incr_tail_n 1 st') ..< head st']))"
  by (metis eq_iff frame le0 list.size(3) rb_can_incr_tail_1 rb_can_incr_tail_n_lt_max 
            rb_can_incr_tail_n_max_def rb_take_tail rb_valid_entries_empty_list2 tail
            take_eq_Nil valid)

lemma rb_delta_helper :
  assumes valid: "rb_valid rb" and
          n_valid: "rb_can_incr_tail_n n rb"
  shows "rb_valid_entries rb = (take n (rb_valid_entries rb)) @ drop n (rb_valid_entries rb)"
  by simp
  

lemma rb_delta_helper2:
  assumes valid: "rb_valid rb" and
          n_valid: "rb_can_incr_tail_n n rb"
  shows "rb_valid_entries rb = rb_delta_tail n rb @ drop n (rb_valid_entries rb)"
  unfolding rb_delta_tail_def
  by simp
  

text \<open>
  This next lemma shows properties about the definition of rb_delta_tail
\<close>
lemma rb_delta_tail_size_nonzero:
  fixes st' st 
  assumes frame: "frame_rb_weak_left st' st" and
          deq: "rb_can_incr_tail_n delta st'"
  shows "delta > 0 \<Longrightarrow> (rb_delta_tail delta st') \<noteq> []"
  using assms
  unfolding rb_delta_tail_def rb_valid_entries_def
  by (smt length_upt not_gr_zero not_le rb_can_incr_tail_n_def rb_valid_entries_def 
      take_eq_Nil upt_0 zero_less_diff) 
  
lemma rb_delta_tail_empty:
  fixes st' st 
  assumes frame: "frame_rb_weak_left st' st"
  shows "delta = 0 \<Longrightarrow> (rb_delta_tail delta st) = []"
  using assms
  unfolding rb_delta_tail_def
by (simp add: frame_rb_weak_left_def rb_valid_def)

lemma rb_weak_list_delta_tail_empty:
  fixes st' st 
  assumes frame: "frame_rb_weak_left st' st" and
          tl_asm:  "(tail st') + \<delta>tl = (tail st) \<and> \<delta>tl = 0"
  shows "tail st' = tail st \<Longrightarrow> rb_valid_entries st' = (rb_delta_tail \<delta>tl st') @ (rb_valid_entries st)"
  by (metis (no_types, hide_lams) append_Nil frame frame_rb_weak_left_def rb_delta_tail_def 
      rb_valid_entries_def take0 tl_asm)


lemma rb_incr_tail_wrap:
  fixes rb
  assumes "rb_valid_ptr rb"
  shows "tail rb = (size rb -1) \<Longrightarrow> tail (rb_incr_tail_n 1 rb) = 0" 
  using assms unfolding rb_incr_tail_n_def rb_valid_ptr_def by(auto)

text \<open>
  Similarly we show the influence of the tail moving on the valid entries in the ring buffer
\<close>

lemma rb_delta_tail_one:
  fixes st st'
  assumes tail: "tail st = tail (rb_incr_tail_n 1 st') \<and> (rb_can_incr_tail_n 1 st')"
  assumes head: "head st = head st'"
  assumes valid: "rb_valid st'"
  shows "(rb_delta_tail 1 st') = [tail st']"
  using tail
  unfolding rb_delta_tail_def rb_valid_def
  by (metis One_nat_def list.size(3) not_less_eq_eq order_refl rb_can_incr_tail_1 
      rb_can_incr_tail_n_def rb_valid_entries_tail_first1 take0 take_Suc valid rb_valid_def)


lemma rb_weak_list_delta_tail_one:
  fixes st' st 
  assumes frame: "frame_rb_weak_left st' st" and
          tail: "tail st = tail (rb_incr_tail_n 1 st')" and
          deq: "rb_can_incr_tail_n 1 st'" and
          valid : " rb_valid st'"
  shows  "rb_valid_entries st' = (rb_delta_tail 1 st') @ (rb_valid_entries st)"
  using assms 
  apply auto unfolding rb_incr_tail_n_def frame_rb_weak_left_def rb_delta_tail_def
  by (metis (no_types, lifting) One_nat_def append_Cons ext_inject rb_can_incr_tail_1 
      rb_incr_tail_1 rb_incr_tail_n_def rb_incr_tail_valid_entries rb_valid_entries_def 
      rb_valid_entries_not_empty_list rb_valid_entries_tail_first1 self_append_conv2 surjective 
      take_Suc take_eq_Nil update_convs(3) rb_valid_def)


text \<open>
  Now, similar the left side, we also need the frame condition for the right side i.e. tail is fixed
  but the head can move
\<close>

definition frame_rb_weak_right :: "'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB \<Rightarrow> bool"
  where "frame_rb_weak_right st' st \<longleftrightarrow>
    size st' = size st \<and>
    tail st' = tail st \<and>
    ring st' = ring st \<and>
    rb_valid st' \<and> rb_valid st \<and>
   (\<exists> \<delta>tl.
    (if (head st') + \<delta>tl < (size st') then head st' + \<delta>tl
     else ((head st') + \<delta>tl) mod (size st')) = head st
  )" 

lemma frame_rb_weak_right_state:
  assumes frame: "frame_rb_weak_right st' st" and
          head: "head st = head (rb_incr_head_n n st')" and
          incr: "rb_can_incr_head_n n st'"
  shows "st = rb_incr_head_n n st'"
  using assms unfolding frame_rb_weak_right_def rb_incr_head_n_def
  by simp

definition rb_delta_head :: "nat \<Rightarrow> 'a CleanQ_RB \<Rightarrow> nat list"
  where "rb_delta_head delta rb = (if (head rb + delta) < (size rb) then [(head rb) ..< ((head rb) + delta)]
                                   else [(head rb)..< (size rb)] @ [0..< ((head rb) + delta) mod (size rb)])"

definition rb_delta_head_alt :: "nat \<Rightarrow> 'a CleanQ_RB \<Rightarrow> nat list"
  where "rb_delta_head_alt n rb = rev (take n (rev (rb_valid_entries rb)))"

definition rb_delta_head_inv :: "nat \<Rightarrow> 'a CleanQ_RB \<Rightarrow> nat list"
  where "rb_delta_head_inv n rb = take n (rb_invalid_entries rb)"

primrec rb_delta_head_rec :: "nat \<Rightarrow> 'a CleanQ_RB \<Rightarrow> nat list"
  where "rb_delta_head_rec 0 rb = []" |
        "rb_delta_head_rec (Suc n) rb = [head rb] @ (rb_delta_head_rec n (rb_incr_head_n 1 rb))"


lemma rb_delta_head_inv_helper:
  assumes valid: "rb_valid rb" and
          head: "rb_can_incr_head_n 1 rb"
  shows "take 1 (rb_invalid_entries rb) = [head rb]"
  by (metis head rb_can_incr_head_1 rb_incr_head_n_delta_1 rb_incr_head_n_delta_def rb_valid_def valid)

lemma rb_delta_head_inv_helper2:
  assumes valid: "rb_valid rb" and
          head: "rb_can_incr_head_n 2 rb"
        shows "take 1 (rb_invalid_entries (rb_incr_head_n 1 rb)) = [head (rb_incr_head_n 1 rb)]"
  using rb_delta_head_inv_helper assms
proof -
  from assms have core: "rb_invalid_entries rb = [head rb] @ rb_invalid_entries (rb_incr_head_n 1 rb)"
    unfolding rb_invalid_entries_def  
    by (smt Suc_1 append_Cons append_Nil list.exhaust_sel rb_can_incr_head_1 rb_can_incr_head_n_suc 
        rb_incr_head_1 rb_incr_head_invalid_entries rb_invalid_entries_def rb_invalid_entries_head2 
        rb_invalid_entries_never_empty_list)

  from core have core2: "take 1 (rb_invalid_entries rb) = [head rb]"
    by simp

  from core core2 show "take 1 (rb_invalid_entries (rb_incr_head_n 1 rb)) = [head (rb_incr_head_n 1 rb)]" 
    using assms
    proof -
    have f1: "ring (rb_incr_head_n 1 rb) = ring rb \<and> head (rb_incr_head_n 1 rb) = (head rb + Suc 0) mod CleanQ_RB.size rb \<and> tail (rb_incr_head_n 1 rb) = tail rb \<and> CleanQ_RB.size (rb_incr_head_n 1 rb) = CleanQ_RB.size rb \<and> more (rb_incr_head_n 1 rb) = more rb"
      by (simp add: rb_incr_head_n_def)
    have f2: "\<forall>ns n. ns = [] \<or> take (Suc n) ns = (hd ns::nat) # take n (tl ns)"
    using take_Suc by blast
    have f3: "\<forall>n na. \<not> (n::nat) < na \<or> n \<le> na"
      using less_imp_le_nat by satx
      have f4: "\<forall>n na nb ns. ([n..<na] = nb # ns) = (n < na \<and> n = nb \<and> [n + 1..<na] = ns)"
        using upt_eq_Cons_conv by blast
    have f5: "\<forall>n na. if n < na then [n..<na] = n # [Suc n..<na] else [n..<na] = []"
      by (simp add: upt_rec)
      then have f6: "rb_invalid_entries (rb_incr_head_n 1 rb) \<noteq> []"
        using f4 f3 by (metis (no_types) One_nat_def Suc_1 append_Cons assms(2) core less_eq_Suc_le list.size(3) list.size(4) not_less rb_can_incr_head_n_def self_append_conv2)
      have f7: "\<forall>c. if tail (c::'a CleanQ_RB) \<le> head c then rb_invalid_entries c = [head c..<CleanQ_RB.size c] @ [0..<tail c] else rb_invalid_entries c = [head c..<tail c]"
        by (meson rb_invalid_entries_def)
      have f8: "\<not> length ([] @ rb_invalid_entries (rb_incr_head_n 1 rb)) + Suc 0 < 2"
        using f3 by (metis append_Cons assms(2) core list.size(4) not_less rb_can_incr_head_n_def)
    then have f9: "[length ([] @ rb_invalid_entries (rb_incr_head_n 1 rb)) + Suc 0..<2] = []"
      using f5 by presburger
      have f10: "\<forall>ns. ns = [] \<or> ns = (hd ns::nat) # tl ns"
        by (meson list.exhaust_sel)
      then have f11: "head (rb_incr_head_n 1 rb) < tail (rb_incr_head_n 1 rb) \<longrightarrow> [] @ rb_invalid_entries (rb_incr_head_n 1 rb) = hd ([] @ rb_invalid_entries (rb_incr_head_n 1 rb)) # tl ([] @ rb_invalid_entries (rb_incr_head_n 1 rb))"
        using f8 f7 f4 by (metis (no_types) not_less self_append_conv2)
      have "[] @ rb_invalid_entries (rb_incr_head_n 1 rb) \<noteq> []"
        using f6 by simp
      then have f12: "[] @ rb_invalid_entries (rb_incr_head_n 1 rb) = hd ([] @ rb_invalid_entries (rb_incr_head_n 1 rb)) # tl ([] @ rb_invalid_entries (rb_incr_head_n 1 rb))"
    using f10 by meson
      have f13: "head \<lparr>ring = ring rb, head = head rb, tail = tail rb, size = CleanQ_RB.size rb, \<dots> = more rb\<rparr> + Suc 0 = head rb + 1"
        by simp
    { assume "\<not> (head rb + Suc 0) mod CleanQ_RB.size rb < CleanQ_RB.size rb"
      { assume "CleanQ_RB.size rb < head rb + 1"
        then have "[head rb + 1..<Suc (CleanQ_RB.size rb)] = []"
          by simp
    then have "rb_invalid_entries (rb_incr_head_n 1 rb) = [head (rb_incr_head_n 1 rb)..<CleanQ_RB.size (rb_incr_head_n 1 rb)] @ [0..<tail (rb_incr_head_n 1 rb)] \<and> [(head rb + Suc 0) mod CleanQ_RB.size rb..<CleanQ_RB.size rb] = [] \<longrightarrow> \<not> 0 < tail rb \<or> 0 \<noteq> hd (rb_invalid_entries (rb_incr_head_n 1 rb)) \<or> [0 + 1..<tail rb] \<noteq> tl (rb_invalid_entries (rb_incr_head_n 1 rb))"
      using f12 f9 f7 f5 f4 f3 f2 by (metis (no_types) append_Cons core not_less not_less_eq_eq self_append_conv2 take0) }
      then have "rb_invalid_entries (rb_incr_head_n 1 rb) = [head (rb_incr_head_n 1 rb)..<CleanQ_RB.size (rb_incr_head_n 1 rb)] @ [0..<tail (rb_incr_head_n 1 rb)] \<longrightarrow> (head rb + Suc 0) mod CleanQ_RB.size rb = hd (rb_invalid_entries (rb_incr_head_n 1 rb)) \<or> [(head rb + Suc 0) mod CleanQ_RB.size rb..<CleanQ_RB.size rb] = (head rb + Suc 0) mod CleanQ_RB.size rb # [Suc ((head rb + Suc 0) mod CleanQ_RB.size rb)..<CleanQ_RB.size rb]"
        using f13 f12 f5 f4 f1 by (metis (no_types) mod_less mod_self nat_neq_iff self_append_conv2 surjective) }
    then have "rb_invalid_entries (rb_incr_head_n 1 rb) = [head (rb_incr_head_n 1 rb)..<CleanQ_RB.size (rb_incr_head_n 1 rb)] @ [0..<tail (rb_incr_head_n 1 rb)] \<longrightarrow> (head rb + Suc 0) mod CleanQ_RB.size rb = hd (rb_invalid_entries (rb_incr_head_n 1 rb))"
      using f1 by fastforce
      then show ?thesis
        using f11 f7 f6 f4 f2 f1 by (metis (no_types) One_nat_def not_less self_append_conv2 take0)
    qed
qed

lemma rb_delta_head_inv_helper3: 
  assumes frame: "frame_rb_weak_right st' st" and
          head: "head st = head (rb_incr_head_n n st')" and
          enq: "rb_can_incr_head_n n st'"
  shows "rb_delta_head_inv (Suc n) st' = [head st'] @ rb_delta_head_inv n (rb_incr_head_n 1 st')" 
  by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 append_Cons assms(1) assms(3) frame_rb_weak_right_def 
      le_add1 less_eq_Suc_le list.size(3) list.size(4) nat_neq_iff not_less plus_1_eq_Suc rb_can_incr_head_n_def rb_delta_head_inv_def rb_incr_head_1 rb_incr_head_invalid_entries rb_invalid_entries_full rb_invalid_entries_head2 rb_valid_def self_append_conv2 take_Suc take_eq_Nil)


text \<open>
  This next lemma shows properties about the definition of rb delta head
\<close>

lemma rb_delta_head_size_nonzero:
  fixes st' st 
  assumes frame: "frame_rb_weak_right st' st"
  shows "delta > 0 \<Longrightarrow> (rb_delta_head delta st) \<noteq> []"
  using assms
  unfolding rb_delta_head_def
by (simp add: frame_rb_weak_right_def rb_valid_def rb_valid_ptr_def)

lemma rb_weak_list_delta_head_empty:
  fixes st' st 
  assumes frame: "frame_rb_weak_right st' st" and
          hd_asm:  "(head st') + \<delta>hd = (head st) \<and> \<delta>hd = 0"
  shows "head st' = head st \<Longrightarrow> rb_delta_head \<delta>hd st' @ rb_valid_entries st'  = (rb_valid_entries st)"
proof -
  from hd_asm have "\<delta>hd = 0" 
    by simp

  from hd_asm have hd: "head st' = head st"
    by simp

  from hd_asm have rb_delta: "rb_delta_head \<delta>hd st' = rb_delta_head 0 st'" 
    unfolding rb_delta_head_def 
    by auto

  from rb_delta have rb_delta_empty: "rb_delta_head \<delta>hd st' = []"
    unfolding rb_delta_head_def
    by (metis frame frame_rb_weak_right_def hd hd_asm less_not_refl rb_valid_def 
        rb_valid_ptr_def upt_rec)

  from rb_delta_empty have "rb_valid_entries st' = rb_valid_entries st"
    unfolding rb_valid_entries_def
    by (metis (no_types, hide_lams) frame frame_rb_weak_right_def hd)

  show ?thesis using rb_delta_empty
    by (simp add: \<open>rb_valid_entries st' = rb_valid_entries st\<close>)
qed

lemma rb_incr_head_wrap:
  fixes rb
  assumes "rb_valid rb"
  shows "head rb = (size rb -1) \<Longrightarrow> head (rb_incr_head_n 1 rb) = 0" 
  unfolding rb_incr_head_n_def
  by (metis (no_types, lifting) One_nat_def Suc_leI append_Nil2 assms diff_is_0_eq' 
      diff_zero ext_inject le_add_diff_inverse2 less_imp_le_nat mod_self not_le_imp_less 
      rb_incr_tail_valid_entries rb_invalid_entries_def rb_invalid_entries_never_empty_list 
      rb_valid_def rb_valid_entries_def rb_valid_entries_tail_empty2 rb_valid_entries_tail_not_empty1 
      surjective update_convs(2) upt_0 upt_eq_Cons_conv)

text \<open>
  Similarly we show the influence of the tail moving on the valid entries in the ring buffer
\<close>

lemma rb_delta_head_one:
  fixes st st'
  assumes head: "head st = head (rb_incr_head_n 1 st') \<and> tail st = tail st'"
  assumes valid: "rb_valid st' \<and> rb_valid st"
  shows "(rb_delta_head 1 st') = [head st']"
  unfolding rb_delta_head_def rb_valid_def
proof auto
  show "\<not> Suc (head st') < CleanQ_RB.size st' \<Longrightarrow> [head st'..<CleanQ_RB.size st'] @ [0..<Suc (head st') mod CleanQ_RB.size st'] = [head st']"
    by (metis Suc_lessI less_not_refl mod_self rb_valid_def rb_valid_ptr_def self_append_conv upt_rec valid)
qed

lemma rb_delta_head_one_rec:
  fixes st st'
  assumes head: "head st = head (rb_incr_head_n 1 st') \<and> tail st = tail st'"
  assumes valid: "rb_valid st' \<and> rb_valid st"
  shows "(rb_delta_head_rec 1 st') = [head st']"
  unfolding rb_delta_head_rec_def rb_valid_def
  by simp

lemma rb_delta_one_hd_geq_tl:
  fixes st 
  assumes frame: "rb_valid st"
  assumes tl_hd: "tail st \<le> head st"
  assumes enq: "rb_can_enq st" (* we can actually enqueue *)
  shows "[tail st..<head st] @ [head st] = [tail st..<(Suc (head st))]"
  using enq tl_hd frame unfolding rb_incr_head_n_def 
  by simp

lemma rb_delta_one_hd_leq_tl:
  fixes st 
  assumes frame: "rb_valid st"
  assumes tl_hd: "tail st \<ge> head st"
  assumes enq: "rb_can_enq st" (* we can actually enqueue *)
  shows "[tail st..<size st] @ [0..< head st] @ [head st]  = [tail st..<size st] @ [0..< Suc (head st)]"
  using enq tl_hd frame unfolding rb_incr_head_n_def 
  by (metis less_eq_nat.simps(1) upt_Suc)
  
lemma rb_weak_list_delta_head_one:
  fixes st' st 
  assumes frame: "frame_rb_weak_left st' st" and
          head: "head st = head (rb_incr_head_n 1 st')" and
          enq: "rb_can_enq st'"
  shows  "rb_valid_entries st' @ rb_delta_head 1 st' = (rb_valid_entries st)"
  using enq
  by (metis frame frame_rb_weak_left_def head rb_can_enq_def rb_incr_head_1 
      rb_incr_head_valid_entries_headin rb_valid_def rb_valid_entries_head)

  
lemma rb_weak_list_delta_head_alt_one:
  fixes st' st 
  assumes frame: "frame_rb_weak_left st' st" and
          head: "head st = head (rb_incr_head_n 1 st')" and
          enq: "rb_can_enq st'"
  shows  "rb_valid_entries st' @ rb_delta_head_alt 1 st' = (rb_valid_entries st)"
  using enq
  by (metis frame frame_rb_weak_left_def head rb_can_enq_def rb_incr_head_1 
      rb_incr_head_valid_entries_headin rb_valid_def rb_valid_entries_head)


lemma rb_weak_list_delta_head_one_rec:
  fixes st' st 
  assumes frame: "frame_rb_weak_left st' st" and
          head: "head st = head (rb_incr_head_n 1 st')" and
          enq: "rb_can_enq st'"
  shows  "rb_valid_entries st' @ rb_delta_head_rec 1 st = (rb_valid_entries st)"
  using enq
  by (metis frame frame_rb_weak_left_def head rb_can_enq_def rb_incr_head_1 
      rb_incr_head_valid_entries_headin rb_valid_def rb_valid_entries_head)

lemma rb_weak_list_delta_head_one_inv:
  fixes st' st 
  assumes frame: "frame_rb_weak_left st' st" and
          head: "head st = head (rb_incr_head_n 1 st')" and
          enq: "rb_can_enq st'"
  shows  "rb_valid_entries st' @ rb_delta_head_inv 1 st = (rb_valid_entries st)"
  using enq
  by (metis frame frame_rb_weak_left_def head rb_can_enq_def 
      rb_incr_head_1 rb_incr_head_valid_entries_headin rb_valid_def rb_valid_entries_head)


text \<open>
  Similar proofs but for delta larger than 1: TODO
\<close>

lemma rb_weak_list_delta_tail_n:
  fixes st' st n
  assumes frame: "frame_rb_weak_left st' st" and
          tail: "tail st = tail (rb_incr_tail_n n st')" and
          deq: "rb_can_incr_tail_n n st'"
  shows  "rb_valid_entries st' = (rb_delta_tail n st') @ (rb_valid_entries st)"
  using assms unfolding rb_delta_tail_def frame_rb_weak_left_def
  using frame_rb_weak_left_def frame_rb_weak_left_state 
        rb_inct_tail_n_drop_first_n rb_valid_implies_ptr_valid by fastforce
(*
lemma rb_weak_list_delta_head_invalid:
  fixes st' st 
  assumes frame: "frame_rb_weak_right st' st" and
          head: "head st = head (rb_incr_head_n n st')" and
          enq: "rb_can_incr_head_n n st'"
  shows  "rb_invalid_entries st' = (rb_delta_head_inv n st') @ rb_invalid_entries st"  
  using assms


lemma rb_weak_list_delta_head_rec_n:
  fixes st' st 
  assumes frame: "frame_rb_weak_right st' st" and
          head: "head st = head (rb_incr_head_n n st')" and
          enq: "rb_can_incr_head_n n st'"
  shows  "rb_valid_entries st' @ rb_delta_head_inv n st' = (rb_valid_entries st)"  
  using assms unfolding rb_delta_head_inv_def
proof -
  have st: "frame_rb_weak_right st' st \<and> head st = head (rb_incr_head_n n st') \<Longrightarrow> st = rb_incr_head_n n st'"
    unfolding frame_rb_weak_right_def rb_incr_head_n_def
    by auto
  have st2: "rb_valid_entries st = rb_valid_entries (rb_incr_head_n n st')"
    using frame head st
    by blast

  from assms have "rb_invalid_entries st' = (rb_delta_head_inv n st') @ rb_invalid_entries st"
    unfolding rb_delta_head_inv_def st st2
  
  

qed
*)

end