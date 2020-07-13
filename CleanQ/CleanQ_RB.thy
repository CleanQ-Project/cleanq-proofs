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


(* ------------------------------------------------------------------------------------ *)
subsection \<open>Bounded Descriptor Ring\<close>
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
  and the buffer needs a certain size. Note, we require the size of the ring to be at
  least 2. By using the head and tail pointers, we need to be able to distinguish 
  a full from an empty ring buffer. This requires to `give up' one element to always
  distinguish the full and empty conditions below.
\<close>

definition rb_valid :: "'a CleanQ_RB \<Rightarrow> bool"
  where "rb_valid rb \<longleftrightarrow> (head rb < size rb) \<and> (tail rb < size rb) \<and> (size rb > 1)"

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
  
\<close>

lemma rb_full_not_empty:
  "rb_valid rb \<Longrightarrow> rb_full rb \<Longrightarrow> \<not> rb_empty rb"
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
  they are part of the valid entries.
\<close>

lemma rb_valid_entries_head :
  "(head rb) \<notin> set (rb_valid_entries rb)"
  unfolding rb_valid_entries_def by(auto)

lemma rb_valid_entries_tail1 :
  "head rb = tail rb \<Longrightarrow> (tail rb) \<notin> set (rb_valid_entries rb)"
  unfolding rb_valid_entries_def by(simp)

lemma rb_valid_entries_tail2 :
  "rb_valid rb \<Longrightarrow> head rb \<noteq> tail rb \<Longrightarrow> (tail rb) \<in> set (rb_valid_entries rb)"
  unfolding rb_valid_entries_def rb_valid_def by(simp)

lemma rb_valid_entries_tail3:
  "\<not>rb_empty rb \<Longrightarrow> (tail rb) \<in> set (rb_valid_entries rb)"

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
   
end