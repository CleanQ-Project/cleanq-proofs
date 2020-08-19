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



section \<open>List/Set Helper Lemmas\<close>

text \<open>
  We first define a few helper-lemmas for reasoning about lists and sets, which
  are used in the cleanq proofs 
\<close>

theory CleanQ_Utils
(*<*) 
  imports Main
(*>*)
begin


lemma list_set_hd_tl_union:
  "\<And>L. L\<noteq>[] \<Longrightarrow> set (L) =  set([hd L] @ (tl L))"
  by(simp)

lemma list_set_hd_tl_union2:
  "L \<noteq> [] \<Longrightarrow> set(L) = set([hd L] @ (tl L))"
  by(simp)


lemma list_set_hd_tl_subtract: 
 assumes ne: "L \<noteq> []" and dist : "distinct L"
 shows "set (tl L) = set (L) - {hd L}"
proof -
  have X0 : "L = [hd L] @ tl L"
    by (simp add: ne)

  have X1: "set (L) = {hd L} \<union> set (tl L)"
    by(subst X0, simp)

  from dist X0 have dn :
    "{hd L} \<inter> set (tl L) = {}"
    apply(simp)
    using  distinct.simps(2) by fastforce

  show ?thesis 
    using ne dist X1 dn by(simp)
qed

lemma list_set_take_drop_subtract: 
 assumes ne: "L \<noteq> []" and dist : "distinct L"
 shows "set (drop 1 L) = set (L) - set (take 1 L)"
  by (simp add: drop_Suc list_set_hd_tl_subtract take_Suc dist ne)



lemma list_tail_drop_one:
  "tl L = drop 1 L"
  by (simp add: drop_Suc)

lemma list_head_take_one:
  "L \<noteq> [] \<Longrightarrow> [hd L] = take 1 L"
  by (simp add: take_Suc)

lemma list_head_take_one_set:
  "L \<noteq> [] \<Longrightarrow> set ([hd L]) = set(take 1 L)"
  by (simp add: take_Suc)

lemma list_head_take_one_set2:
  "L \<noteq> [] \<Longrightarrow> {hd L} = set(take 1 L)"
  by (simp add: take_Suc)

lemma list_distinct_drop_take_element:
  "distinct L \<Longrightarrow>  x \<in> set (drop n L) \<Longrightarrow> x \<notin> set (take n L)"
  by (metis append_take_drop_id disjoint_iff_not_equal distinct_append)

lemma list_drop_set_inter1:
  "set L \<inter> A = {} \<Longrightarrow> set (drop n L) \<inter> A = {}"
  using in_set_dropD by fastforce

lemma list_drop_set_inter2:
  "A \<inter> set L = {} \<Longrightarrow> A \<inter> set (drop n L) = {}"
  using in_set_dropD by fastforce

lemma list_take_set_inter1:
  "set L \<inter> A = {} \<Longrightarrow> set (take n L) \<inter> A = {}"
  by (meson disjoint_eq_subset_Compl order_trans set_take_subset)

lemma list_take_set_inter2:
  "A \<inter> set L = {} \<Longrightarrow> A \<inter> set (take n L) = {}"
  by (metis inf_commute list_take_set_inter1)

lemma list_distinct_drop_take_inter:
  "distinct L \<Longrightarrow>  set (drop n L) \<inter> set (take n L) = {}"
  by (meson Int_emptyI list_distinct_drop_take_element)

lemma list_take_drop_union_inters:
  "A \<inter> set L = {} \<Longrightarrow> distinct L \<Longrightarrow> (A \<union> set (take n L)) \<inter> set (drop n L) = {}"
  by (simp add: Int_Un_distrib inf_commute list_distinct_drop_take_inter list_drop_set_inter2)
  

lemma list_take_drop_cons:
  "L = take n L @ drop n L"
  by(auto)

lemma list_take_drop_union:
  "set L = set (take n L) \<union> set (drop n L)"
  using list_take_drop_cons by (metis set_append)


lemma singleton_set_list:
  "distinct L \<Longrightarrow> set (L) = {e} \<longleftrightarrow> L = [e]"
  by (metis Diff_Diff_Int Diff_empty empty_set hd_Cons_tl inf_bot_right insert_iff 
            list.set_cases list.simps(15) list.simps(3) list_set_hd_tl_subtract)


lemma list_length_1:
  "\<exists>e. (length L =  1) = (L = [e])"
  by (metis One_nat_def length_0_conv length_Suc_conv)


lemma list_distinct_tail_subset:
  "distinct L \<Longrightarrow> L \<noteq> [] \<Longrightarrow>  set (tl L) \<subset> set L"
  using list_set_hd_tl_subtract by fastforce


end