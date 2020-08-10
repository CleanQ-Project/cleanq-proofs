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

lemma list_distinct_drop_take_element:
  "distinct L \<Longrightarrow>  x \<in> set (drop n L) \<Longrightarrow> x \<notin> set (take n L)"
  by (metis append_take_drop_id disjoint_iff_not_equal distinct_append)

lemma list_distinct_drop_take_inter:
  "distinct L \<Longrightarrow>  set (drop n L) \<inter> set (take n L) = {}"
  by (meson Int_emptyI list_distinct_drop_take_element)

end