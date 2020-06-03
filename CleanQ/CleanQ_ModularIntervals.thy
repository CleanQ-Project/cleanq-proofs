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



theory CleanQ_ModularIntervals imports Main begin

locale nonzero_modulus =
  fixes N::nat
  assumes Npos: "0 < N"
begin

definition mod_dist :: "nat \<Rightarrow> nat \<Rightarrow> nat" (infixl "\<ominus>" 51)
  where "mod_dist a b = (LEAST i. (b + i) mod N = a mod N)"

lemma mod_dist_witness:
  fixes a b
  shows "\<exists>i. (b + i) mod N = a mod N"
proof
  have "(b + (((a mod N) + N) - b mod N)) mod N =
        (b mod N + (((a mod N) + N) - b mod N) mod N) mod N"
    by(simp add:mod_add_eq)
  also have "... = nat (int ((b mod N + (((a mod N) + N) - b mod N) mod N) mod N))"
    by(simp)
  also {
    have "int ((b mod N + (((a mod N) + N) - b mod N) mod N) mod N) =
          int (b mod N + (((a mod N) + N) - b mod N) mod N) mod int N"
      by(simp add:zmod_int)
    also {
      have "int (b mod N + (((a mod N) + N) - b mod N) mod N) =
            int (b mod N) + int ((((a mod N) + N) - b mod N) mod N)"
        by(simp)
      also have "... = int b mod int N + int ((((a mod N) + N) - b mod N)) mod int N"
        by(simp add:zmod_int)
      also {
        from Npos have "b mod N \<le> N" by(auto)
        also have "N \<le> (a mod N) + N" by(auto)
        finally have "int (((a mod N) + N) - b mod N) =
                      int ((a mod N) + N) - int (b mod N)"
          by(auto)
        hence "int b mod int N + int ((((a mod N) + N) - b mod N)) mod int N =
               int b mod int N + (int ((a mod N) + N) - int (b mod N)) mod int N"
          by(simp)
      }
      also have "int b mod int N + (int ((a mod N) + N) - int (b mod N)) mod int N =
                 int b mod int N + ((int (a mod N) + int N) - int (b mod N)) mod int N"
        by(simp)
      also have "... = int b mod int N + ((int a mod int N + int N) - int b mod int N) mod int N"
        by(simp add:zmod_int)
      finally have "int (b mod N + (((a mod N) + N) - b mod N) mod N) mod int N =
                    (int b mod int N +
                     ((int a mod int N + int N) - int b mod int N) mod int N) mod int N"
        by(simp)
    }
    also have "(int b mod int N + ((int a mod int N + int N) - int b mod int N) mod int N) mod int N =
               (int b mod int N + ((int a mod int N + int N) - int b mod int N)) mod int N"
      by(simp add:mod_add_right_eq)
    finally have "nat (int ((b mod N + (((a mod N) + N) - b mod N) mod N) mod N)) =
                  nat (int a mod int N)"
      by(simp add:ac_simps)
  }
  also have "nat (int a mod int N) = a mod N"
    by(fold zmod_int, simp)
  finally show "(b + (a mod N + N - b mod N)) mod N = a mod N" .
qed

lemma mod_dist_least:
  "\<And>a b i. (b + i) mod N = a mod N \<Longrightarrow> a \<ominus> b \<le> i"
  unfolding mod_dist_def by(auto intro:Least_le)

lemma mod_dist_left_inverse:
  "\<And>a b. (b + (a \<ominus> b)) mod N = a mod N"
  unfolding mod_dist_def by(rule LeastI_ex[OF mod_dist_witness])

lemma mod_dist_right_inverse:
  "\<And>a b. ((a \<ominus> b) + b) mod N = a mod N"
  using mod_dist_left_inverse by(simp add:ac_simps)

lemma mod_dist_bounded:
  fixes a b shows "a \<ominus> b < N"
proof(rule ccontr)
  assume "\<not> a \<ominus> b < N"
  hence Nle: "N \<le> a \<ominus> b" by(auto)
  hence "(b + ((a \<ominus> b) - N)) mod N = ((b + (a \<ominus> b)) - N) mod N" by(auto)
  also {
    from Nle have "N \<le> b + (a \<ominus> b)" by(auto)
    hence "((b + (a \<ominus> b)) - N) mod N = (b + (a \<ominus> b)) mod N"
      by(simp add:le_mod_geq[symmetric])
  }
  also note mod_dist_left_inverse
  finally have "a \<ominus> b \<le> (a \<ominus> b) - N"
    by(rule mod_dist_least)
  moreover from Nle Npos have "(a \<ominus> b) - N < a \<ominus> b" by(auto)
  ultimately show False by(auto)
qed

lemma mod_dist_unique:
  fixes a b i
  assumes iN: "i < N"
      and P: "(b + i) mod N = a mod N"
    shows "i = a \<ominus> b"
proof(rule contrapos_pp[OF iN])
  from P have ab_le: "a \<ominus> b \<le> i" by(rule mod_dist_least)
  hence "b + (a \<ominus> b) \<le> b + i" by(simp)
  moreover from P mod_dist_left_inverse
  have "(b + i) mod N = (b + (a \<ominus> b)) mod N" by(simp)
  ultimately obtain q where quot: "b + i = (b + (a \<ominus> b)) + N * q"
    by(blast dest:nat_mod_eq_lemma)

  assume "i \<noteq> a \<ominus> b"
  with quot have "0 < q" by(auto)
  hence "b + N * 1 \<le> (b + (a \<ominus> b)) + N * q"
    by(intro add_le_mono, auto)
  hence "b + N \<le> (b + (a \<ominus> b)) + N * q" by(simp)
  with quot have "N \<le> i" by(simp)
  thus "\<not> i < N" by(simp)
qed

lemma mod_dist_self:
  "a \<ominus> a = 0"
proof -
  have "(a + 0) mod N = a mod N" by(simp)
  hence "a \<ominus> a \<le> 0" by(rule mod_dist_least)
  thus "a \<ominus> a = 0" by(simp)
qed

lemma mod_dist_zero:
  fixes a b
  shows "a \<ominus> b = 0 \<Longrightarrow> a mod N = b mod N"
  using mod_dist_left_inverse[of b a] by(simp)

lemma mod_dist_modeq:
  "a mod N = b mod N \<Longrightarrow> a \<ominus> b = 0"
  unfolding mod_dist_def by(auto)

lemma mod_dist_rzero:
  "a \<ominus> 0 = a mod N"
proof -
  from mod_dist_bounded have "a \<ominus> 0 = (0 + (a \<ominus> 0)) mod N" by(simp)
  also have "(0 + (a \<ominus> 0)) mod N = a mod N" by(rule mod_dist_left_inverse)
  finally show ?thesis .
qed

lemma mod_dist_mod_right:
  "a \<ominus> b mod N = a \<ominus> b"
proof(rule antisym)
  have "(b + (a \<ominus> b mod N)) mod N =
        (b mod N + (a \<ominus> b mod N)) mod N"
    by(simp add:mod_add_left_eq)
  also have "... = a mod N"
    by(simp add:mod_dist_left_inverse)
  finally show "a \<ominus> b \<le> a \<ominus> b mod N"
    by(rule mod_dist_least)
next
  have "(b mod N + (a \<ominus> b)) mod N =
        (b + (a \<ominus> b)) mod N"
    by(simp add:mod_add_left_eq)
  also have "... = a mod N"
    by(simp add:mod_dist_left_inverse)
  finally show "a \<ominus> b mod N \<le> a \<ominus> b"
    by(rule mod_dist_least)
qed

lemma mod_dist_mod_left:
  "a mod N \<ominus> b = a \<ominus> b"
proof(rule antisym)
  have "(b + (a mod N \<ominus> b)) mod N = a mod N"
    by(simp add:mod_dist_left_inverse)
  thus "a \<ominus> b \<le> a mod N \<ominus> b"
    by(rule mod_dist_least)
next
  have "(b + (a \<ominus> b)) mod N = (a mod N) mod N"
    by(simp add:mod_dist_left_inverse)
  thus "a mod N \<ominus> b \<le> a \<ominus> b"
    by(rule mod_dist_least)
qed

lemmas mod_dist_simps =
  mod_dist_mod_left mod_dist_mod_right mod_dist_modeq mod_dist_self

definition between :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"  ("_ \<sqsubseteq> _ \<sqsubseteq> _" 200)
  where "between l x h \<longleftrightarrow> x \<ominus> l \<le> h \<ominus> l"

lemma squeezed_between:
  assumes abc: "a \<sqsubseteq> b \<sqsubseteq> c"
      and ca: "c = a"
      and aN: "a < N"
      and bN: "b < N"
    shows "b = a"
proof -
  from abc ca have "b \<ominus> a = 0" unfolding between_def by(auto simp:mod_dist_simps)
  hence "b mod N = a mod N" by(simp add:mod_dist_zero)
  with aN bN show ?thesis by(auto)
qed

definition between_strict :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"  ("_ \<sqsubseteq> _ \<sqsubset> _")
  where "between_strict l x h \<longleftrightarrow> x \<ominus> l < h \<ominus> l"

lemma between_strict_eq:
  assumes betw: "a \<sqsubseteq> b \<sqsubset> c"
  shows "a \<noteq> c"
proof(rule contrapos_pn[OF betw])
  assume eq: "a = c"
  with betw have "b = c"
    unfolding between_strict_def by(simp add:mod_dist_simps)
  thus "\<not> a \<sqsubseteq> b \<sqsubset> c"
    unfolding between_strict_def by(simp)
qed

lemma between_strict_between:
  "\<And>a b c. a \<sqsubseteq> b \<sqsubset> c \<Longrightarrow> a \<sqsubseteq> b \<sqsubseteq> c"
  unfolding between_def between_strict_def by(auto)

lemma mod_dist_triangle:
  fixes a b c shows "c \<ominus> a \<le> (c \<ominus> b) + (b \<ominus> a)"
proof -
  have "(a + ((c \<ominus> b) + (b \<ominus> a))) mod N =
        ((c \<ominus> b) + ((b \<ominus> a) + a)) mod N"
    by(simp add:ac_simps)
  also have "... = ((c \<ominus> b) mod N + ((b \<ominus> a) + a) mod N) mod N"
    by(simp add:mod_add_eq)
  also have "... = ((c \<ominus> b) mod N + b mod N) mod N"
    by(simp add:mod_dist_right_inverse)
  also have "... = ((c \<ominus> b) + b) mod N"
    by(simp add:mod_add_eq)
  also have "... = c mod N"
    by(simp add:mod_dist_right_inverse)
  finally show "c \<ominus> a \<le> (c \<ominus> b) + (b \<ominus> a)"
    by(rule mod_dist_least)
qed

lemma interval_split:
  assumes betw: "a \<sqsubseteq> b \<sqsubseteq> c"
  shows "(c \<ominus> b) + (b \<ominus> a) = c \<ominus> a"
proof(rule antisym[OF _ mod_dist_triangle], rule ccontr)
  assume "\<not> (c \<ominus> b) + (b \<ominus> a) \<le> c \<ominus> a"
  hence less: "c \<ominus> a < (c \<ominus> b) + (b \<ominus> a)" by(simp)

  from betw have le_ba: "b \<ominus> a \<le> c \<ominus> a" by(simp add:between_def)

  let ?i = "(c \<ominus> a) - (b \<ominus> a)"
  have "(b + ?i) mod N = (?i + b) mod N"
    by(simp add:ac_simps)
  also have "... = (?i mod N + b mod N) mod N"
    by(simp add:mod_add_eq)
  also have "... = (?i mod N + ((b \<ominus> a) + a) mod N) mod N"
    by(simp add:mod_dist_right_inverse)
  also have "... = (?i + ((b \<ominus> a) + a)) mod N"
    by(simp add:mod_add_eq)
  also from le_ba have "... = ((c \<ominus> a) + a) mod N"
    by(simp add:ac_simps)
  also have "... = c mod N"
    by(simp add:mod_dist_right_inverse)
  finally have X: "c \<ominus> b \<le> ?i"
    by(rule mod_dist_least)

  with less have "(c \<ominus> a) + (c \<ominus> b) < ((c \<ominus> b) + (b \<ominus> a)) + ((c \<ominus> a) - (b \<ominus> a))"
    by(auto)
  with le_ba show False by(simp)
qed

lemmas interval_split_strict = interval_split[OF between_strict_between]

lemma between_extend_right:
  assumes abc: "a \<sqsubseteq> b \<sqsubseteq> c"
      and axb: "a \<sqsubseteq> x \<sqsubset> b"
    shows "a \<sqsubseteq> x \<sqsubset> c"
  using assms unfolding between_def between_strict_def by(auto)

lemma between_strict_rhs:
    fixes a b c
  assumes betw: "a \<sqsubseteq> b \<sqsubset> c"
    shows "0 < c \<ominus> b"
proof(rule contrapos_pp[OF betw])
  assume "\<not> 0 < c \<ominus> b"
  hence "c \<ominus> b = 0" by(auto)
  moreover from betw have "(c \<ominus> b) + (b \<ominus> a) = c \<ominus> a"
    by(rule interval_split_strict)
  ultimately have "b \<ominus> a = c \<ominus> a" by(simp)
  thus "\<not> a \<sqsubseteq> b \<sqsubset> c" by(simp add:between_strict_def)
qed

lemma between_strict_disj:
  assumes abc: "a \<sqsubseteq> b \<sqsubseteq> c"
      and axb: "a \<sqsubseteq> x \<sqsubset> c"
    obtains (Left) "a \<sqsubseteq> x \<sqsubset> b" |
            (Right) "b \<sqsubseteq> x \<sqsubset> c"
proof(cases "x \<ominus> a < b \<ominus> a")
  case True thus thesis by(auto simp:between_strict_def intro:Left)
next
  case False
  hence le_bx: "b \<ominus> a \<le> x \<ominus> a" by(auto)
  hence abx: "a \<sqsubseteq> b \<sqsubseteq> x" by(simp add:between_def)

  from axb have part_axb: "c \<ominus> a = (c \<ominus> x) + (x \<ominus> a)"
    by(simp add:interval_split_strict)
  moreover from abx have "x \<ominus> a = (x \<ominus> b) + (b \<ominus> a)"
    by(simp add:interval_split)
  ultimately have "c \<ominus> a = (c \<ominus> x) + (x \<ominus> b) + (b \<ominus> a)"
    by(simp)
  moreover from abc have "c \<ominus> a = (c \<ominus> b) + (b \<ominus> a)"
    by(simp add:interval_split)
  ultimately have "c \<ominus> b = (c \<ominus> x) + (x \<ominus> b)"
    by(simp)
  moreover from axb have "0 < c \<ominus> x"
    by(rule between_strict_rhs)
  ultimately have "x \<ominus> b < c \<ominus> b"
    by(auto)
  hence "b \<sqsubseteq> x \<sqsubset> c"
    by(simp add:between_strict_def)
  thus thesis
    by(rule Right)
qed

lemma between_lhs:
  "\<And>a b. a \<sqsubseteq> a \<sqsubseteq> b"
  unfolding between_def by(simp add:mod_dist_simps)

lemma between_rhs:
  "\<And>a b. a \<sqsubseteq> b \<sqsubseteq> b"
  unfolding between_def by(simp)

lemma between_mod_left_iff:
  "\<And>a b c. (a mod N \<sqsubseteq> b \<sqsubseteq> c) = (a \<sqsubseteq> b \<sqsubseteq> c)"
  by(simp add:between_def mod_dist_simps)

lemma between_mod_middle_iff:
  "\<And>a b c. (a \<sqsubseteq> b mod N \<sqsubseteq> c) = (a \<sqsubseteq> b \<sqsubseteq> c)"
  by(simp add:between_def mod_dist_simps)

lemma between_mod_right_iff:
  "\<And>a b c. (a \<sqsubseteq> b \<sqsubseteq> c mod N) = (a \<sqsubseteq> b \<sqsubseteq> c)"
  by(simp add:between_def mod_dist_simps)

lemma between_strict_mod_left_iff:
  "\<And>a b c. (a mod N \<sqsubseteq> b \<sqsubset> c) = (a \<sqsubseteq> b \<sqsubset> c)"
  by(simp add:between_strict_def mod_dist_simps)

lemma between_strict_mod_middle_iff:
  "\<And>a b c. (a \<sqsubseteq> b mod N \<sqsubset> c) = (a \<sqsubseteq> b \<sqsubset> c)"
  by(simp add:between_strict_def mod_dist_simps)

lemma between_strict_mod_right_iff:
  "\<And>a b c. (a \<sqsubseteq> b \<sqsubset> c mod N) = (a \<sqsubseteq> b \<sqsubset> c)"
  by(simp add:between_strict_def mod_dist_simps)

lemmas between_simps =
  between_lhs between_rhs
  between_mod_left_iff between_mod_middle_iff between_mod_right_iff
  between_strict_mod_left_iff between_strict_mod_middle_iff between_strict_mod_right_iff

lemma between_disj:
  assumes abc: "a \<sqsubseteq> b \<sqsubseteq> c"
      and axb: "a \<sqsubseteq> x \<sqsubseteq> c"
    obtains (Left) "a \<sqsubseteq> x \<sqsubseteq> b" |
            (Right) "b \<sqsubseteq> x \<sqsubseteq> c"
proof(cases "x mod N = c mod N")
  case True
  hence "b \<sqsubseteq> x mod N \<sqsubseteq> c mod N" by(simp add:between_simps)
  hence "b \<sqsubseteq> x \<sqsubseteq> c" by(simp add:between_simps)
  thus thesis by(rule Right)
next
  case False
  hence "0 < c \<ominus> x"
    by(auto intro:mod_dist_zero[symmetric])
  moreover from axb have "c \<ominus> a = (c \<ominus> x) + (x \<ominus> a)"
    by(simp add:interval_split)
  ultimately have "x \<ominus> a < c \<ominus> a"
    by(auto)
  hence "a \<sqsubseteq> x \<sqsubset> c" by(simp add:between_strict_def)
  with abc show thesis
    by(blast intro:between_strict_disj between_strict_between Left Right)
qed

lemma between_extend_left:
  assumes abc: "a \<sqsubseteq> b \<sqsubseteq> c"
      and bxc: "b \<sqsubseteq> x \<sqsubset> c"
    shows "a \<sqsubseteq> x \<sqsubset> c"
proof -
  have "x \<ominus> a \<le> (x \<ominus> b) + (b \<ominus> a)"
    by(rule mod_dist_triangle)
  also {
    from abc bxc have part: "(c \<ominus> x) + (x \<ominus> b) + (b \<ominus> a) = c \<ominus> a"
      by(simp add:interval_split interval_split_strict)
    moreover from bxc have "0 < c \<ominus> x" by(rule between_strict_rhs)
    ultimately have "(x \<ominus> b) + (b \<ominus> a) < c \<ominus> a" by(auto)
  }
  finally show ?thesis by(simp add:between_strict_def)
qed

definition set_between :: "nat \<Rightarrow> nat \<Rightarrow> nat set" (infix "upto" 500)
  where "l upto h = {i. i < N \<and> (l \<sqsubseteq> i \<sqsubset> h)}"

lemma upto_eq:
  assumes eq: "l = h"
  shows "l upto h = {}"
proof
  show "{} \<subseteq> l upto h" by(auto)
  show "l upto h \<subseteq> {}"
  proof
    fix x
    assume "x \<in> l upto h"
    hence "l \<noteq> h" unfolding set_between_def
      by(auto dest:between_strict_eq)
    with eq show "x \<in> {}" by(auto)
  qed
qed

lemma upto_mono_right:
  "\<And>a b c. a \<sqsubseteq> b \<sqsubseteq> c \<Longrightarrow> a upto b \<subseteq> a upto c"
  unfolding set_between_def by(auto dest:between_extend_right)

lemma upto_mono_left:
  "\<And>a b c. a \<sqsubseteq> b \<sqsubseteq> c \<Longrightarrow> b upto c \<subseteq> a upto c"
  unfolding set_between_def by(auto dest:between_extend_left)

lemma upto_between_strict_eq:
  "(b < N \<and> a \<sqsubseteq> b \<sqsubset> c) = (b \<in> a upto c)"
  unfolding set_between_def between_strict_def by(auto)

lemma upto_union:
  assumes abc: "a \<sqsubseteq> b \<sqsubseteq> c"
  shows "a upto b \<union> b upto c = a upto c"
proof(intro antisym subsetI)
  fix x
  assume "x \<in> a upto b \<union> b upto c"
  thus "x \<in> a upto c"
  proof(rule UnE)
    assume "x \<in> a upto b"
    with abc show "x \<in> a upto c" by(auto dest:upto_mono_right)
  next
    assume "x \<in> b upto c"
    with abc show "x \<in> a upto c" by(auto dest:upto_mono_left)
  qed
next
  fix x
  assume "x \<in> a upto c"
  hence "a \<sqsubseteq> x \<sqsubset> c" and "x < N" by(simp_all add:set_between_def)
  with abc show "x \<in> a upto b \<union> b upto c"
    by(cases rule:between_strict_disj, simp_all add:set_between_def)
qed

lemma upto_inter:
  assumes abc: "a \<sqsubseteq> b \<sqsubseteq> c"
  shows "a upto b \<inter> b upto c = {}"
proof(intro iffD1[OF subset_empty] subsetI)
  fix x
  assume "x \<in> a upto b \<inter> b upto c"
  hence btw_axb: "a \<sqsubseteq> x \<sqsubset> b" and "b \<sqsubseteq> x \<sqsubset> c" by(simp_all add:set_between_def)
  hence part_axb: "b \<ominus> a = (b \<ominus> x) + (x \<ominus> a)" and pos_bx: "0 < b \<ominus> x"
    and part_bxc: "c \<ominus> b = (c \<ominus> x) + (x \<ominus> b)"
    by(auto dest:interval_split_strict between_strict_rhs)

  from abc have "c \<ominus> a = (c \<ominus> b) + (b \<ominus> a)" by(simp add:interval_split)
  with part_axb part_bxc
  have part_ac: "c \<ominus> a = (c \<ominus> x) + (x \<ominus> b) + (b \<ominus> x) + (x \<ominus> a)"
    by(simp)

  from abc btw_axb have "a \<sqsubseteq> x \<sqsubset> c" by(rule between_extend_right)
  hence "c \<ominus> a = (c \<ominus> x) + (x \<ominus> a)" by(simp add:interval_split_strict)
  txt {* Derive a contradiction. *}
  with part_ac pos_bx show "x \<in> {}" by(simp)
qed

(*
lemma send_help_2:
  "\<And>a c. ((c \<ominus> a) + 1) \<noteq> N \<Longrightarrow> (c \<ominus> a) + 1 = ((c+1) \<ominus> a)"
  sorry 

lemma send_help:
  fixes a :: "nat" and c :: "nat"
  assumes a1: "0 < a \<ominus> (c+1)"
  shows "(c \<ominus> a) \<le> ((c+1) \<ominus> a)"
proof -
  from a1 have "((c \<ominus> a) + 1) \<noteq> N" 
  have hx: "((c \<ominus> a) + 1) \<noteq> N" sorry
  have "((c + 1) \<ominus> a) = (c \<ominus> a) + 1" using hx send_help_2 by(auto)
  thus ?thesis by(auto)
qed

lemma tail_increment:
  fixes a :: "nat" and b :: "nat" and c :: "nat"
  assumes a1: "a \<sqsubseteq> b \<sqsubseteq> c"
      and a2: "b \<sqsubseteq> (c+1) \<sqsubset> a" (* c + 1 mod N /= a *)
    shows "a \<sqsubseteq> b \<sqsubseteq> (c+1)"
proof -
  from a1 have hx1: "(b \<ominus> a \<le> c \<ominus> a)" using between_def by(simp)
  from a2 have h1: "a \<ominus> (c+1) > 0" using between_strict_rhs by(blast)
  have h2: "(c \<ominus> a) \<le> ((c+1) \<ominus> a)" using h1 by(simp only:send_help)
  from hx1 h2 have "b \<ominus> a \<le> ((c+1) \<ominus> a)" by(auto)
  thus ?thesis by(auto simp: between_def)
qed
*)

end (* locale nonzero_modulus *)

end