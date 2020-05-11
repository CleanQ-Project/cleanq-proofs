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



theory Refine_Mod2
  imports Refinements
begin

definition lift_mod_2 :: "nat \<Rightarrow> nat"
  where "lift_mod_2 = (\<lambda>n. n mod 2)"

lemma add_refines:
  "((\<Gamma>a,UNIV,Language.Basic id), (\<Gamma>c,UNIV,Language.Basic (\<lambda>n. n + 2)))
      \<in> refinement_s (separable_lift lift_mod_2 id)"
  unfolding lift_mod_2_def by(auto intro: refinement_s_BasicI)

lemma double_refines:
  "((\<Gamma>a,UNIV,Language.Basic (\<lambda>n. 0)), (\<Gamma>c,UNIV,Language.Basic (\<lambda>n. n * 2)))
      \<in> refinement_s (separable_lift lift_mod_2 id)"
  unfolding lift_mod_2_def by(auto intro: refinement_s_BasicI)

lemma halve_refines:
  "((\<Gamma>a,UNIV,Language.Basic (\<lambda>n. n + 1)),
    (\<Gamma>c,Semantic.Normal ` {n. n mod 4 = 2},Language.Basic (\<lambda>n. n div 2)))
      \<in> refinement_s (separable_lift lift_mod_2 id)"
  unfolding lift_mod_2_def
proof(rule refinement_s_BasicI, auto) (* XXX - not the way to do it. *)
  (* But here you're down to the object logic. *) 
  fix n::nat
  assume mod_4_2: "n mod 4 = 2"
  have "n = 4 * (n div 4) + (n mod 4)"
    by(simp)
  also from mod_4_2 have "... = 4 * (n div 4) + 2"
    by(simp)
  also have "... = (2 * (2 * (n div 4))) + 2"
    by(simp)
  finally have n_sum: "n = 2 * (2 * (n div 4)) + 2" .
  hence "n div 2 = ((2 * (2 * (n div 4))) + 2) div 2"
    by(simp)
  also have "... = (2 * (n div 4)) + (2 div 2)"
    by(simp)
  also have "... = 2 * (n div 4) + 1"
    by(simp)
  finally have "n div 2 mod 2 = (2 * (n div 4) + 1) mod 2"
    by(simp)
  also have "... = 1"
    by(simp)
  also {
    from n_sum have "n mod 2 = (2 * (2 * (n div 4)) + 2) mod 2"
      by(simp)
    also have "... = 0" by(simp)
    finally have "1 = Suc (n mod 2)" by(simp)
  }
  finally show "n div 2 mod 2 = Suc (n mod 2)" .
qed

(* XXX - SeqI needs to take a concrete hoare triple. *)

end