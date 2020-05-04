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

definition sr_mod_2 :: "(nat \<times> nat) set"
  where "sr_mod_2 = {(m,n). m mod 2 = n mod 2}"

definition fr_id :: "(nat \<times> nat) set"
  where "fr_id = {(m,n). m = n}"

lemma
  "(Language.Basic id, Language.Basic (\<lambda>x. x + 2)) \<in> refinement_s (separable_sr sr_mod_2 fr_id) \<Gamma>a \<Gamma>c"
  unfolding sr_mod_2_def by(auto intro:refinement_s_BasicI)

end