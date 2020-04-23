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



theory SimplEmbedding imports "Simpl/Simpl" "Complx/OG_Hoare" begin

text \<open>All primitves are embedded 1-1\<close>
primrec embedSimpl :: "('s, 'p, 'f) Language.com \<Rightarrow> ('s, 'p, 'f) OG_Language.com"
  where
    "embedSimpl Language.com.Skip = OG_Language.com.Skip"
  | "embedSimpl (Language.com.Basic f) = OG_Language.com.Basic f"
  | "embedSimpl (Language.com.Spec S) = OG_Language.com.Spec S"
  | "embedSimpl (Language.com.Seq a b) = OG_Language.com.Seq (embedSimpl a) (embedSimpl b)"
  | "embedSimpl (Language.com.Cond G a b) = OG_Language.com.Cond G (embedSimpl a) (embedSimpl b)"
  | "embedSimpl (Language.com.While G b) = OG_Language.com.While G (embedSimpl b)"
  | "embedSimpl (Language.com.Call p) = OG_Language.com.Call p"
  | "embedSimpl (Language.com.DynCom dc) = OG_Language.com.DynCom (embedSimpl o dc)"
  | "embedSimpl (Language.com.Guard f G b) = OG_Language.com.Guard f G (embedSimpl b)"
  | "embedSimpl Language.com.Throw = OG_Language.com.Throw"
  | "embedSimpl (Language.com.Catch a b) = OG_Language.com.Catch (embedSimpl a) (embedSimpl b)"

definition embedContext :: "('s,'p,'f) Semantic.body \<Rightarrow> ('s,'p,'f) OG_SmallStep.body"
  where
    "embedContext \<Gamma> = (\<lambda>x. case x of None \<Rightarrow> None | Some c \<Rightarrow> Some (embedSimpl c)) o \<Gamma>"

text \<open>The Simpl-Complx state relation is 1-1, but excludes the Simpl Abrupt state.\<close>
function (sequential) stateRel :: "('s, 'f) Semantic.xstate \<Rightarrow> ('s, 'f) OG_SmallStep.xstate \<Rightarrow> bool"
  where
    "stateRel (Semantic.Normal s) (OG_SmallStep.Normal s_og) \<longleftrightarrow> s = s_og"
  | "stateRel (Semantic.Fault f) (OG_SmallStep.Fault f_og) \<longleftrightarrow> f = f_og"
  | "stateRel Semantic.Stuck OG_SmallStep.Stuck \<longleftrightarrow> True"
  | "stateRel xs xs_og \<longleftrightarrow> False"
  by(pat_completeness, auto)
termination by(lexicographic_order)

lemma stateRel_fw_Normal:
  "stateRel (Semantic.Normal s) xs_og \<Longrightarrow> xs_og = OG_SmallStep.Normal s"
  by(cases xs_og, auto)

lemma stateRel_rev_Normal:
  "stateRel xs (OG_SmallStep.Normal s) \<Longrightarrow> xs = Semantic.Normal s"
  by(cases xs, auto)

lemma stateRel_fw_Fault:
  "stateRel (Semantic.Fault f) xs_og \<Longrightarrow> xs_og = OG_SmallStep.Fault f"
  by(cases xs_og, auto)

lemma stateRel_rev_Fault:
  "stateRel xs (OG_SmallStep.Fault f) \<Longrightarrow> xs = Semantic.Fault f"
  by(cases xs, auto)

lemma stateRel_fw_Stuck:
  "stateRel Semantic.Stuck xs_og \<Longrightarrow> xs_og = OG_SmallStep.Stuck"
  by(cases xs_og, auto)

lemma stateRel_rev_Stuck:
  "stateRel xs OG_SmallStep.Stuck \<Longrightarrow> xs = Semantic.Stuck"
  by(cases xs, auto)

lemma stateRel_no_Abrupt:
  "stateRel xs xs_og \<Longrightarrow> \<not>isAbr xs"
  by(cases xs, auto)

lemmas stateRel_rewrites =
  stateRel_fw_Normal stateRel_rev_Normal
  stateRel_fw_Fault stateRel_rev_Fault
  stateRel_fw_Stuck stateRel_rev_Stuck
  stateRel_no_Abrupt

definition wf_com :: "('s, 'p, 'f) Language.com \<Rightarrow> bool"
  where "wf_com c = True"

lemma wf_comI: "wf_com c" by(simp add:wf_com_def)

thm OG_SmallStep.step_elim_cases

lemma final_cases:
  assumes "OG_SmallStep.final (c,xs)"
  obtains (Skip) "c = OG_Language.Skip" | 
          (Throw) s where "c = OG_Language.Throw" and "xs = OG_SmallStep.Normal s"
  using assms unfolding final_def by(auto)

primrec og_com_size :: "('s,'p,'f) OG_Language.com \<Rightarrow> nat"
  where "og_com_size Skip = 1" |
        "og_com_size (Basic f) = 1" |
        "og_com_size (Spec r) = 1" |
        "og_com_size (Seq c1 c2) = og_com_size c1 + og_com_size c2 + 1" |
        "og_com_size (Cond b c1 c2) = og_com_size c1 + og_com_size c2 + 1" |
        "og_com_size (While b c) = og_com_size c + 1" |
        "og_com_size (Call p) = 1" |
        "og_com_size (DynCom d) = 1" |
        "og_com_size (Guard f g c) = og_com_size c + 1" |
        "og_com_size Throw = 1" |
        "og_com_size (Catch c1 c2) = og_com_size c1 + og_com_size c2 + 1" |
        "og_com_size (Parallel s) = (sum_list (map og_com_size s)) + 1" |
        "og_com_size (Await g c) = og_com_size c + 1"

lemma redex_size_le:
  "og_com_size (redex c) \<le> og_com_size c"
  by(induct c, auto)

lemma redex_Seq_ne:
  fixes c1 c2
  shows "redex (Seq c1 c2) \<noteq> Seq c1 c2"
proof
  assume "redex (Seq c1 c2) = Seq c1 c2"
  hence "og_com_size (Seq c1 c2) = og_com_size (redex c1)"
    by(simp)
  also from redex_size_le have "... \<le> og_com_size c1"
    by(auto)
  also have "... < og_com_size (Seq c1 c2)"
    by(simp)
  finally show False
    by(simp)
qed

lemma redex_Catch_ne:
  fixes c1 c2
  shows "redex (Catch c1 c2) \<noteq> Catch c1 c2"
proof
  assume "redex (Catch c1 c2) = Catch c1 c2"
  hence "og_com_size (Catch c1 c2) = og_com_size (redex c1)"
    by(simp)
  also from redex_size_le have "... \<le> og_com_size c1"
    by(auto)
  also have "... < og_com_size (Catch c1 c2)"
    by(simp)
  finally show False
    by(simp)
qed

text \<open>The embedding is closed: For any step of the embedded computation, we can find a step
in the Simpl semantics that corresponds to it.\<close>
lemma embedSimpl_fwd_refine:
  assumes sr: "stateRel xs xs_og"
      and embed_step: "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl c, xs_og) (c_og', xs_og')"
    shows "\<exists>c' xs'. c_og' = embedSimpl c' \<and> SmallStep.step \<Gamma> (c, xs) (c', xs') \<and> stateRel xs' xs_og'"
  using embed_step
proof(induct c arbitrary:c_og' xs_og')
  case Skip
  with embed_step show ?case
    by(auto intro:OG_SmallStep.no_step_final[unfolded OG_SmallStep.final_def])
next
  case (Basic f)

  from Basic.prems[simplified] show ?case
  proof(cases rule:OG_SmallStep.step_elim_cases(3))
    case (1 s)
    from 1 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 1 have "stateRel (Semantic.Normal (f s)) xs_og'" by(simp)
    moreover {
      from 1 sr have "xs = Semantic.Normal s" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.Basic f, xs) (Language.Skip, Semantic.Normal (f s))"
        by(auto intro:SmallStep.step.Basic)
    } 
    ultimately show ?thesis by(blast)
  next
    case (2 flt)
    from 2 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 2 have "stateRel (Semantic.Fault flt) xs_og'" by(simp)
    moreover {
      from 2 sr have "xs = Semantic.Fault flt" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.Basic f, xs) (Language.Skip, Semantic.Fault flt)"
        by(auto intro:SmallStep.step.FaultProp)
    }
    ultimately show ?thesis by(blast)
  next
    case 3
    from 3 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 3 have "stateRel Semantic.Stuck xs_og'" by(simp)
    moreover {
      from 3 sr have "xs = Semantic.Stuck" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.Basic f, xs) (Language.Skip, Semantic.Stuck)"
        by(auto intro:SmallStep.step.StuckProp)
    }
    ultimately show ?thesis by(blast)
  qed

next
  case (Spec r)

  from Spec.prems[simplified] show ?case
  proof(cases rule:OG_SmallStep.step_elim_cases(4))
    case (1 s t)
    from 1 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 1 have "stateRel (Semantic.Normal t) xs_og'" by(simp)
    moreover {
      from 1 sr have "xs = Semantic.Normal s" by(cases xs, auto)
      with 1 have "SmallStep.step \<Gamma> (Language.Spec r, xs) (Language.Skip, Semantic.Normal t)"
        by(auto intro:SmallStep.step.Spec)
    }
    ultimately show ?thesis by(blast)
  next
    case (2 s)
    from 2 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 2 have "stateRel Semantic.Stuck xs_og'" by(simp)
    moreover {
      from 2 sr have "xs = Semantic.Normal s" by(cases xs, auto)
      with 2 have "SmallStep.step \<Gamma> (Language.Spec r, xs) (Language.Skip, Semantic.Stuck)"
        by(auto intro:SmallStep.step.SpecStuck)
    }
    ultimately show ?thesis by(blast)
  next
    case (3 flt)
    from 3 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 3 have "stateRel (Semantic.Fault flt) xs_og'" by(simp)
    moreover {
      from 3 sr have "xs = Semantic.Fault flt" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.Spec r, xs) (Language.Skip, Semantic.Fault flt)"
        by(auto intro:SmallStep.step.FaultProp)
    }
    ultimately show ?thesis by(blast)
  next
    case 4
    from 4 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 4 have "stateRel Semantic.Stuck xs_og'" by(simp)
    moreover {
      from 4 sr have "xs = Semantic.Stuck" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.Spec r, xs) (Language.Skip, Semantic.Stuck)"
        by(auto intro:SmallStep.step.StuckProp)
    }
    ultimately show ?thesis by(blast)
  qed

next
  case (Seq c1 c2)

  from Seq.prems[simplified] show ?case
  proof(cases rule:OG_SmallStep.step_elim_cases(5))
    case (1 c1_og s_og)
    with Seq.hyps(1) obtain c' xs'
      where embed_IH: "c1_og = embedSimpl c'"
        and step_IH: "SmallStep.step \<Gamma> (c1, xs) (c', xs')"
        and sr_IH: "stateRel xs' s_og"
      by(blast)

    from 1 embed_IH
    have "c_og' = embedSimpl (Language.Seq c' c2)" by(simp)

    moreover from 1 sr_IH
    have "stateRel xs' xs_og'" by(simp)

    moreover from step_IH
    have "SmallStep.step \<Gamma> (Language.Seq c1 c2, xs) (Language.Seq c' c2, xs')"
      by(rule SmallStep.step.Seq)

    ultimately show ?thesis by(blast)
  next
    case 2
    from 2 have "c_og' = embedSimpl c2" by(simp)
    moreover from 2 sr have "stateRel xs xs_og'" by(simp)
    moreover {
      from 2 have "c1 = Language.Skip" by(cases c1, auto)
      hence "SmallStep.step \<Gamma> (Language.Seq c1 c2, xs) (c2, xs)"
        by(auto intro:SmallStep.step.SeqSkip)
    }
    ultimately show ?thesis by(blast)
  next
    case (3 s)
    from 3 have "c_og' = embedSimpl Language.Throw" by(simp)
    moreover from 3 sr have "stateRel xs xs_og'" by(simp)
    moreover {
      from 3 have "c1 = Language.Throw" by(cases c1, auto)
      moreover from 3 sr have "xs = Semantic.Normal s" by(cases xs, auto)
      ultimately have "SmallStep.step \<Gamma> (Language.Seq c1 c2, xs) (Language.Throw, xs)"
        by(auto intro:SmallStep.step.SeqThrow)
    }
    ultimately show ?thesis by(blast)
  next
    case (4 f)
    with redex_Seq_ne show ?thesis by(blast)
  next
    case 5
    with redex_Seq_ne show ?thesis by(blast)
  qed

next
  case (Cond b c1 c2)

  from Cond.prems[simplified] show ?case
  proof(cases rule:OG_SmallStep.step_elim_cases(6))
    case (1 s)
    from 1 have "c_og' = embedSimpl c1" by(simp)
    moreover from 1 sr have "stateRel xs xs_og'" by(simp)
    moreover {
      from 1 sr have "xs = Semantic.xstate.Normal s" by(cases xs, auto)
      with 1 have "SmallStep.step \<Gamma> (Language.Cond b c1 c2, xs) (c1, xs)"
        by(auto intro:SmallStep.step.CondTrue)
    }
    ultimately show ?thesis by(blast)
  next
    case (2 s)
    from 2 have "c_og' = embedSimpl c2" by(simp)
    moreover from 2 sr have "stateRel xs xs_og'" by(simp)
    moreover {
      from 2 sr have "xs = Semantic.xstate.Normal s" by(cases xs, auto)
      with 2 have "SmallStep.step \<Gamma> (Language.Cond b c1 c2, xs) (c2, xs)"
        by(auto intro:SmallStep.step.CondFalse)
    }
    ultimately show ?thesis by(blast)
  next
    case (3 flt)
    from 3 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 3 have "stateRel (Semantic.Fault flt) xs_og'" by(simp)
    moreover {
      from 3 sr have "xs = Semantic.Fault flt" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.Cond b c1 c2, xs) (Language.Skip, Semantic.Fault flt)"
        by(auto intro:SmallStep.step.FaultProp)
    }
    ultimately show ?thesis by(blast)
  next
    case 4
    from 4 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 4 have "stateRel Semantic.Stuck xs_og'" by(simp)
    moreover {
      from 4 sr have "xs = Semantic.Stuck" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.Cond b c1 c2, xs) (Language.Skip, Semantic.Stuck)"
        by(auto intro:SmallStep.step.StuckProp)
    }
    ultimately show ?thesis by(blast)
  qed

next
  case (While b c)

  from While.prems[simplified] show ?case
  proof(cases rule:OG_SmallStep.step_elim_cases(7))
    case (1 s)
    from 1 have "c_og' = embedSimpl (Language.Seq c (Language.While b c))" by(simp)
    moreover from 1 sr have "stateRel xs xs_og'" by(simp)
    moreover {
      from 1 sr have "xs = Semantic.xstate.Normal s" by(cases xs, auto)
      with 1 have "SmallStep.step \<Gamma> (Language.While b c, xs) (Language.Seq c (Language.While b c), xs)"
        by(auto intro:SmallStep.step.WhileTrue)
    }
    ultimately show ?thesis by(blast)
  next
    case (2 s)
    from 2 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 2 sr have "stateRel xs xs_og'" by(simp)
    moreover {
      from 2 sr have "xs = Semantic.xstate.Normal s" by(cases xs, auto)
      with 2 have "SmallStep.step \<Gamma> (Language.While b c, xs) (Language.Skip, xs)"
        by(auto intro:SmallStep.step.WhileFalse)
    }
    ultimately show ?thesis by(blast)
  next
    case (3 flt)
    from 3 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 3 have "stateRel (Semantic.Fault flt) xs_og'" by(simp)
    moreover {
      from 3 sr have "xs = Semantic.Fault flt" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.While b c, xs) (Language.Skip, Semantic.Fault flt)"
        by(auto intro:SmallStep.step.FaultProp)
    }
    ultimately show ?thesis by(blast)
  next
    case 4
    from 4 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 4 have "stateRel Semantic.Stuck xs_og'" by(simp)
    moreover {
      from 4 sr have "xs = Semantic.Stuck" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.While b c, xs) (Language.Skip, Semantic.Stuck)"
        by(auto intro:SmallStep.step.StuckProp)
    }
    ultimately show ?thesis by(blast)
  qed

next
  case (Call p)

  from Call.prems[simplified] show ?case
  proof(cases rule:OG_SmallStep.step_elim_cases(8))
    case (1 b_og s)
    from 1 obtain b where b_og_rw:"b_og = embedSimpl b" and lookup: "\<Gamma> p = Some b"
      unfolding embedContext_def o_def
      by(cases "\<Gamma> p", auto)
    with 1 have "c_og' = embedSimpl b" by(simp)
    moreover from 1 sr have "stateRel xs xs_og'" by(simp)
    moreover {
      from 1 sr have "xs = Semantic.xstate.Normal s" by(cases xs, auto)
      with lookup have "SmallStep.step \<Gamma> (Language.Call p, xs) (b, xs)"
        by(auto intro:SmallStep.step.Call)
    }
    ultimately show ?thesis by(blast)
  next
    case (2 s)
    with 2 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 2 sr have "stateRel Semantic.Stuck xs_og'" by(simp)
    moreover {
      from 2 sr have "xs = Semantic.xstate.Normal s" by(cases xs, auto)
      moreover from 2 have "\<Gamma> p = None"
        unfolding embedContext_def o_def
        by(cases "\<Gamma> p", auto)
      ultimately have "SmallStep.step \<Gamma> (Language.Call p, xs) (Language.Skip, Semantic.Stuck)"
        by(auto intro:SmallStep.step.CallUndefined)
    }
    ultimately show ?thesis by(blast)
  next
    case (3 flt)
    from 3 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 3 have "stateRel (Semantic.Fault flt) xs_og'" by(simp)
    moreover {
      from 3 sr have "xs = Semantic.Fault flt" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.Call p, xs) (Language.Skip, Semantic.Fault flt)"
        by(auto intro:SmallStep.step.FaultProp)
    }
    ultimately show ?thesis by(blast)
  next
    case 4
    from 4 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 4 have "stateRel Semantic.Stuck xs_og'" by(simp)
    moreover {
      from 4 sr have "xs = Semantic.Stuck" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.Call p, xs) (Language.Skip, Semantic.Stuck)"
        by(auto intro:SmallStep.step.StuckProp)
    }
    ultimately show ?thesis by(blast)
  qed

next
  case (DynCom c)

  from DynCom.prems[simplified] show ?case
  proof(cases rule:OG_SmallStep.step_elim_cases(9))
    case (1 s)
    from 1 have "c_og' = embedSimpl (c s)" by(simp)
    moreover from 1 sr have "stateRel xs xs_og'" by(simp)
    moreover {
      from 1 sr have "xs = Semantic.xstate.Normal s" by(cases xs, auto)
      with 1 have "SmallStep.step \<Gamma> (Language.DynCom c, xs) (c s, xs)"
        by(auto intro:SmallStep.step.DynCom)
    }
    ultimately show ?thesis by(blast)
  next
    case (2 flt)
    from 2 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 2 have "stateRel (Semantic.Fault flt) xs_og'" by(simp)
    moreover {
      from 2 sr have "xs = Semantic.Fault flt" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.DynCom c, xs) (Language.Skip, Semantic.Fault flt)"
        by(auto intro:SmallStep.step.FaultProp)
    }
    ultimately show ?thesis by(blast)
  next
    case 3
    from 3 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 3 have "stateRel Semantic.Stuck xs_og'" by(simp)
    moreover {
      from 3 sr have "xs = Semantic.Stuck" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.DynCom c, xs) (Language.Skip, Semantic.Stuck)"
        by(auto intro:SmallStep.step.StuckProp)
    }
    ultimately show ?thesis by(blast)
  qed

next
  case (Guard f g c)

  from Guard.prems[simplified] show ?case
  proof(cases rule:OG_SmallStep.step_elim_cases(2))
    case (1 s)
    from 1 have "c_og' = embedSimpl c" by(simp)
    moreover from 1 sr have "stateRel xs xs_og'" by(simp)
    moreover {
      from 1 sr have "xs = Semantic.xstate.Normal s" by(cases xs, auto)
      with 1 have "SmallStep.step \<Gamma> (Language.Guard f g c, xs) (c, xs)"
        by(auto intro:SmallStep.step.Guard)
    }
    ultimately show ?thesis by(blast)
  next
    case (2 s)
    from 2 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 2 sr have "stateRel (Semantic.Fault f) xs_og'" by(simp)
    moreover {
      from 2 sr have "xs = Semantic.xstate.Normal s" by(cases xs, auto)
      with 2 have "SmallStep.step \<Gamma> (Language.Guard f g c, xs) (Language.Skip, Semantic.Fault f)"
        by(auto intro:SmallStep.step.GuardFault)
    }
    ultimately show ?thesis by(blast)
  next
    case (3 flt)
    from 3 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 3 have "stateRel (Semantic.Fault flt) xs_og'" by(simp)
    moreover {
      from 3 sr have "xs = Semantic.Fault flt" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.Guard f g c, xs) (Language.Skip, Semantic.Fault flt)"
        by(auto intro:SmallStep.step.FaultProp)
    }
    ultimately show ?thesis by(blast)
  next
    case 4
    from 4 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 4 have "stateRel Semantic.Stuck xs_og'" by(simp)
    moreover {
      from 4 sr have "xs = Semantic.Stuck" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.Guard f g c, xs) (Language.Skip, Semantic.Stuck)"
        by(auto intro:SmallStep.step.StuckProp)
    }
    ultimately show ?thesis by(blast)
  qed

next
  case Throw

  from Throw.prems[simplified] show ?case
  proof(cases rule:OG_SmallStep.step_elim_cases(10))
    case (1 flt)
    from 1 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 1 have "stateRel (Semantic.Fault flt) xs_og'" by(simp)
    moreover {
      from 1 sr have "xs = Semantic.Fault flt" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.Throw, xs) (Language.Skip, Semantic.Fault flt)"
        by(auto intro:SmallStep.step.FaultProp)
    }
    ultimately show ?thesis by(blast)
  next
    case 2
    from 2 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 2 have "stateRel Semantic.Stuck xs_og'" by(simp)
    moreover {
      from 2 sr have "xs = Semantic.Stuck" by(cases xs, auto)
      hence "SmallStep.step \<Gamma> (Language.Throw, xs) (Language.Skip, Semantic.Stuck)"
        by(auto intro:SmallStep.step.StuckProp)
    }
    ultimately show ?thesis by(blast)
  qed

next
  case (Catch c1 c2)

  from Catch.prems[simplified] show ?case
  proof(cases rule:OG_SmallStep.step_elim_cases(11))
    case (1 c1_og' s_og')
    with Catch.hyps(1) obtain c1' xs'
      where embed_IH: "c1_og' = embedSimpl c1'"
        and step_IH: "SmallStep.step \<Gamma> (c1, xs) (c1', xs')"
        and sr_IH: "stateRel xs' s_og'"
      by(blast)

    from 1 embed_IH
    have "c_og' = embedSimpl (Language.Catch c1' c2)" by(simp)

    moreover from 1 sr_IH
    have "stateRel xs' xs_og'" by(simp)

    moreover from step_IH
    have "SmallStep.step \<Gamma> (Language.Catch c1 c2, xs) (Language.Catch c1' c2, xs')"
      by(rule SmallStep.step.Catch)

    ultimately show ?thesis by(blast)
  next
    case 2
    from 2 have "c_og' = embedSimpl Language.Skip" by(simp)
    moreover from 2 sr have "stateRel xs xs_og'" by(simp)
    moreover {
      from 2 have "c1 = Language.Skip" by(cases c1, auto)
      hence "SmallStep.step \<Gamma> (Language.Catch c1 c2, xs) (Language.Skip, xs)"
        by(auto intro:SmallStep.step.CatchSkip)
    }
    ultimately show ?thesis by(blast)
  next
    case (3 s)
    from 3 have "c_og' = embedSimpl c2" by(simp)
    moreover from 3 sr have "stateRel xs xs_og'" by(simp)
    moreover {
      from 3 have "c1 = Language.Throw" by(cases c1, auto)
      moreover from 3 sr have "xs = Semantic.Normal s" by(cases xs, auto)
      ultimately have "SmallStep.step \<Gamma> (Language.Catch c1 c2, xs) (c2, xs)"
        by(auto intro:SmallStep.step.CatchThrow)
    }
    ultimately show ?thesis by(blast)
  next
    case (4 f)
    with redex_Catch_ne show ?thesis by(blast)
  next
    case 5
    with redex_Catch_ne show ?thesis by(blast)
  qed
qed

text \<open>Elimination rule form of forward refinement.\<close>
lemma embedSimpl_fwdE[consumes 2]:
  assumes sr: "stateRel xs xs_og"
      and embed_step: "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl c, xs_og) (c_og', xs_og')"
  obtains (Simpl) c' xs'
    where "c_og' = embedSimpl c'"
      and "SmallStep.step \<Gamma> (c, xs) (c', xs')"
      and "stateRel xs' xs_og'"
  using embedSimpl_fwd_refine[OF assms] by(auto)

end