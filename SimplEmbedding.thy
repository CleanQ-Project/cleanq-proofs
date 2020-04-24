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

lemma embedSimpl_inj:
  "inj embedSimpl"
proof(rule injI)
  fix c1 c2::"('s,'p,'f) Language.com"
  assume "embedSimpl c1 = embedSimpl c2"
  thus "c1 = c2"
  proof(induct c1 arbitrary:c2)
    case Skip
    then show ?case by(cases c2, auto)
  next
    case (Basic f)
    then show ?case by(cases c2, auto)
  next
    case (Spec r)
    then show ?case by(cases c2, auto)
  next
    case (Seq c11 c12)
    then show ?case by(cases c2, auto)
  next
    case (Cond b c11 c12)
    then show ?case by(cases c2, auto)
  next
    case (While b c)
    then show ?case by(cases c2, auto)
  next
    case (Call p)
    then show ?case by(cases c2, auto)
  next
    case (DynCom c)
    note outer = this
    then show ?case
    proof(cases c2)
      case Skip
      with DynCom show ?thesis by(auto)
    next
      case (Basic x2)
      with DynCom show ?thesis by(auto)
    next
      case (Spec x3)
      with DynCom show ?thesis by(auto)
    next
      case (Seq x41 x42)
      with DynCom show ?thesis by(auto)
    next
      case (Cond x51 x52 x53)
      with DynCom show ?thesis by(auto)
    next
      case (While x61 x62)
      with DynCom show ?thesis by(auto)
    next
      case (Call x7)
      with DynCom show ?thesis by(auto)
    next
      case (DynCom c')
      text \<open>This is the only non-trivial case.  The induction hypothesis + extensionality give us
            equality on the computations: c = c'.\<close>
      {
        fix s

        have "embedSimpl (c s) = (embedSimpl o c) s" by(simp)
        also {
          from DynCom outer have "OG_Language.DynCom (embedSimpl o c) = OG_Language.DynCom (embedSimpl o c')"
            by(simp)
          hence "(embedSimpl o c) s = (embedSimpl o c') s"
            by(auto)
        }
        also have "(embedSimpl o c') s = embedSimpl (c' s)" by(simp)
        finally have "c s = c' s"
          using outer by(auto)
      }
      hence "c = c'" by(rule ext)
      with DynCom outer show ?thesis by(simp)
    next
      case (Guard x91 x92 x93)
      with DynCom show ?thesis by(auto)
    next
      case Throw
      with DynCom show ?thesis by(auto)
    next
      case (Catch x111 x112)
      with DynCom show ?thesis by(auto)
    qed
  next
    case (Guard x1 x2a c1)
    then show ?case by(cases c2, auto)
  next
    case Throw
    then show ?case by(cases c2, auto)
  next
    case (Catch c11 c12)
    then show ?case by(cases c2, auto)
  qed
qed

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

lemma stateRel_sv_fwd:
  "single_valuedp stateRel"
proof(rule single_valuedpI)
  fix x y z
  assume rxy: "stateRel x y" and rxz: "stateRel x z"
  show "y = z"
  proof(cases x)
    case (Normal s)
    from Normal rxy have "y = OG_SmallStep.Normal s" by(cases y, auto)
    moreover from Normal rxz have "z = OG_SmallStep.Normal s" by(cases z, auto)
    ultimately show ?thesis by(simp)
  next
    case (Abrupt f)
    with rxy show ?thesis by(auto)
  next
    case (Fault f)
    from Fault rxy have "y = OG_SmallStep.Fault f" by(cases y, auto)
    moreover from Fault rxz have "z = OG_SmallStep.Fault f" by(cases z, auto)
    ultimately show ?thesis by(simp)
  next
    case Stuck
    from Stuck rxy have "y = OG_SmallStep.Stuck" by(cases y, auto)
    moreover from Stuck rxz have "z = OG_SmallStep.Stuck" by(cases z, auto)
    ultimately show ?thesis by(simp)
  qed
qed

lemma stateRel_sv_rev:
  "single_valuedp (conversep stateRel)"
proof(rule single_valuedpI)
  fix x y z
  assume rxy: "(conversep stateRel) x y" and rxz: "(conversep stateRel) x z"
  show "y = z"
  proof(cases x)
    case (Normal s)
    from Normal rxy have "y = Semantic.Normal s" by(cases y, auto)
    moreover from Normal rxz have "z = Semantic.Normal s" by(cases z, auto)
    ultimately show ?thesis by(simp)
  next
    case (Fault f)
    from Fault rxy have "y = Semantic.Fault f" by(cases y, auto)
    moreover from Fault rxz have "z = Semantic.Fault f" by(cases z, auto)
    ultimately show ?thesis by(simp)
  next
    case Stuck
    from Stuck rxy have "y = Semantic.Stuck" by(cases y, auto)
    moreover from Stuck rxz have "z = Semantic.Stuck" by(cases z, auto)
    ultimately show ?thesis by(simp)
  qed
qed

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

primrec com_size :: "('s,'p,'f) Language.com \<Rightarrow> nat"
  where "com_size Language.Skip = 1" |
        "com_size (Language.Basic f) = 1" |
        "com_size (Language.Spec r) = 1" |
        "com_size (Language.Seq c1 c2) = com_size c1 + com_size c2 + 1" |
        "com_size (Language.Cond b c1 c2) = com_size c1 + com_size c2 + 1" |
        "com_size (Language.While b c) = com_size c + 1" |
        "com_size (Language.Call p) = 1" |
        "com_size (Language.DynCom d) = 1" |
        "com_size (Language.Guard f g c) = com_size c + 1" |
        "com_size Language.Throw = 1" |
        "com_size (Language.Catch c1 c2) = com_size c1 + com_size c2 + 1"

lemma redex_size_le:
  "com_size (SmallStep.redex c) \<le> com_size c"
  by(induct c, auto)

lemma redex_Seq_ne:
  fixes c1 c2
  shows "SmallStep.redex (Language.Seq c1 c2) \<noteq> Language.Seq c1 c2"
proof
  assume "SmallStep.redex (Language.Seq c1 c2) = Language.Seq c1 c2"
  hence "com_size (Language.Seq c1 c2) = com_size (SmallStep.redex c1)"
    by(simp)
  also from redex_size_le have "... \<le> com_size c1"
    by(auto)
  also have "... < com_size (Language.Seq c1 c2)"
    by(simp)
  finally show False
    by(simp)
qed

lemma redex_Catch_ne:
  fixes c1 c2
  shows "SmallStep.redex (Language.Catch c1 c2) \<noteq> Language.Catch c1 c2"
proof
  assume "SmallStep.redex (Language.Catch c1 c2) = Language.Catch c1 c2"
  hence "com_size (Language.Catch c1 c2) = com_size (SmallStep.redex c1)"
    by(simp)
  also from redex_size_le have "... \<le> com_size c1"
    by(auto)
  also have "... < com_size (Language.Catch c1 c2)"
    by(simp)
  finally show False
    by(simp)
qed

primrec og_com_size :: "('s,'p,'f) OG_Language.com \<Rightarrow> nat"
  where "og_com_size OG_Language.Skip = 1" |
        "og_com_size (OG_Language.Basic f) = 1" |
        "og_com_size (OG_Language.Spec r) = 1" |
        "og_com_size (OG_Language.Seq c1 c2) = og_com_size c1 + og_com_size c2 + 1" |
        "og_com_size (OG_Language.Cond b c1 c2) = og_com_size c1 + og_com_size c2 + 1" |
        "og_com_size (OG_Language.While b c) = og_com_size c + 1" |
        "og_com_size (OG_Language.Call p) = 1" |
        "og_com_size (OG_Language.DynCom d) = 1" |
        "og_com_size (OG_Language.Guard f g c) = og_com_size c + 1" |
        "og_com_size OG_Language.Throw = 1" |
        "og_com_size (OG_Language.Catch c1 c2) = og_com_size c1 + og_com_size c2 + 1" |
        "og_com_size (OG_Language.Parallel s) = (sum_list (map og_com_size s)) + 1" |
        "og_com_size (OG_Language.Await g c) = og_com_size c + 1"

lemma og_redex_size_le:
  "og_com_size (OG_SmallStep.redex c) \<le> og_com_size c"
  by(induct c, auto)

lemma og_redex_Seq_ne:
  fixes c1 c2
  shows "OG_SmallStep.redex (OG_Language.Seq c1 c2) \<noteq> OG_Language.Seq c1 c2"
proof
  assume "OG_SmallStep.redex (OG_Language.Seq c1 c2) = OG_Language.Seq c1 c2"
  hence "og_com_size (OG_Language.Seq c1 c2) = og_com_size (OG_SmallStep.redex c1)"
    by(simp)
  also from og_redex_size_le have "... \<le> og_com_size c1"
    by(auto)
  also have "... < og_com_size (OG_Language.Seq c1 c2)"
    by(simp)
  finally show False
    by(simp)
qed

lemma og_redex_Catch_ne:
  fixes c1 c2
  shows "OG_SmallStep.redex (OG_Language.Catch c1 c2) \<noteq> OG_Language.Catch c1 c2"
proof
  assume "OG_SmallStep.redex (OG_Language.Catch c1 c2) = OG_Language.Catch c1 c2"
  hence "og_com_size (OG_Language.Catch c1 c2) = og_com_size (OG_SmallStep.redex c1)"
    by(simp)
  also from og_redex_size_le have "... \<le> og_com_size c1"
    by(auto)
  also have "... < og_com_size (OG_Language.Catch c1 c2)"
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
  thus ?case
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
    with og_redex_Seq_ne show ?thesis by(blast)
  next
    case 5
    with og_redex_Seq_ne show ?thesis by(blast)
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
    with og_redex_Catch_ne show ?thesis by(blast)
  next
    case 5
    with og_redex_Catch_ne show ?thesis by(blast)
  qed
qed

text \<open>The forward embedding is single-valued.\<close>
lemma embedSimpl_fwd_refine1:
  assumes sr: "stateRel xs xs_og"
      and embed_step: "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl c, xs_og) (c_og', xs_og')"
    shows "\<exists>!(c',xs'). c_og' = embedSimpl c' \<and> SmallStep.step \<Gamma> (c, xs) (c', xs') \<and> stateRel xs' xs_og'"
      (is "\<exists>!(c',xs'). ?P c' \<and> ?Q c' xs' \<and> ?R xs'")
proof -
  from embedSimpl_fwd_refine[OF assms] have "\<exists>c' xs'. ?P c' \<and> ?Q c' xs' \<and> ?R xs'"
    by(blast)
  moreover {
    fix c' xs' c'' xs''
    assume P1: "?P c' \<and> ?Q c' xs' \<and> ?R xs'"
       and P2: "?P c'' \<and> ?Q c'' xs'' \<and> ?R xs''"

    from embedSimpl_inj P1 P2 have "c' = c''" by(blast dest:inj_eq)
    moreover from stateRel_sv_rev P1 P2 have "xs' = xs''"
      unfolding single_valuedp_def by(auto)
    ultimately have "(c',xs') = (c'',xs'')" by(simp)
  }
  ultimately show ?thesis by(auto)
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

text \<open>Embedding is faithful - any step of the Simpl program is also a step of the Complx.\<close>
lemma embedSimpl_rev_refine:
  assumes sr: "stateRel xs xs_og"
      and step: "SmallStep.step \<Gamma> (c, xs) (c', xs')"
    shows "\<exists>xs_og'. OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl c, xs_og) (embedSimpl c', xs_og') \<and> stateRel xs' xs_og'"
  using step
proof(induct c arbitrary:c')
  case Skip
  thus ?case
    by(auto intro:SmallStep.no_step_final[unfolded SmallStep.final_def])
next
  case (Basic f)

  from Basic show ?case
  proof(cases rule:SmallStep.step_elim_cases(3))
    case (1 s)
    hence "stateRel xs' (OG_SmallStep.Normal (f s))" by(simp)
    moreover {
      from 1 sr have "xs_og = OG_SmallStep.Normal s" by(cases xs_og, auto)
      with 1 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Basic f), xs_og)
                    (embedSimpl c', OG_SmallStep.Normal (f s))"
        by(auto intro:OG_SmallStep.step.Basic)
    }
    ultimately show ?thesis by(blast)
  next
    case (2 flt)
    hence "stateRel xs' (OG_SmallStep.Fault flt)" by(simp)
    moreover {
      from 2 sr have "xs_og = OG_SmallStep.Fault flt" by(cases xs_og, auto)
      with 2 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Basic f), xs_og)
                    (embedSimpl c', OG_SmallStep.Fault flt)"
        by(auto intro:OG_SmallStep.step.FaultProp)
    }
    ultimately show ?thesis by(blast)
  next
    case 3
    hence "stateRel xs' OG_SmallStep.Stuck" by(simp)
    moreover {
      from 3 sr have "xs_og = OG_SmallStep.Stuck" by(cases xs_og, auto)
      with 3 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Basic f), xs_og)
                    (embedSimpl c', OG_SmallStep.Stuck)"
        by(auto intro:OG_SmallStep.step.StuckProp)
    }
    ultimately show ?thesis by(blast)
  next
    text \<open>The Abrupt state is forbidden by the state relation.\<close>
    case (4 f)
    with sr show ?thesis by(simp)
  qed

next
  case (Spec r)

  from Spec show ?case
  proof(cases rule:SmallStep.step_elim_cases(4))
    case (1 s t)
    hence "stateRel xs' (OG_SmallStep.Normal t)" by(simp)
    moreover {                    
      from 1 sr have "xs_og = OG_SmallStep.Normal s" by(cases xs_og, auto)
      with 1 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Spec r), xs_og)
                    (embedSimpl c', OG_SmallStep.Normal t)"
        by(auto intro:OG_SmallStep.step.Spec)
    }
    ultimately show ?thesis by(blast)
next
    case (2 s)
    hence "stateRel xs' (OG_SmallStep.Stuck)" by(simp)
    moreover {
      from 2 sr have "xs_og = OG_SmallStep.Normal s" by(cases xs_og, auto)
      with 2 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Spec r), xs_og)
                    (embedSimpl c', OG_SmallStep.Stuck)"
        by(auto intro:OG_SmallStep.step.SpecStuck)
    }
    ultimately show ?thesis by(blast)
  next
    case (3 flt)
    hence "stateRel xs' (OG_SmallStep.Fault flt)" by(simp)
    moreover {
      from 3 sr have "xs_og = OG_SmallStep.Fault flt" by(cases xs_og, auto)
      with 3 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Spec r), xs_og)
                    (embedSimpl c', OG_SmallStep.Fault flt)"
        by(auto intro:OG_SmallStep.step.FaultProp)
    }
    ultimately show ?thesis by(blast)
  next
    case 4
    hence "stateRel xs' OG_SmallStep.Stuck" by(simp)
    moreover {
      from 4 sr have "xs_og = OG_SmallStep.Stuck" by(cases xs_og, auto)
      with 4 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Spec r), xs_og)
                    (embedSimpl c', OG_SmallStep.Stuck)"
        by(auto intro:OG_SmallStep.step.StuckProp)
    }
    ultimately show ?thesis by(blast)
  next
    case (5 f)
    with sr show ?thesis by(simp)
  qed

next
  case (Seq c1 c2)

  from Seq.prems show ?case
  proof(cases rule:SmallStep.step_elim_cases(5))
    case (1 c1' s')
    with Seq.hyps(1) obtain xs_og'
        where step_IH: "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl c1, xs_og) (embedSimpl c1', xs_og')"
        and sr_IH: "stateRel xs' xs_og'"
      by(blast)

    from 1 step_IH
    have "OG_SmallStep.step (embedContext \<Gamma>)
          (embedSimpl (Language.Seq c1 c2), xs_og) (embedSimpl c', xs_og')"
      by(auto intro: OG_SmallStep.step.Seq)
    with sr_IH show ?thesis by(blast)
  next
    case 2
    from 2 sr have "stateRel xs' xs_og" by(simp)
    moreover {
      from 2 have "OG_SmallStep.step (embedContext \<Gamma>)
                    (embedSimpl (Language.Seq c1 c2), xs_og)
                    (embedSimpl c', xs_og)"
        by(auto intro:OG_SmallStep.step.SeqSkip)
    }
    ultimately show ?thesis by(blast)
  next
    case (3 s)
    from 3 sr have "stateRel xs' (OG_SmallStep.Normal s)" by(simp)
    moreover {
      from 3 sr have "xs_og = OG_SmallStep.Normal s" by(cases xs_og, auto)
      with 3 have "OG_SmallStep.step (embedContext \<Gamma>)
                    (embedSimpl (Language.Seq c1 c2), xs_og)
                    (embedSimpl c', OG_SmallStep.Normal s)"
        by(auto intro:OG_SmallStep.step.SeqThrow)
    }
    ultimately show ?thesis by(blast)
  next
    case (4 flt)
    with redex_Seq_ne show ?thesis by(blast)
  next
    case 5
    with redex_Seq_ne show ?thesis by(blast)
  next
    case (6 f)
    with sr show ?thesis by(simp)
  qed

next
  case (Cond b c1 c2)

  from Cond.prems show ?case
  proof(cases rule:SmallStep.step_elim_cases(6))
    case (1 s)
    hence "stateRel xs' (OG_SmallStep.Normal s)" by(simp)
    moreover {
      from 1 sr have "xs_og = OG_SmallStep.Normal s" by(cases xs_og, auto)
      with 1 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Cond b c1 c2), xs_og)
                    (embedSimpl c', OG_SmallStep.Normal s)"
        by(auto intro:OG_SmallStep.step.CondTrue)
    }
    ultimately show ?thesis by(blast)
  next
    case (2 s)
    hence "stateRel xs' (OG_SmallStep.Normal s)" by(simp)
    moreover {
      from 2 sr have "xs_og = OG_SmallStep.Normal s" by(cases xs_og, auto)
      with 2 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Cond b c1 c2), xs_og)
                    (embedSimpl c', OG_SmallStep.Normal s)"
        by(auto intro:OG_SmallStep.step.CondFalse)
    }
    ultimately show ?thesis by(blast)
  next
    case (3 flt)
    hence "stateRel xs' (OG_SmallStep.Fault flt)" by(simp)
    moreover {
      from 3 sr have "xs_og = OG_SmallStep.Fault flt" by(cases xs_og, auto)
      with 3 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Cond b c1 c2), xs_og)
                    (embedSimpl c', OG_SmallStep.Fault flt)"
        by(auto intro:OG_SmallStep.step.FaultProp)
    }
    ultimately show ?thesis by(blast)
  next
    case 4
    hence "stateRel xs' OG_SmallStep.Stuck" by(simp)
    moreover {
      from 4 sr have "xs_og = OG_SmallStep.Stuck" by(cases xs_og, auto)
      with 4 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Cond b c1 c2), xs_og)
                    (embedSimpl c', OG_SmallStep.Stuck)"
        by(auto intro:OG_SmallStep.step.StuckProp)
    }
    ultimately show ?thesis by(blast)
  next
    case (5 f)
    with sr show ?thesis by(simp)
  qed

next
  case (While b c)

  from While.prems show ?case
  proof(cases rule:SmallStep.step_elim_cases(7))
    case (1 s)
    hence "stateRel xs' (OG_SmallStep.Normal s)" by(simp)
    moreover {
      from 1 sr have "xs_og = OG_SmallStep.Normal s" by(cases xs_og, auto)
      with 1 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.While b c), xs_og)
                    (embedSimpl c', OG_SmallStep.Normal s)"
        by(auto intro:OG_SmallStep.step.WhileTrue)
    }
    ultimately show ?thesis by(blast)
  next
    case (2 s)
    hence "stateRel xs' (OG_SmallStep.Normal s)" by(simp)
    moreover {
      from 2 sr have "xs_og = OG_SmallStep.Normal s" by(cases xs_og, auto)
      with 2 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.While b c), xs_og)
                    (embedSimpl c', OG_SmallStep.Normal s)"
        by(auto intro:OG_SmallStep.step.WhileFalse)
    }
    ultimately show ?thesis by(blast)
  next
    case (3 flt)
    hence "stateRel xs' (OG_SmallStep.Fault flt)" by(simp)
    moreover {
      from 3 sr have "xs_og = OG_SmallStep.Fault flt" by(cases xs_og, auto)
      with 3 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.While b c), xs_og)
                    (embedSimpl c', OG_SmallStep.Fault flt)"
        by(auto intro:OG_SmallStep.step.FaultProp)
    }
    ultimately show ?thesis by(blast)
  next
    case 4
    hence "stateRel xs' OG_SmallStep.Stuck" by(simp)
    moreover {
      from 4 sr have "xs_og = OG_SmallStep.Stuck" by(cases xs_og, auto)
      with 4 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.While b c), xs_og)
                    (embedSimpl c', OG_SmallStep.Stuck)"
        by(auto intro:OG_SmallStep.step.StuckProp)
    }
    ultimately show ?thesis by(blast)
  next
    case (5 f)
    with sr show ?thesis by(simp)
  qed

next
  case (Call p)

  from Call.prems show ?case
  proof(cases rule:SmallStep.step_elim_cases(8))
    case (1 bdy s)
    hence lookup: "(embedContext \<Gamma>) p = Some (embedSimpl bdy)"
      unfolding embedContext_def by(simp)
    from 1 have "stateRel xs' (OG_SmallStep.Normal s)" by(simp)
    moreover {
      from 1 sr have "xs_og = OG_SmallStep.Normal s" by(cases xs_og, auto)
      with 1 lookup
      have "OG_SmallStep.step (embedContext \<Gamma>)
              (embedSimpl (Language.Call p), xs_og)
              (embedSimpl c', OG_SmallStep.Normal s)"
        by(auto intro:OG_SmallStep.step.Call)
    }
    ultimately show ?thesis by(blast)
  next
    case (2 s)
    hence lookup: "(embedContext \<Gamma>) p = None"
      unfolding embedContext_def by(simp)
    from 2 have "stateRel xs' OG_SmallStep.Stuck" by(simp)
    moreover {
      from 2 sr have "xs_og = OG_SmallStep.Normal s" by(cases xs_og, auto)
      with 2 lookup
      have "OG_SmallStep.step (embedContext \<Gamma>)
              (embedSimpl (Language.Call p), xs_og)
              (embedSimpl c', OG_SmallStep.Stuck)"
        by(auto intro:OG_SmallStep.step.CallUndefined)
    }
    ultimately show ?thesis by(blast)
  next
    case (3 flt)
    hence "stateRel xs' (OG_SmallStep.Fault flt)" by(simp)
    moreover {
      from 3 sr have "xs_og = OG_SmallStep.Fault flt" by(cases xs_og, auto)
      with 3 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Call p), xs_og)
                    (embedSimpl c', OG_SmallStep.Fault flt)"
        by(auto intro:OG_SmallStep.step.FaultProp)
    }
    ultimately show ?thesis by(blast)
  next
    case 4
    hence "stateRel xs' OG_SmallStep.Stuck" by(simp)
    moreover {
      from 4 sr have "xs_og = OG_SmallStep.Stuck" by(cases xs_og, auto)
      with 4 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Call p), xs_og)
                    (embedSimpl c', OG_SmallStep.Stuck)"
        by(auto intro:OG_SmallStep.step.StuckProp)
    }
    ultimately show ?thesis by(blast)
  next
    case (5 f)
    with sr show ?thesis by(simp)
  qed

next
  case (DynCom c)

  from DynCom.prems show ?case
  proof(cases rule:SmallStep.step_elim_cases(9))
    case (1 s)
    hence "stateRel xs' (OG_SmallStep.Normal s)" by(simp)
    moreover {
      from 1 sr have "xs_og = OG_SmallStep.Normal s" by(cases xs_og, auto)
      with 1 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.DynCom c), xs_og)
                    (embedSimpl c', OG_SmallStep.Normal s)"
        by(auto intro:OG_SmallStep.step.DynCom simp:o_def)
      }
    ultimately show ?thesis by(blast)
  next
    case (2 flt)
    hence "stateRel xs' (OG_SmallStep.Fault flt)" by(simp)
    moreover {
      from 2 sr have "xs_og = OG_SmallStep.Fault flt" by(cases xs_og, auto)
      with 2 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.DynCom c), xs_og)
                    (embedSimpl c', OG_SmallStep.Fault flt)"
        by(auto intro:OG_SmallStep.step.FaultProp)
    }
    ultimately show ?thesis by(blast)
  next
    case 3
    hence "stateRel xs' OG_SmallStep.Stuck" by(simp)
    moreover {
      from 3 sr have "xs_og = OG_SmallStep.Stuck" by(cases xs_og, auto)
      with 3 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.DynCom c), xs_og)
                    (embedSimpl c', OG_SmallStep.Stuck)"
        by(auto intro:OG_SmallStep.step.StuckProp)
    }
    ultimately show ?thesis by(blast)
  next
    case (4 f)
    with sr show ?thesis by(simp)
  qed

next
  case (Guard f g c)

  from Guard.prems show ?case
  proof(cases rule:SmallStep.step_elim_cases(2))
    case (1 s)
    hence "stateRel xs' (OG_SmallStep.Normal s)" by(simp)
    moreover {
      from 1 sr have "xs_og = OG_SmallStep.Normal s" by(cases xs_og, auto)
      with 1 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Guard f g c), xs_og)
                    (embedSimpl c', OG_SmallStep.Normal s)"
        by(auto intro:OG_SmallStep.step.Guard)
    }
    ultimately show ?thesis by(blast)
  next
    case (2 s)
    hence "stateRel xs' (OG_SmallStep.Fault f)" by(simp)
    moreover {
      from 2 sr have "xs_og = OG_SmallStep.Normal s" by(cases xs_og, auto)
      with 2 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Guard f g c), xs_og)
                    (embedSimpl c', OG_SmallStep.Fault f)"
        by(auto intro:OG_SmallStep.step.GuardFault)
    }
    ultimately show ?thesis by(blast)
  next
    case (3 flt)
    hence "stateRel xs' (OG_SmallStep.Fault flt)" by(simp)
    moreover {
      from 3 sr have "xs_og = OG_SmallStep.Fault flt" by(cases xs_og, auto)
      with 3 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Guard f g c), xs_og)
                    (embedSimpl c', OG_SmallStep.Fault flt)"
        by(auto intro:OG_SmallStep.step.FaultProp)
    }
    ultimately show ?thesis by(blast)
  next
    case 4
    hence "stateRel xs' OG_SmallStep.Stuck" by(simp)
    moreover {
      from 4 sr have "xs_og = OG_SmallStep.Stuck" by(cases xs_og, auto)
      with 4 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Guard f g c), xs_og)
                    (embedSimpl c', OG_SmallStep.Stuck)"
        by(auto intro:OG_SmallStep.step.StuckProp)
    }
    ultimately show ?thesis by(blast)
  next
    case (5 f)
    with sr show ?thesis by(simp)
  qed

next
  case Throw

  from Throw.prems show ?case
  proof(cases rule:SmallStep.step_elim_cases(10))
    case (1 f)
    hence "stateRel xs' (OG_SmallStep.Fault f)" by(simp)
    moreover {
      from 1 sr have "xs_og = OG_SmallStep.Fault f" by(cases xs_og, auto)
      with 1 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl Language.Throw, xs_og)
                    (embedSimpl c', OG_SmallStep.Fault f)"
        by(auto intro:OG_SmallStep.step.FaultProp)
    }
    ultimately show ?thesis by(blast)
  next
    case 2
    hence "stateRel xs' OG_SmallStep.Stuck" by(simp)
    moreover {
      from 2 sr have "xs_og = OG_SmallStep.Stuck" by(cases xs_og, auto)
      with 2 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl Language.Throw, xs_og)
                    (embedSimpl c', OG_SmallStep.Stuck)"
        by(auto intro:OG_SmallStep.step.StuckProp)
    }
    ultimately show ?thesis by(blast)
  next
    case (3 f)
    with sr show ?thesis by(simp)
  qed

next
  case (Catch c1 c2)

  from Catch.prems show ?case
  proof(cases rule:SmallStep.step_elim_cases(11))
    case (1 c1' s')
    with Catch.hyps(1) obtain xs_og'
        where step_IH: "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl c1, xs_og) (embedSimpl c1', xs_og')"
        and sr_IH: "stateRel xs' xs_og'"
      by(blast)

    from 1 step_IH
    have "OG_SmallStep.step (embedContext \<Gamma>)
          (embedSimpl (Language.Catch c1 c2), xs_og) (embedSimpl c', xs_og')"
      by(auto intro: OG_SmallStep.step.Catch)
    with sr_IH show ?thesis by(blast)
  next
    case (2 s)
    with sr have "stateRel xs' xs_og" by(simp)
    moreover {
      from 2 sr have "xs_og = OG_SmallStep.Normal s" by(cases xs_og, auto)
      with 2 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Catch c1 c2), xs_og)
                    (embedSimpl c', xs_og)"
        by(auto intro:OG_SmallStep.step.CatchThrow)
    }
    ultimately show ?thesis by(blast)
next
    case 3
    with sr have "stateRel xs' xs_og" by(simp)
    moreover
    from 3 have "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl (Language.Catch c1 c2), xs_og)
                  (embedSimpl c', xs_og)"
     by(auto intro:OG_SmallStep.step.CatchSkip)
    ultimately show ?thesis by(blast)
  next
    case (4 f)
    with redex_Catch_ne show ?thesis by(blast)
  next
    case 5
    with redex_Catch_ne show ?thesis by(blast)
  next
    case (6 f)
    with sr show ?thesis by(simp)
  qed
qed

text \<open>The reverse refinement is also unique.  It's functional in both directions.\<close>
lemma embedSimpl_rev_refine1:
  assumes sr: "stateRel xs xs_og"
      and step: "SmallStep.step \<Gamma> (c, xs) (c', xs')"
    shows "\<exists>!xs_og'. OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl c, xs_og) (embedSimpl c', xs_og') \<and> stateRel xs' xs_og'"
      (is "\<exists>!xs_og'. ?P xs_og'")
proof -
  from embedSimpl_rev_refine[OF assms] have "\<exists>xs_og'. ?P xs_og'"
    by(blast)
  moreover {
    fix xs_og' xs_og''
    assume "?P xs_og'" and "?P xs_og''"
    with stateRel_sv_fwd have "xs_og' = xs_og''"
      unfolding single_valuedp_def by(auto)
  }
  ultimately show ?thesis by(auto)
qed

text \<open>Elimination rule form of reverse refinement.\<close>
lemma embedSimpl_revE[consumes 2]:
  assumes sr: "stateRel xs xs_og"
      and step: "SmallStep.step \<Gamma> (c, xs) (c', xs')"
  obtains (Complx) xs_og'
    where "OG_SmallStep.step (embedContext \<Gamma>) (embedSimpl c, xs_og) (embedSimpl c', xs_og')"
      and "stateRel xs' xs_og'"
  using embedSimpl_rev_refine[OF assms] by(auto)

end