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



theory Refinements
  imports SimplEmbedding
begin

text \<open>A `program', or the subject of the refinement relation is a computation plus its function-call
  closure and a precondition.\<close>
type_synonym ('s,'p,'f) program_s =
  "(('s,'p,'f) Semantic.body \<times> ('s,'f) Semantic.xstate set \<times> ('s,'p,'f) Language.com)"

text \<open>The state relation is a lifting function from concrete to abstract.\<close>
type_synonym ('sa,'fa,'sc,'fc) xstate_lift_s =
  "('sc,'fc) Semantic.xstate \<Rightarrow> ('sa,'fa) Semantic.xstate"

text \<open>Refinement is a relation on programs.\<close>
type_synonym ('sa,'pa,'fa,'sc,'pc,'fc) refinement_s =
  "(('sa,'pa,'fa) program_s \<times> ('sc,'pc,'fc) program_s) set"

text \<open>General data refinement of abstract computation ca with context \<Gamma>a by concrete computation
  cc with context \<Gamma>c.  For any concrete state xsc satisfying the concrete precondition,
  if the concrete computation takes a step to a state xsc', then the abstract computation must be
  able to step from the lifted xsc to the lifted xsc', such that the remaining abstract computation
  is still refined by the remaining concrete computation.  This inductive refinment need only hold
  for this specific new state.

  The abstract precondition must be weak enough to encompass all valid concrete starting states, and
  is thus satisfied by construction.  This condition is necessary for refinement to compose.

  Moreover, the refinement may only terminate if the specification also terminates, and throws a
  fault exactly when the specification does.\<close>
inductive_set refinement_s ::
  "('sa,'fa,'sc,'fc) xstate_lift_s \<Rightarrow> ('sa,'pa,'fa,'sc,'pc,'fc) refinement_s"
  for xsl :: "('sa,'fa,'sc,'fc) xstate_lift_s"
  where Step:
    "(\<And>xsc xsc' cc'.
      xsc \<in> Pc \<Longrightarrow>
      SmallStep.step \<Gamma>c (cc,xsc) (cc',xsc') \<Longrightarrow>
      (\<exists>ca'. SmallStep.step \<Gamma>a (ca,xsl xsc) (ca',xsl xsc') \<and>
             ((\<Gamma>a,{xsl xsc'},ca'),(\<Gamma>c,{xsc'},cc')) \<in> refinement_s xsl)) \<Longrightarrow>
      xsl ` Pc \<subseteq> Pa \<Longrightarrow>
      (cc = Language.Skip \<Longrightarrow> ca = Language.Skip) \<Longrightarrow>
      (cc = Language.Throw \<longleftrightarrow> ca = Language.Throw) \<Longrightarrow>
      ((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc)) \<in> refinement_s xsl"

text \<open>An elimination rule form of the above lemma, making it easy to access an equivalent abstract
  transition in proofs.\<close>
lemma refinement_s_stepE:
    fixes Pa Pc xsl \<Gamma>a \<Gamma>c xsc xsc' ca cc cc'
    assumes refines: "((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc)) \<in> refinement_s xsl"
      and Pc: "xsc \<in> Pc"
      and concrete_step: "SmallStep.step \<Gamma>c (cc,xsc) (cc',xsc')"
  obtains (abstract_step) ca'
    where "SmallStep.step \<Gamma>a (ca,xsl xsc) (ca',xsl xsc')"
      and "((\<Gamma>a,{xsl xsc'},ca'),(\<Gamma>c,{xsc'},cc')) \<in> refinement_s xsl"
  using refines
proof(cases rule:refinement_s.cases)
  case Step
  with Pc concrete_step obtain ca'
    where stepa: "SmallStep.step \<Gamma>a (ca, xsl xsc) (ca', xsl xsc')"
      and refines': "((\<Gamma>a,{xsl xsc'},ca'),(\<Gamma>c,{xsc'},cc')) \<in> refinement_s xsl"
    by(blast)

  from stepa refines' show ?thesis
    by(rule abstract_step)
qed

text \<open>The concrete precondition is stricter than the abstract.\<close>
lemma refinement_s_stricter_pre:
  fixes Pa Pc xsl \<Gamma>a \<Gamma>c ca cc
  assumes refines: "((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc)) \<in> refinement_s xsl"
  shows "xsl ` Pc \<subseteq> Pa"
  using assms by(cases, auto)

text \<open>A mode-preserving lifting function only relates Normal-Normal etc.\<close>
definition
  mode_preserving :: "('sa,'fa,'sc,'fc) xstate_lift_s \<Rightarrow> bool"
where
  "mode_preserving xsl \<longleftrightarrow> (\<forall>xsc.
    (((\<exists>sa. xsl xsc = Semantic.Normal sa) \<longleftrightarrow> (\<exists>sc. xsc = Semantic.Normal sc)) \<and>
     ((\<exists>sa. xsl xsc = Semantic.Abrupt sa) \<longleftrightarrow> (\<exists>sc. xsc = Semantic.Abrupt sc)) \<and>
     ((\<exists>fa. xsl xsc = Semantic.Fault fa) \<longleftrightarrow> (\<exists>fc. xsc = Semantic.Fault fc)) \<and>
     (xsl xsc = Semantic.Stuck \<longleftrightarrow> xsc = Semantic.Stuck)))"

lemma mode_preserving_NormalaE:
  assumes mp: "mode_preserving xsl"
      and normala: "xsl xsc = Semantic.Normal sa"
  obtains (normalc) sc where "xsc = Semantic.Normal sc"
proof -
  from normala have "\<exists>sa. xsl xsc = Semantic.Normal sa"
    by(auto)
  with allE[OF mp[unfolded mode_preserving_def], of xsc]
  have "\<exists>sc. xsc = Semantic.Normal sc"
    by(blast)
  then obtain sc where "xsc = Semantic.Normal sc"
    by(blast)
  thus thesis
    by(rule normalc)
qed

lemma mode_preserving_NormalcE:
  assumes mp: "mode_preserving xsl"
      and normalc: "xsc = Semantic.Normal sc"
  obtains (normala) sa where "xsl xsc = Semantic.Normal sa"
proof -
  from normalc have "\<exists>sc. xsc = Semantic.Normal sc"
    by(auto)
  with allE[OF mp[unfolded mode_preserving_def], of xsc]
  have "\<exists>sa. xsl xsc = Semantic.Normal sa"
    by(blast)
  then obtain sa where "xsl xsc = Semantic.Normal sa"
    by(blast)
  thus thesis
    by(rule normala)
qed

lemma mode_preserving_AbruptaE:
  assumes mp: "mode_preserving xsl"
      and abrupta: "xsl xsc = Semantic.Abrupt sa"
  obtains (abruptc) sc where "xsc = Semantic.Abrupt sc"
proof -
  from abrupta have "\<exists>sa. xsl xsc = Semantic.Abrupt sa"
    by(auto)
  with allE[OF mp[unfolded mode_preserving_def], of xsc]
  have "\<exists>sc. xsc = Semantic.Abrupt sc"
    by(blast)
  then obtain sc where "xsc = Semantic.Abrupt sc"
    by(blast)
  thus thesis
    by(rule abruptc)
qed

lemma mode_preserving_AbruptcE:
  assumes mp: "mode_preserving xsl"
      and abruptc: "xsc = Semantic.Abrupt sc"
  obtains (abrupta) sa where "xsl xsc = Semantic.Abrupt sa"
proof -
  from abruptc have "\<exists>sc. xsc = Semantic.Abrupt sc"
    by(auto)
  with allE[OF mp[unfolded mode_preserving_def], of xsc]
  have "\<exists>sa. xsl xsc = Semantic.Abrupt sa"
    by(blast)
  then obtain sa where "xsl xsc = Semantic.Abrupt sa"
    by(blast)
  thus thesis
    by(rule abrupta)
qed

lemma mode_preserving_FaultaE:
  assumes mp: "mode_preserving xsl"
      and faulta: "xsl xsc = Semantic.Fault fa"
  obtains (faultc) sc where "xsc = Semantic.Fault sc"
proof -
  from faulta have "\<exists>sa. xsl xsc = Semantic.Fault sa"
    by(auto)
  with allE[OF mp[unfolded mode_preserving_def], of xsc]
  have "\<exists>sc. xsc = Semantic.Fault sc"
    by(blast)
  then obtain sc where "xsc = Semantic.Fault sc"
    by(blast)
  thus thesis
    by(rule faultc)
qed

lemma mode_preserving_FaultcE:
  assumes mp: "mode_preserving xsl"
      and faultc: "xsc = Semantic.Fault sc"
  obtains (faulta) sa where "xsl xsc = Semantic.Fault sa"
proof -
  from faultc have "\<exists>sc. xsc = Semantic.Fault sc"
    by(auto)
  with allE[OF mp[unfolded mode_preserving_def], of xsc]
  have "\<exists>sa. xsl xsc = Semantic.Fault sa"
    by(blast)
  then obtain sa where "xsl xsc = Semantic.Fault sa"
    by(blast)
  thus thesis
    by(rule faulta)
qed

lemma mode_preserving_StuckaE:
  assumes mp: "mode_preserving xsl"
      and stucka: "xsl xsc = Semantic.Stuck"
    shows "xsc = Semantic.Stuck"
proof -
  from stucka have "xsl xsc = Semantic.Stuck"
    by(auto)
  with allE[OF mp[unfolded mode_preserving_def], of xsc]
  show "xsc = Semantic.Stuck"
    by(blast)
qed

lemma mode_preserving_StuckcE:
  assumes mp: "mode_preserving xsl"
      and stuckc: "xsc = Semantic.Stuck"
    shows "xsl xsc = Semantic.Stuck"
proof -
  from stuckc have "xsc = Semantic.Stuck"
    by(auto)
  with allE[OF mp[unfolded mode_preserving_def], of xsc]
  show "xsl xsc = Semantic.Stuck"
    by(blast)
qed

lemma refinement_s_finalE:
    fixes Pa Pc xsl \<Gamma>a \<Gamma>c ca cc
  assumes refines: "((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc)) \<in> refinement_s xsl"
      and mp: "mode_preserving xsl"
      and finalc: "SmallStep.final (cc,xsc)"
    shows "SmallStep.final (ca,xsl xsc)"
  using assms unfolding mode_preserving_def SmallStep.final_def
  by(auto elim:refinement_s.cases)

lemma refinement_s_skipcE:
  fixes Pa Pc xsl \<Gamma>a \<Gamma>c ca cc
  assumes refines: "((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc)) \<in> refinement_s xsl"
      and throw: "cc = Language.Skip"
  shows "ca = Language.Skip"
  using assms by(auto elim:refinement_s.cases)

lemma refinement_s_throwcE:
  fixes Pa Pc xsl \<Gamma>a \<Gamma>c ca cc
  assumes refines: "((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc)) \<in> refinement_s xsl"
      and throw: "cc = Language.Throw"
  shows "ca = Language.Throw"
  using assms by(auto elim:refinement_s.cases)

lemma refinement_s_throwaE:
  fixes Pa Pc xsl \<Gamma>a \<Gamma>c ca cc
  assumes refines: "((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc)) \<in> refinement_s xsl"
      and throw: "ca = Language.Throw"
  shows "cc = Language.Throw"
  using assms by(auto elim:refinement_s.cases)

lemma refinement_s_throweq:
  fixes Pa Pc xsl \<Gamma>a \<Gamma>c ca cc
  assumes refines: "((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc)) \<in> refinement_s xsl"
  shows "(cc = Language.Throw) = (ca = Language.Throw)"
  using assms by(auto elim:refinement_s.cases)

lemma refinement_s_strengthen:
    fixes xsl \<Gamma>a \<Gamma>c Pa Pc Pa' Pc' ca cc
  assumes refines: "((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc)) \<in> refinement_s xsl"
      and strengthenc: "Pc' \<subseteq> Pc"
      and consistent: "xsl ` Pc' \<subseteq> Pa'"
    shows "((\<Gamma>a, Pa', ca), (\<Gamma>c, Pc', cc)) \<in> refinement_s xsl"
proof
    fix xsc xsc' cc'

    assume "xsc \<in> Pc'"
    with strengthenc have Pc: "xsc \<in> Pc" by(auto)

    assume step: "SmallStep.step \<Gamma>c (cc,xsc) (cc',xsc')"
    
    from refinement_s_stepE[OF refines Pc step]
    obtain ca'
      where "SmallStep.step \<Gamma>a (ca,xsl xsc) (ca',xsl xsc')"
        and "((\<Gamma>a,{xsl xsc'},ca'),(\<Gamma>c,{xsc'},cc')) \<in> refinement_s xsl"
      by(blast)
    thus "\<exists>ca'.
          SmallStep.step \<Gamma>a (ca, xsl xsc) (ca', xsl xsc') \<and>
          ((\<Gamma>a, {xsl xsc'}, ca'), \<Gamma>c, {xsc'}, cc') \<in> refinement_s xsl"
      by(blast)
  next
    from consistent show "xsl ` Pc' \<subseteq> Pa'" .
  next
    assume "cc = Language.Skip"
    with refines show "ca = Language.Skip"
      by(rule refinement_s_skipcE)
  next
    from refines show "(cc = Language.Throw) = (ca = Language.Throw)"
      by(auto elim:refinement_s_throwcE refinement_s_throwaE)
qed

text \<open>Refinement composes transitively.\<close>
lemma refinement_s_trans:
  shows "(refinement_s xsl_ab :: ('sa,'pa,'fa,'sb,'pb,'fb) refinement_s) O
         (refinement_s xsl_bc :: ('sb,'pb,'fb,'sc,'pc,'fc) refinement_s) \<subseteq>
          refinement_s (xsl_ab o xsl_bc)"
proof
  fix x :: "('sa,'pa,'fa) program_s \<times> ('sc,'pc,'fc) program_s"
  obtain \<Gamma>a \<Gamma>c Pa Pc ca cc
    where rw_x: "x = ((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc))"
    by(cases x, auto)

  assume "x \<in> (refinement_s xsl_ab :: ('sa,'pa,'fa,'sb,'pb,'fb) refinement_s) O
              (refinement_s xsl_bc :: ('sb,'pb,'fb,'sc,'pc,'fc) refinement_s)"
  hence "((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc)) \<in>
            (refinement_s xsl_ab :: ('sa,'pa,'fa,'sb,'pb,'fb) refinement_s) O
            (refinement_s xsl_bc :: ('sb,'pb,'fb,'sc,'pc,'fc) refinement_s)"
    by(simp add:rw_x)

  then obtain \<Gamma>b :: "('sb,'pb,'fb) Semantic.body"
          and Pb :: "('sb,'fb) Semantic.xstate set"
          and cb :: "('sb,'pb,'fb) Language.com"
    where refines_ab: "((\<Gamma>a,Pa,ca),(\<Gamma>b,Pb,cb)) \<in> refinement_s xsl_ab"
      and refines_bc: "((\<Gamma>b,Pb,cb),(\<Gamma>c,Pc,cc)) \<in> refinement_s xsl_bc"
    by(auto)

  from refines_ab refines_bc
  show "x \<in> refinement_s (xsl_ab o xsl_bc)"
    unfolding rw_x
  proof(induct \<Gamma>a Pa ca \<Gamma>b Pb cb arbitrary:Pc cc rule: refinement_s.induct)
    case (Step Pb \<Gamma>b cb \<Gamma>a ca Pa)

    show ?case
    proof(rule refinement_s.Step)
      fix xsc xsc' cc'

      assume Pc: "xsc \<in> Pc"
         and stepc: "SmallStep.step \<Gamma>c (cc,xsc) (cc',xsc')"

      from Pc refinement_s_stricter_pre[OF Step.prems]
      have Pb: "xsl_bc xsc \<in> Pb"
        by(auto)

      from refinement_s_stepE[OF Step.prems Pc stepc] obtain cb'
        where stepb: "SmallStep.step \<Gamma>b (cb,xsl_bc xsc) (cb',xsl_bc xsc')"
          and refines_bc': "((\<Gamma>b, {xsl_bc xsc'}, cb'), \<Gamma>c, {xsc'}, cc') \<in> refinement_s xsl_bc"
        by(blast)

      from Step.hyps(1)[OF Pb stepb] obtain ca'
        where stepa: "SmallStep.step \<Gamma>a (ca,xsl_ab (xsl_bc xsc)) (ca',xsl_ab (xsl_bc xsc'))"
          and refines_ab': "((\<Gamma>a,{xsl_ab (xsl_bc xsc')},ca'), (\<Gamma>b,{xsl_bc xsc'},cb')) \<in> refinement_s xsl_ab"
          and IH: "(\<forall>x xa.
            ((\<Gamma>b, {xsl_bc xsc'}, cb'), (\<Gamma>c, x, xa)) \<in> refinement_s xsl_bc \<longrightarrow>
            ((\<Gamma>a, {xsl_ab (xsl_bc xsc')}, ca'), (\<Gamma>c, x, xa)) \<in> refinement_s (xsl_ab \<circ> xsl_bc))"
        by(blast)

      from stepa have "SmallStep.step \<Gamma>a (ca,(xsl_ab \<circ> xsl_bc) xsc) (ca',(xsl_ab \<circ> xsl_bc) xsc')"
        by(simp)
      moreover from refines_bc' IH
      have "((\<Gamma>a,{(xsl_ab \<circ> xsl_bc) xsc'},ca'), (\<Gamma>c,{xsc'},cc')) \<in> refinement_s (xsl_ab \<circ> xsl_bc)"
        by(auto)
      ultimately show "\<exists>ca'.
        SmallStep.step \<Gamma>a (ca, (xsl_ab \<circ> xsl_bc) xsc) (ca', (xsl_ab \<circ> xsl_bc) xsc') \<and>
        ((\<Gamma>a,{(xsl_ab \<circ> xsl_bc) xsc'},ca'), (\<Gamma>c,{xsc'},cc')) \<in> refinement_s (xsl_ab \<circ> xsl_bc)"
        by(blast)

    next
      show "(xsl_ab \<circ> xsl_bc) ` Pc \<subseteq> Pa"
      proof
        fix xsa
        assume "xsa \<in> (xsl_ab \<circ> xsl_bc) ` Pc"
        moreover {
          from Step.prems have "xsl_bc ` Pc \<subseteq> Pb"
            by(rule refinement_s_stricter_pre)
          hence "(xsl_ab o xsl_bc) ` Pc \<subseteq> xsl_ab ` Pb"
            by(auto)
        }
        also note Step.hyps(2)
        finally show "xsa \<in> Pa" .
      qed

    next
      assume "cc = Language.Skip"
      with Step.prems have "cb = Language.Skip"
        by(rule refinement_s_skipcE)
      thus "ca = Language.Skip"
        by(rule Step.hyps(3))

    next
      from Step.prems have "(cc = Language.Throw) = (cb = Language.Throw)"
        by(rule refinement_s_throweq)
      also note Step.hyps(4)
      finally show "(cc = THROW) = (ca = THROW)" .
    qed
  qed
qed

lemma refinement_steps:
    fixes xsl \<Gamma>a \<Gamma>c Pa Pc xsc xsc' ca cc cc'
  assumes refines: "((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc)) \<in> refinement_s xsl"
      and Pc: "xsc \<in> Pc"
      and concrete_steps: "(rtranclp (SmallStep.step \<Gamma>c)) (cc,xsc) (cc',xsc')"
    shows "\<exists>ca'.
      ((\<Gamma>a,{xsl xsc'},ca'),(\<Gamma>c,{xsc'},cc')) \<in> refinement_s xsl \<and>
      (rtranclp (SmallStep.step \<Gamma>a)) (ca,xsl xsc) (ca',xsl xsc')"
  using concrete_steps
proof(induct cc' xsc' rule:rtranclp_induct2)
  case refl

  from refines Pc
  have "((\<Gamma>a, {xsl xsc}, ca), \<Gamma>c, {xsc}, cc) \<in> refinement_s xsl"
    by(auto intro:refinement_s_strengthen)
  moreover have "(rtranclp (SmallStep.step \<Gamma>a)) (ca,xsl xsc) (ca,xsl xsc)"
    by(blast)
  ultimately show ?case
    by(blast)

next
  case (step cc' xsc' cc'' xsc'')
  then obtain ca'
    where refines': "((\<Gamma>a,{xsl xsc'},ca'), (\<Gamma>c,{xsc'},cc')) \<in> refinement_s xsl"
      and stepsa: "(rtranclp (SmallStep.step \<Gamma>a)) (ca, xsl xsc) (ca',xsl xsc')"
    by(blast)

  from refines' step(2)
  obtain ca''
    where refines'': "((\<Gamma>a,{xsl xsc''},ca''),(\<Gamma>c,{xsc''},cc'')) \<in> refinement_s xsl"
      and stepa: "SmallStep.step \<Gamma>a (ca',xsl xsc') (ca'',xsl xsc'')"
    by(blast elim:refinement_s_stepE)

  from stepsa stepa have "(rtranclp (SmallStep.step \<Gamma>a)) (ca, xsl xsc) (ca'',xsl xsc'')"
    by(auto)
  with refines'' show ?case by(blast)
qed

lemma refinement_s_stepsE:
    fixes xsl \<Gamma>a \<Gamma>c Pa Pc xsc xsc' ca cc cc'
  assumes refines: "((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc)) \<in> refinement_s xsl"
      and Pc: "xsc \<in> Pc"
      and concrete_steps: "(rtranclp (SmallStep.step \<Gamma>c)) (cc,xsc) (cc',xsc')"
  obtains (abstract_steps) ca'
    where "((\<Gamma>a,{xsl xsc'},ca'),(\<Gamma>c,{xsc'},cc')) \<in> refinement_s xsl"
      and "(rtranclp (SmallStep.step \<Gamma>a)) (ca,xsl xsc) (ca',xsl xsc')"
  using refinement_steps[OF assms] by(blast)

type_synonym ('s,'p,'f) trace_s = "(('s,'p,'f) Language.com \<times> ('s,'f) Semantic.xstate) list"

text \<open>The finite traces of a computation are those reachable from some starting state.\<close>
inductive_set finite_traces_s ::
  "('s,'p,'f) Semantic.body \<Rightarrow> ('s,'p,'f) Language.com \<Rightarrow> ('s,'p,'f) trace_s set"
  for \<Gamma> :: "('s,'p,'f) Semantic.body"
  and c :: "('s,'p,'f) Language.com"
where
  Start: "[(c, xs)] \<in> finite_traces_s \<Gamma> c" |
  Step: "(cf,xsf) # T \<in> finite_traces_s \<Gamma> c \<Longrightarrow> SmallStep.step \<Gamma> (cf,xsf) (cf',xsf') \<Longrightarrow>
         (cf',xsf') # (cf,xsf) # T \<in> finite_traces_s \<Gamma> c"

lemma finite_trace_nonempty_s:
  "T \<in> finite_traces_s \<Gamma> c \<Longrightarrow> T \<noteq> []"
  by(induct T rule:finite_traces_s.induct, auto)

text \<open>Refinement is pointwise between traces of the same length.\<close>
inductive trace_refines_s ::
  "('sa,'fa,'sc,'fc) xstate_lift_s \<Rightarrow> ('sa,'pa,'fa) trace_s \<Rightarrow> ('sc,'pc,'fc) trace_s \<Rightarrow> bool"
  for xsl :: "('sa,'fa,'sc,'fc) xstate_lift_s"
  where
    Start: "trace_refines_s xsl [] []" |
    Step:  "trace_refines_s xsl Ta Tc \<Longrightarrow>
              trace_refines_s xsl ((ca,xsl xsc)#Ta) ((cc,xsc)#Tc)"

type_synonym ('s,'f) state_trace_s = "('s,'f) Semantic.xstate list"

text \<open>Project the state component.\<close>
definition state_trace_of :: "('s,'p,'f) trace_s \<Rightarrow> ('s,'f) state_trace_s"
  where "state_trace_of T = map snd T"

definition finite_state_traces_s ::
  "('s,'p,'f) Semantic.body \<Rightarrow> ('s,'p,'f) Language.com \<Rightarrow> ('s,'f) state_trace_s set"
  where
    "finite_state_traces_s \<Gamma> c = state_trace_of ` (finite_traces_s \<Gamma> c)"

lemma finite_state_trace_nonempty_s:
  "T \<in> finite_state_traces_s \<Gamma> c \<Longrightarrow> T \<noteq> []"
  using finite_trace_nonempty_s unfolding finite_state_traces_s_def state_trace_of_def by(auto)

text \<open>If cc refines ca, then for any trace of cc there exists a corresponding abstract trace of
  which the concrete trace is a refinement, in the sense defined above i.e. program refinement
  implies trace refinement.\<close>
lemma trace_refinement_s:
  fixes Tc \<Gamma>a \<Gamma>c Pa Pc ca cc xsl
  assumes pre: "snd (last Tc) \<in> Pc"
      and refines: "((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc)) \<in> refinement_s xsl"
      and concrete_trace: "Tc \<in> finite_traces_s \<Gamma>c cc"
    shows "\<exists>Ta.
      ((\<Gamma>a,{xsl (snd (hd Tc))},fst (hd Ta)),(\<Gamma>c,{snd (hd Tc)},fst (hd Tc))) \<in> refinement_s xsl \<and>
      Ta \<in> finite_traces_s \<Gamma>a ca \<and>
      trace_refines_s xsl Ta Tc"
  using concrete_trace pre
proof(induct)
  case (Start xsc)

  from Start refines
  have "((\<Gamma>a,{xsl (snd (hd [(cc, xsc)]))},fst (hd [(ca,xsl xsc)])),
         (\<Gamma>c, {snd (hd [(cc, xsc)])},fst (hd [(cc, xsc)])))
               \<in> refinement_s xsl"
    by(auto elim:refinement_s_strengthen)
  moreover have "[(ca,xsl xsc)] \<in> finite_traces_s \<Gamma>a ca"
    by(rule finite_traces_s.Start)
  moreover have "trace_refines_s xsl [(ca, xsl xsc)] [(cc, xsc)]"
    by(auto intro:trace_refines_s.intros)
  ultimately show ?case by(blast)

next
  case (Step cc' xsc' Tc cc'' xsc'')

  from Step obtain Ta
    where refines': "((\<Gamma>a, {xsl xsc'}, fst (hd Ta)), (\<Gamma>c, {xsc'}, cc')) \<in> refinement_s xsl"
      and abstract_trace: "Ta \<in> finite_traces_s \<Gamma>a ca"
      and IH: "trace_refines_s xsl Ta ((cc', xsc') # Tc)"
    by(auto)

  from IH have match: "snd (hd Ta) = xsl xsc'"
    by(cases, auto)

  from refinement_s_stepE[OF refines' _ Step(3)]
  obtain ca''
    where stepa: "SmallStep.step \<Gamma>a (fst (hd Ta), snd (hd Ta)) (ca'', xsl xsc'')"
      and refines'': "((\<Gamma>a, {xsl xsc''}, ca''), (\<Gamma>c, {xsc''}, cc'')) \<in> refinement_s xsl"
    by(auto simp:match)

  from refines''
  have "((\<Gamma>a, {xsl (snd (hd ((cc'', xsc'') # (cc', xsc') # Tc)))}, fst (hd ((ca'',xsl xsc'') # Ta))),
         (\<Gamma>c, {snd (hd ((cc'', xsc'') # (cc', xsc') # Tc))}, fst (hd ((cc'', xsc'') # (cc', xsc') # Tc))))
           \<in> refinement_s xsl"
    by(simp)
  moreover {
    from abstract_trace have "(fst (hd Ta), snd (hd Ta)) # tl Ta \<in> finite_traces_s \<Gamma>a ca"
      by(cases, auto)
    from finite_traces_s.Step[OF this stepa] finite_trace_nonempty_s[OF abstract_trace]
    have "(ca'',xsl xsc'') # Ta \<in> finite_traces_s \<Gamma>a ca"
      by(simp)
  }
  moreover from IH
  have "trace_refines_s xsl ((ca'',xsl xsc'') # Ta) ((cc'', xsc'') # (cc', xsc') # Tc)"
    by(rule trace_refines_s.Step)
  ultimately show ?case by(blast)
qed

text \<open>Elimination form of the above, for getting one's grubby little hands on an abstract trace.\<close>
lemma trace_refinement_sE:
  fixes Tc \<Gamma>a \<Gamma>c Pa Pc ca cc xsl
  assumes pre: "snd (last Tc) \<in> Pc"
      and refines: "((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc)) \<in> refinement_s xsl"
      and concrete_trace: "Tc \<in> finite_traces_s \<Gamma>c cc"
  obtains (abstract_trace) Ta
    where "((\<Gamma>a,{xsl (snd (hd Tc))},fst (hd Ta)),(\<Gamma>c,{snd (hd Tc)},fst (hd Tc))) \<in> refinement_s xsl"
      and "Ta \<in> finite_traces_s \<Gamma>a ca"
      and "trace_refines_s xsl Ta Tc"
  using trace_refinement_s[OF assms] by(blast)

definition separable_lift :: "('sc \<Rightarrow> 'sa) \<Rightarrow> ('fc \<Rightarrow> 'fa) \<Rightarrow> ('sa,'fa,'sc,'fc) xstate_lift_s"
  where "separable_lift sl fl = (\<lambda>xsc. case xsc of
    Semantic.Stuck \<Rightarrow> Semantic.Stuck
  | Semantic.Normal sc \<Rightarrow> Semantic.Normal (sl sc)
  | Semantic.Abrupt sc \<Rightarrow> Semantic.Abrupt (sl sc)
  | Semantic.Fault fc \<Rightarrow> Semantic.Fault (fl fc))"

(* XXX - move *)
lemma final_s_cases:
  assumes "SmallStep.final cfg"
  obtains
    (Skip) xs where "cfg = (Language.Skip, xs)"
  | (Throw) s where "cfg = (Language.Throw, Semantic.Normal s)"
  using assms unfolding SmallStep.final_def by(cases cfg, auto)

definition abrupt_consistent :: "('sa,'fa,'sc,'fc) xstate_lift_s \<Rightarrow> bool"
  where "abrupt_consistent xsl \<longleftrightarrow> (\<forall>sa sc.
          Semantic.Normal sa = xsl (Semantic.Normal sc) \<longrightarrow>
          Semantic.Abrupt sa = xsl (Semantic.Abrupt sc)
        )"

lemma abrupt_consistentE:
  fixes xsl sa sc
  assumes "abrupt_consistent xsl" and "Semantic.Normal sa = xsl (Semantic.Normal sc)"
  shows "Semantic.Abrupt sa = xsl (Semantic.Abrupt sc)"
  using assms unfolding abrupt_consistent_def by(auto)

lemma separable_lift_mp:
  "mode_preserving (separable_lift sl fl)"
  unfolding mode_preserving_def
proof
  fix xsc
  show "(\<exists>sa. separable_lift sl fl xsc = Semantic.xstate.Normal sa) = (\<exists>sc. xsc = Semantic.xstate.Normal sc) \<and>
        (\<exists>sa. separable_lift sl fl xsc = Abrupt sa) = (\<exists>sc. xsc = Abrupt sc) \<and>
        (\<exists>fa. separable_lift sl fl xsc = Semantic.xstate.Fault fa) = (\<exists>fc. xsc = Semantic.xstate.Fault fc) \<and>
        (separable_lift sl fl xsc = Semantic.xstate.Stuck) = (xsc = Semantic.xstate.Stuck)"
    by(cases xsc, auto simp:separable_lift_def)
qed

lemma separable_lift_ac:
  "abrupt_consistent (separable_lift sl fl)"
  unfolding abrupt_consistent_def separable_lift_def
  by(auto)

lemma refinement_exec_s:
    fixes ca cc xsl \<Gamma>a \<Gamma>c Pa Pc xsc xsc'
  assumes refines: "((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc)) \<in> refinement_s xsl"
      and bigstepc: "Semantic.exec \<Gamma>c cc xsc xsc'"
      and Pc: "xsc \<in> Pc"
      and mp: "mode_preserving xsl"
      and ac: "abrupt_consistent xsl"
    shows "Semantic.exec \<Gamma>a ca (xsl xsc) (xsl xsc')"
proof(cases "isAbr xsc'")
  case True
  then obtain sc where rw_xsc': "xsc' = Semantic.Abrupt sc" by(auto elim:isAbrE)

  show ?thesis
  proof(cases "xsc = xsc'")
    case True
    with rw_xsc' exec_impl_steps[OF bigstepc]
    have stepsc: "(rtranclp (SmallStep.step \<Gamma>c)) (cc,xsc) (Language.Skip,xsc)"
      by(auto)

    from refines Pc stepsc
    obtain ca'
      where refines': "((\<Gamma>a,{xsl xsc},ca'), (\<Gamma>c,{xsc},Language.Skip)) \<in> refinement_s xsl"
        and bigstepa: "(rtranclp (SmallStep.step \<Gamma>a)) (ca, xsl xsc) (ca', xsl xsc)"
      by(auto elim:refinement_s_stepsE)

    have "SmallStep.final (Language.Skip,xsc)"
      unfolding SmallStep.final_def by(auto)
    with mp refines' have finala: "SmallStep.final (ca',xsl xsc)"
      by(auto elim:refinement_s_finalE)

    from finala show ?thesis
    proof(cases rule:final_s_cases)
      case (Skip xs)
      with bigstepa True show ?thesis
        by(auto intro:steps_Skip_impl_exec)                         

    next
      case (Throw sa)
      with True rw_xsc' mp show ?thesis
        by(auto elim!:mode_preserving_AbruptcE)
    qed

  next
    case False
    with rw_xsc' exec_impl_steps[OF bigstepc]
    have stepsc: "(rtranclp (SmallStep.step \<Gamma>c)) (cc,xsc) (Language.Throw, Semantic.Normal sc)"
      by(auto)

    from refines Pc stepsc
    obtain ca'
      where refines': "((\<Gamma>a,{xsl (Semantic.Normal sc)},ca'),
                        (\<Gamma>c,{Semantic.Normal sc},Language.Throw)) \<in> refinement_s xsl"
        and bigstepa: "(rtranclp (SmallStep.step \<Gamma>a)) (ca, xsl xsc) (ca', xsl (Semantic.Normal sc))"
      by(auto elim:refinement_s_stepsE)

    have "SmallStep.final (Language.Throw, Semantic.Normal sc)"
      unfolding SmallStep.final_def by(auto)
    with mp  refines' have finala: "SmallStep.final (ca',xsl (Semantic.Normal sc))"
      by(auto elim:refinement_s_finalE)

    from finala show ?thesis
    proof(cases rule:final_s_cases)
      case (Skip xs)
      with refines' show ?thesis by(auto dest:refinement_s_throwcE)
    next
      case (Throw sa)
      with bigstepa have "Semantic.exec \<Gamma>a ca (xsl xsc) (Semantic.Abrupt sa)"
        by(auto intro:steps_Throw_impl_exec)
      moreover from Throw abrupt_consistentE[OF ac] rw_xsc'
      have "Semantic.Abrupt sa = xsl xsc'"
        by(simp)
      ultimately show ?thesis by(simp)
    qed
  qed
next
  case False
  with exec_impl_steps[OF bigstepc]
  have stepsc: "(rtranclp (SmallStep.step \<Gamma>c)) (cc,xsc) (Language.Skip,xsc')"
    unfolding isAbr_def by(cases xsc', auto)

    from refines Pc stepsc
    obtain ca'
      where refines': "((\<Gamma>a,{xsl xsc'},ca'), (\<Gamma>c,{xsc'},Language.Skip)) \<in> refinement_s xsl"
        and bigstepa: "(rtranclp (SmallStep.step \<Gamma>a)) (ca, xsl xsc) (ca', xsl xsc')"
      by(auto elim:refinement_s_stepsE)

  have "SmallStep.final (Language.Skip, xsc')"
    unfolding SmallStep.final_def by(auto)
  with mp refines' have finala: "SmallStep.final (ca',xsl xsc')"
    by(auto elim:refinement_s_finalE)

  from finala show ?thesis
  proof(cases rule:final_s_cases)
    case (Skip xs)
    with bigstepa show "Semantic.exec \<Gamma>a ca (xsl xsc) (xsl xsc')"
      by(auto intro:steps_Skip_impl_exec)
  next
    case (Throw sa)
    with refines' show ?thesis by(auto dest:refinement_s_throwaE)
  qed
qed

lemma valid_sE:
  fixes \<Gamma> F P c Q A s t
  assumes valid: "HoarePartialDef.valid \<Gamma> F P c Q A" 
      and exec: "Semantic.exec \<Gamma> c s t"
      and pre: "s \<in> Semantic.Normal ` P"
      and nofault: "t \<notin> Semantic.Fault ` F"
    obtains (Normal) "t \<in> Semantic.Normal ` Q" | (Abrupt) "t \<in> Semantic.Abrupt ` A"
  using assms unfolding HoarePartialDef.valid_def by(blast)

text \<open>Refinement preserves (partial) Hoare triples\<close>
lemma refinement_valid_s:
    fixes ca cc sl fl \<Gamma>a \<Gamma>c Pa Pc F P Q A
    assumes refines: "((\<Gamma>a,Pa,ca),(\<Gamma>c,Pc,cc)) \<in> refinement_s (separable_lift sl fl)"
      and weakenc: "Semantic.Normal ` sl -` P \<subseteq> Pc"
      and valida: "HoarePartialDef.valid \<Gamma>a F P ca Q A"
    shows "HoarePartialDef.valid \<Gamma>c (fl-`F) (sl-`P) cc (sl-`Q) (sl-`A)"
proof(rule HoarePartialDef.validI)
  fix sc xsc'
  assume execc: "Semantic.exec \<Gamma>c cc (Semantic.Normal sc) xsc'"
     and imgP: "sc \<in> sl -` P"
     and noF: "xsc' \<notin> Semantic.xstate.Fault ` fl -` F"

  from imgP weakenc have Pc: "Semantic.Normal sc \<in> Pc" by(auto)

  from refinement_exec_s[OF refines execc Pc separable_lift_mp separable_lift_ac]
  have execa: "Semantic.exec \<Gamma>a ca (separable_lift sl fl (Semantic.xstate.Normal sc))
                 (separable_lift sl fl xsc')" .

  note valida execa
  moreover {
    have "separable_lift sl fl (Semantic.Normal sc) = Semantic.Normal (sl sc)"
      by(simp add:separable_lift_def)
    also from imgP have "... \<in> Semantic.Normal ` P"
      by(auto)
    finally have "separable_lift sl fl (Semantic.Normal sc) \<in> Semantic.Normal ` P" .
  }
  moreover from noF have "separable_lift sl fl xsc' \<notin> Semantic.Fault ` F"
  proof(rule contrapos_nn)
    assume "separable_lift sl fl xsc' \<in> Semantic.Fault ` F"
    then obtain fa
      where faulta: "separable_lift sl fl xsc' = Semantic.Fault fa"
        and saF: "fa \<in> F"
      by(auto)

    from mode_preserving_FaultaE[OF separable_lift_mp faulta]
    obtain fc where faultc: "xsc' = Semantic.Fault fc"
      by(blast)

    from faulta faultc have "fa = fl fc"
      by(simp add:separable_lift_def)
    with saF have "fc \<in> fl -` F"
      by(auto)
    with faultc
    show "xsc' \<in> Semantic.Fault ` fl -` F"
      by(auto)
  qed
  ultimately show "xsc' \<in> Semantic.Normal ` sl -` Q \<union> Semantic.Abrupt ` sl -` A"
  proof(cases rule:valid_sE)
    case Normal
    then obtain sa
      where normala: "separable_lift sl fl xsc' = Semantic.Normal sa"
        and saQ: "sa \<in> Q"
      by(auto)

    from mode_preserving_NormalaE[OF separable_lift_mp normala]
    obtain sc where normalc: "xsc' = Semantic.Normal sc"
      by(blast)

    from normala normalc have "sa = sl sc"
      by(simp add:separable_lift_def)
    with saQ have "sc \<in> sl -` Q"
      by(auto)
    with normalc
    have "xsc' \<in> Semantic.Normal ` sl -` Q"
      by(auto)
    thus ?thesis
      by(blast)
  next
    case Abrupt
    then obtain sa
      where abrupta: "separable_lift sl fl xsc' = Semantic.Abrupt sa"
        and saA: "sa \<in> A"
      by(auto)

    from mode_preserving_AbruptaE[OF separable_lift_mp abrupta]
    obtain sc where abruptc: "xsc' = Semantic.Abrupt sc"
      by(blast)

    from abrupta abruptc have "sa = sl sc"
      by(simp add:separable_lift_def)
    with saA have "sc \<in> sl -` A"
      by(auto)
    with abruptc
    have "xsc' \<in> Semantic.Abrupt ` sl -` A"
      by(auto)
    thus ?thesis
      by(blast)
  qed
qed

lemma refinement_s_SkipI:
  assumes stricter: "xsl ` Pc \<subseteq> Pa"
  shows "((\<Gamma>a,Pa,Language.Skip), (\<Gamma>c,Pc,Language.Skip)) \<in> refinement_s xsl"
proof(rule refinement_s.Step[OF _ stricter])
  show "(Language.Skip = Language.Throw) = (Language.Skip = Language.Throw)" by(auto)
next
  fix xsa
  show "Language.Skip = Language.Skip" by(simp)
next
  fix xsa xsc xsc' cc'
  assume stepc: "SmallStep.step \<Gamma>c (Language.com.Skip, xsc) (cc', xsc')"
  thus "\<exists>ca'.
          SmallStep.step \<Gamma>a (Language.com.Skip, xsa) (ca', xsl xsc') \<and>
          ((\<Gamma>a,{xsl xsc'},ca'), (\<Gamma>c,{xsc'},cc')) \<in> refinement_s xsl"
    by(blast elim:SmallStep.step.cases)
qed

lemma refinement_s_ThrowI:
  assumes stricter: "separable_lift sl fl ` Pc \<subseteq> Pa"
  shows "((\<Gamma>a,Pa,Language.Throw), (\<Gamma>c,Pc,Language.Throw)) \<in> refinement_s (separable_lift sl fl)"
proof(rule refinement_s.Step[OF _ stricter])
  show "(Language.Throw = Language.Throw) = (Language.Throw = Language.Throw)" by(simp)
next
  assume "Language.Throw = Language.Skip"
  thus "Language.Throw = Language.Skip"
    by(simp)
next
  fix xsc xsc' cc'
  assume Pc: "xsc \<in> Pc"

  assume "SmallStep.step \<Gamma>c(Language.com.Throw, xsc) (cc', xsc')"
  thus "\<exists>ca'.
          SmallStep.step \<Gamma>a (Language.com.Throw, separable_lift sl fl xsc)
                            (ca', separable_lift sl fl xsc') \<and>
          ((\<Gamma>a,{separable_lift sl fl xsc'},ca'), (\<Gamma>c,{xsc'},cc'))
            \<in> refinement_s (separable_lift sl fl)"
  proof(cases rule:SmallStep.step.cases)
    case (FaultProp fc)

    have "SmallStep.step \<Gamma>a (Language.Throw, separable_lift sl fl xsc)
                            (Language.Skip, separable_lift sl fl xsc')"
      by(auto simp:FaultProp separable_lift_def intro:SmallStep.step.FaultProp)
    moreover {
      have "separable_lift sl fl xsc' = Semantic.xstate.Fault (fl fc)"
        by(simp add:FaultProp separable_lift_def)
    
      hence "((\<Gamma>a, {separable_lift sl fl xsc'}, Language.Skip),
                      (\<Gamma>c, {xsc'}, cc')) \<in> refinement_s (separable_lift sl fl)"
        by(auto simp:FaultProp intro:refinement_s_SkipI)
    }
    ultimately show ?thesis by(blast)

  next
    case StuckProp

    have "SmallStep.step \<Gamma>a (Language.Throw, separable_lift sl fl xsc)
                            (Language.Skip, separable_lift sl fl xsc')"
      by(auto simp:StuckProp separable_lift_def intro:SmallStep.step.StuckProp)
    moreover {
      have "separable_lift sl fl xsc' = Semantic.Stuck"
        by(simp add:StuckProp separable_lift_def)
    
      hence "((\<Gamma>a, {separable_lift sl fl xsc'}, Language.Skip),
                      (\<Gamma>c, {xsc'}, cc')) \<in> refinement_s (separable_lift sl fl)"
        by(auto simp:StuckProp intro:refinement_s_SkipI)
    }
    ultimately show ?thesis by(blast)

  next
    case (AbruptProp sc)

    have "SmallStep.step \<Gamma>a (Language.Throw, separable_lift sl fl xsc)
                            (Language.Skip, separable_lift sl fl xsc')"
      by(auto simp:AbruptProp separable_lift_def intro:SmallStep.step.AbruptProp)
    moreover {
      have "separable_lift sl fl xsc' = Semantic.xstate.Abrupt (sl sc)"
        by(simp add:AbruptProp separable_lift_def)
    
      hence "((\<Gamma>a, {separable_lift sl fl xsc'}, Language.Skip),
                      (\<Gamma>c, {xsc'}, cc')) \<in> refinement_s (separable_lift sl fl)"
        by(auto simp:AbruptProp intro:refinement_s_SkipI)
    }
    ultimately show ?thesis by(blast)
  qed
qed

lemma refinement_s_BasicI:
  assumes fun_rel: "\<And>sc. Semantic.Normal sc \<in> Pc \<Longrightarrow> sl (g sc) = f (sl sc)"
      and stricter: "separable_lift sl fl ` Pc \<subseteq> Pa"
    shows "((\<Gamma>a,Pa,Language.Basic f), (\<Gamma>c,Pc,Language.Basic g)) \<in> refinement_s (separable_lift sl fl)"
proof(rule refinement_s.Step[OF _ stricter])
  show "(Language.com.Basic g = THROW) = (Language.com.Basic f = THROW)"
    by(auto)
next
  fix xsa xsc
  assume "Language.com.Basic g = Language.Skip"
  thus "Language.com.Basic f = Language.Skip"
    by(simp)
next
  fix xsc xsc' cc'
  assume Pc: "xsc \<in> Pc"
     and stepc: "SmallStep.step \<Gamma>c(Language.com.Basic g, xsc) (cc', xsc')"

  from stepc
  show "\<exists>ca'.
          SmallStep.step \<Gamma>a (Language.com.Basic f, separable_lift sl fl xsc)
                            (ca', separable_lift sl fl xsc') \<and>
          ((\<Gamma>a, {separable_lift sl fl xsc'}, ca'), (\<Gamma>c, {xsc'}, cc'))
            \<in> refinement_s (separable_lift sl fl)"
  proof(cases rule:SmallStep.step.cases)
    case (Basic sc)

    from Basic Pc have "Semantic.Normal sc \<in> Pc" by(simp)
    hence "separable_lift sl fl xsc' = Semantic.Normal (f (sl sc))"
      by(simp add:Basic separable_lift_def fun_rel)
    hence "SmallStep.step \<Gamma>a (Language.Basic f, separable_lift sl fl xsc)
                            (Language.Skip, separable_lift sl fl xsc')"
      by(auto simp:Basic separable_lift_def intro:SmallStep.step.Basic)
    moreover have "((\<Gamma>a, {separable_lift sl fl xsc'}, Language.Skip),
                    (\<Gamma>c, {xsc'}, cc')) \<in> refinement_s (separable_lift sl fl)"
      by(auto simp:Basic intro:refinement_s_SkipI)
    ultimately show ?thesis by(blast)

  next
    case (FaultProp fc)

    have "SmallStep.step \<Gamma>a (Language.Basic f, separable_lift sl fl xsc)
                            (Language.Skip, separable_lift sl fl xsc')"
      by(auto simp:FaultProp separable_lift_def intro:SmallStep.step.FaultProp)
    moreover {
      have "separable_lift sl fl xsc' = Semantic.xstate.Fault (fl fc)"
        by(simp add:FaultProp separable_lift_def)
    
      hence "((\<Gamma>a, {separable_lift sl fl xsc'}, Language.Skip),
                      (\<Gamma>c, {xsc'}, cc')) \<in> refinement_s (separable_lift sl fl)"
        by(auto simp:FaultProp intro:refinement_s_SkipI)
    }
    ultimately show ?thesis by(blast)


  next
    case StuckProp

    have "SmallStep.step \<Gamma>a (Language.Basic f, separable_lift sl fl xsc)
                            (Language.Skip, separable_lift sl fl xsc')"
      by(auto simp:StuckProp separable_lift_def intro:SmallStep.step.StuckProp)
    moreover {
      have "separable_lift sl fl xsc' = Semantic.Stuck"
        by(simp add:StuckProp separable_lift_def)
    
      hence "((\<Gamma>a, {separable_lift sl fl xsc'}, Language.Skip),
                      (\<Gamma>c, {xsc'}, cc')) \<in> refinement_s (separable_lift sl fl)"
        by(auto simp:StuckProp intro:refinement_s_SkipI)
    }
    ultimately show ?thesis by(blast)

  next
    case (AbruptProp sc)

    have "SmallStep.step \<Gamma>a (Language.Basic f, separable_lift sl fl xsc)
                            (Language.Skip, separable_lift sl fl xsc')"
      by(auto simp:AbruptProp separable_lift_def intro:SmallStep.step.AbruptProp)
    moreover {
      have "separable_lift sl fl xsc' = Semantic.xstate.Abrupt (sl sc)"
        by(simp add:AbruptProp separable_lift_def)
    
      hence "((\<Gamma>a, {separable_lift sl fl xsc'}, Language.Skip),
                      (\<Gamma>c, {xsc'}, cc')) \<in> refinement_s (separable_lift sl fl)"
        by(auto simp:AbruptProp intro:refinement_s_SkipI)
    }
    ultimately show ?thesis by(blast)
  qed
qed

lemma valid_step:
  assumes valid: "HoarePartialDef.valid \<Gamma> F P c Q A"
      and step: "SmallStep.step \<Gamma> (c,Semantic.Normal s) (c',Semantic.Normal s')"
      and pre: "s \<in> P"
    shows "HoarePartialDef.valid \<Gamma> F {s'} c' Q A"
proof(rule HoarePartialDef.validI)
  fix s_h t
  assume "Semantic.exec \<Gamma> c' (Semantic.Normal s_h) t"
     and "s_h \<in> {s'}"
  hence exec': "Semantic.exec \<Gamma> c' (Semantic.Normal s') t"
    by(simp)
  with step have exec: "Semantic.exec \<Gamma> c (Semantic.Normal s) t"
    by(rule SmallStep.step_extend)

  from pre have Ps: "Semantic.Normal s \<in> Semantic.Normal ` P"
    by(auto)

  assume nofault: "t \<notin> Semantic.Fault ` F"

  from valid exec Ps nofault
  show "t \<in> Semantic.xstate.Normal ` Q \<union> Abrupt ` A"
    by(cases rule:valid_sE, auto)
qed

lemma valid_s_emptypre:
  "HoarePartialDef.valid \<Gamma> F {} c Q A"
  by(blast intro:HoarePartialDef.validI)

lemma step_NormalE:
  fixes c c'::"('s,'p,'f) Language.com"
    and xs::"('s,'f) Semantic.xstate"
    and s'::'s
  assumes "SmallStep.step \<Gamma> (c,xs) (c',Semantic.Normal s')"
  obtains s where "xs = Semantic.Normal s"
  using assms
    by(induct cfg \<equiv> "(c,xs)"
              cfg' \<equiv> "(c',Semantic.Normal s')::('s,'p,'f) Language.com \<times> ('s,'f) Semantic.xstate"
              arbitrary:c c'
              rule:SmallStep.step.induct,
       auto)

lemma step_AbruptE:
  fixes c c'::"('s,'p,'f) Language.com"
    and xs::"('s,'f) Semantic.xstate"
    and s::'s
  assumes "SmallStep.step \<Gamma> (c,xs) (c',Semantic.Abrupt s)"
  shows "xs = Semantic.Abrupt s"
  using assms
    by(induct cfg \<equiv> "(c,xs)"
              cfg' \<equiv> "(c',Semantic.Abrupt s)::('s,'p,'f) Language.com \<times> ('s,'f) Semantic.xstate"
              arbitrary:c c'
              rule:SmallStep.step.induct,
       auto)

lemma step_FaultE:
  fixes c c'::"('s,'p,'f) Language.com"
    and xs::"('s,'f) Semantic.xstate"
    and f::'f
  assumes "SmallStep.step \<Gamma> (c,xs) (c',Semantic.Fault f)"
  obtains (FaultProp) "xs = Semantic.Fault f" |
          (NewFault) s where "xs = Semantic.Normal s"
  using assms
  by(induct cfg \<equiv> "(c,xs)"
            cfg' \<equiv> "(c',Semantic.Fault f)::('s,'p,'f) Language.com \<times> ('s,'f) Semantic.xstate"
            arbitrary:c c'
            rule:SmallStep.step.induct,
     auto)

lemma refinement_s_SeqI:
  assumes refines_c1: "((\<Gamma>a,P1a,c1a),(\<Gamma>c,P1c,c1c)) \<in> refinement_s (separable_lift sl fl)"
      and refines_c2: "((\<Gamma>a,P2a,c2a),(\<Gamma>c,P2c,c2c)) \<in> refinement_s (separable_lift sl fl)"
      and valid: "HoarePartialDef.valid \<Gamma>a F P c1a Q A"
      and preFault: "\<And>fa. Semantic.Fault fa \<in> P1a \<Longrightarrow> fa \<in> F"
      and preAbrupt: "\<And>sa. Semantic.Abrupt sa \<in> P1a \<Longrightarrow> sa \<in> A"
      and preNormal: "\<And>sa. Semantic.Normal sa \<in> P1a \<Longrightarrow> sa \<in> P"
      and propStuck: "(\<forall>xsc. xsc \<in> P1c \<longrightarrow> \<not>Semantic.exec \<Gamma>c c1c xsc Semantic.Stuck) \<or>
                      Semantic.Stuck \<in> P2c"
      and postFault: "\<And>fc. fl fc \<in> F \<Longrightarrow> Semantic.Fault fc \<in> P2c"
      and postAbrupt: "\<And>sc. sl sc \<in> A \<Longrightarrow> Semantic.Abrupt sc \<in> P2c"
      and postNormal: "\<And>sc. sl sc \<in> Q \<Longrightarrow> Semantic.Normal sc \<in> P2c"
    shows "((\<Gamma>a,P1a,Language.Seq c1a c2a), (\<Gamma>c,P1c,Language.Seq c1c c2c))
            \<in> refinement_s (separable_lift sl fl)"
  using refines_c1 refines_c2 valid preNormal preAbrupt preFault propStuck
proof(induct arbitrary:P)
  case (Step P1c \<Gamma>c c1c \<Gamma>a c1a P1a)

  show ?case
  proof(rule refinement_s.Step)
    show "(Language.Seq c1c c2c = THROW) = (Language.Seq c1a c2a = THROW)" by(auto)

  next
    fix xsa xsc
    assume "Language.Seq c1c c2c = Language.Skip"
    thus "Language.Seq c1a c2a = Language.Skip"
      by(simp)

  next
    from Step.hyps(2) show "separable_lift sl fl ` P1c \<subseteq> P1a" .

  next
    fix xsc xsc' cc'
    assume Pc: "xsc \<in> P1c"
       and stepc: "SmallStep.step \<Gamma>c (Language.Seq c1c c2c, xsc) (cc', xsc')"

    from stepc
    show "\<exists>ca'.
            SmallStep.step \<Gamma>a (Language.Seq c1a c2a, separable_lift sl fl xsc)
                              (ca', separable_lift sl fl xsc') \<and>
            ((\<Gamma>a, {separable_lift sl fl xsc'}, ca'), \<Gamma>c, {xsc'}, cc')
              \<in> refinement_s (separable_lift sl fl)"
    proof(cases rule:SmallStep.step.cases)
      case (Seq c1c')

      from Step.hyps(1)[OF Pc Seq(2)] Step.prems(1) obtain c1a'
        where step_c1a: "SmallStep.step \<Gamma>a (c1a, separable_lift sl fl xsc)
                                           (c1a', separable_lift sl fl xsc')"
          and refines_c1a': "((\<Gamma>a, {separable_lift sl fl xsc'}, c1a'), (\<Gamma>c, {xsc'}, c1c'))
                              \<in> refinement_s (separable_lift sl fl)"
          and IH: "\<forall>P. HoarePartialDef.valid \<Gamma>a F P c1a' Q A \<longrightarrow>
                      (\<forall>sa'. Semantic.Normal sa' \<in> {separable_lift sl fl xsc'} \<longrightarrow> sa' \<in> P) \<longrightarrow>
                      (\<forall>sa'. Semantic.Abrupt sa' \<in> {separable_lift sl fl xsc'} \<longrightarrow> sa' \<in> A) \<longrightarrow>
                      (\<forall>fa'. Semantic.xstate.Fault fa' \<in> {separable_lift sl fl xsc'} \<longrightarrow> fa' \<in> F) \<longrightarrow>
                      ((\<forall>xsc. xsc \<in> {xsc'} \<longrightarrow> \<not> Semantic.exec \<Gamma>c c1c' xsc Semantic.xstate.Stuck) \<or>
                          Semantic.xstate.Stuck \<in> P2c) \<longrightarrow>
                      ((\<Gamma>a, {separable_lift sl fl xsc'}, Language.Seq c1a' c2a),
                       (\<Gamma>c, {xsc'}, Language.Seq c1c' c2c)) \<in> refinement_s (separable_lift sl fl)"
        by(blast)

      from step_c1a have "SmallStep.step \<Gamma>a (Language.Seq c1a c2a, separable_lift sl fl xsc)
                                            (Language.Seq c1a' c2a, separable_lift sl fl xsc')"
        by(rule SmallStep.step.Seq)
      moreover {
        let ?P' = "case xsc' of Semantic.Normal sc' \<Rightarrow> {sl sc'} | _ \<Rightarrow> {}"
        have "HoarePartialDef.valid \<Gamma>a F ?P' c1a' Q A"
        proof(cases xsc')
          case (Normal sc')
          hence rw_xsa': "separable_lift sl fl xsc' = Semantic.Normal (sl sc')"
            by(simp add:separable_lift_def)

          from step_c1a rw_xsa' obtain sa
            where rw_xsa_initial: "separable_lift sl fl xsc = Semantic.Normal sa"
            by(auto elim:step_NormalE)
          then obtain sc
            where rw_xsc: "xsc = Semantic.Normal sc"
            by(auto elim:mode_preserving_NormalaE[OF separable_lift_mp])
          with rw_xsa_initial have rw_sa: "sa = sl sc"
            by(simp add:separable_lift_def)
          with rw_xsa_initial have rw_xsa: "separable_lift sl fl xsc = Semantic.Normal (sl sc)"
            by(simp)

          note rw_xsa[symmetric]
          also from Pc have "separable_lift sl fl xsc \<in> separable_lift sl fl ` P1c"
            by(auto)
          also note Step.hyps(2)
          finally have P1a: "Semantic.xstate.Normal (sl sc) \<in> P1a" .
          hence P: "sl sc \<in> P"
            by(rule Step.prems(3))

          from Step.prems(2) step_c1a[unfolded rw_xsa rw_xsa'] P
          have "HoarePartialDef.valid \<Gamma>a F {sl sc'} c1a' Q A"
            by(rule valid_step)
          with Normal show ?thesis by(simp)

        next
          case (Abrupt sc')
          then show ?thesis by(simp add:valid_s_emptypre)

        next
          case (Fault x3)
          then show ?thesis by(simp add:valid_s_emptypre)

        next
          case Stuck
          then show ?thesis by(simp add:valid_s_emptypre)
        qed
        moreover have "\<forall>sa'. Semantic.xstate.Normal sa' \<in> {separable_lift sl fl xsc'} \<longrightarrow> sa' \<in> ?P'"
          by(cases xsc', simp_all add:separable_lift_def)
        moreover have "\<forall>sa'. Semantic.Abrupt sa' \<in> {separable_lift sl fl xsc'} \<longrightarrow> sa' \<in> A"
        proof(clarify)
          fix sa
          assume abr: "Semantic.Abrupt sa = separable_lift sl fl xsc'"

          from step_c1a have [symmetric] : "separable_lift sl fl xsc = Semantic.Abrupt sa"
            unfolding abr[symmetric] by(rule step_AbruptE)
          also from Pc have "separable_lift sl fl xsc \<in> separable_lift sl fl ` P1c"
            by(auto)
          also note Step.hyps(2)
          finally show "sa \<in> A"
            by(rule Step.prems(4))
        qed
        moreover have "(\<forall>fa'. Semantic.xstate.Fault fa' \<in> {separable_lift sl fl xsc'} \<longrightarrow> fa' \<in> F)"
        proof(clarify, rule contrapos_pp, assumption)
          fix fa'
          assume fault: "Semantic.Fault fa' = separable_lift sl fl xsc'"
             and nF: "fa' \<notin> F"

          from step_c1a fault
          have fault_step: "SmallStep.step  \<Gamma>a (c1a, separable_lift sl fl xsc) (c1a', Semantic.Fault fa')"
            by(simp)
          moreover have "Semantic.exec \<Gamma>a c1a' (Semantic.Fault fa') (Semantic.Fault fa')"
            by(auto)
          ultimately
          have execa: "Semantic.exec \<Gamma>a c1a (separable_lift sl fl xsc) (Semantic.Fault fa')"
            by(rule step_extend)

          from Pc have "separable_lift sl fl xsc \<in> separable_lift sl fl ` P1c"
            by(auto)
          also note Step.hyps(2)
          finally have P1a: "separable_lift sl fl xsc \<in> P1a" .

          from fault_step
          show "Semantic.xstate.Fault fa' \<noteq> separable_lift sl fl xsc'"
          proof(cases rule:step_FaultE)
            case FaultProp
            with Step.prems(5) P1a have "fa' \<in> F"
              by(auto)
            with nF show ?thesis
              by(auto)
          next
            case (NewFault s)
            with Step.prems(3) P1a
            have "separable_lift sl fl xsc \<in> Semantic.xstate.Normal ` P"
              by(auto)
            moreover from nF have "Semantic.xstate.Fault fa' \<notin> Semantic.xstate.Fault ` F"
              by(auto)
            moreover note Step.prems(2) execa
            ultimately show ?thesis
              by(auto elim:valid_sE)
          qed
        qed
        moreover from Step.prems(6)
        have "((\<forall>xsc. xsc \<in> {xsc'} \<longrightarrow> \<not> Semantic.exec \<Gamma>c c1c' xsc Semantic.xstate.Stuck) \<or>
              Semantic.xstate.Stuck \<in> P2c)"
        proof
          assume "Semantic.xstate.Stuck \<in> P2c"
          thus ?thesis by(auto)
        next
          assume nostuck: "\<forall>xsc. xsc \<in> P1c \<longrightarrow> \<not> Semantic.exec \<Gamma>c c1c xsc Semantic.xstate.Stuck"
          hence "\<forall>xsc. xsc \<in> {xsc'} \<longrightarrow> \<not> \<Gamma>c\<turnstile> \<langle>c1c',xsc\<rangle> \<Rightarrow> Semantic.xstate.Stuck"
          proof(rule contrapos_pp)
            assume "\<not> (\<forall>xsc. xsc \<in> {xsc'} \<longrightarrow> \<not> \<Gamma>c\<turnstile> \<langle>c1c',xsc\<rangle> \<Rightarrow> Semantic.xstate.Stuck)"
            hence "\<Gamma>c\<turnstile> \<langle>c1c',xsc'\<rangle> \<Rightarrow> Semantic.xstate.Stuck"
              by(blast)
            with Seq(2) have "\<Gamma>c\<turnstile> \<langle>c1c,xsc\<rangle> \<Rightarrow> Semantic.xstate.Stuck"
              by(rule step_extend)
            with Pc show "\<not> (\<forall>xsc. xsc \<in> P1c \<longrightarrow> \<not> \<Gamma>c\<turnstile> \<langle>c1c,xsc\<rangle> \<Rightarrow> Semantic.xstate.Stuck)"
              by(blast)
          qed
          thus ?thesis by(auto)
        qed
        ultimately have "((\<Gamma>a, {separable_lift sl fl xsc'}, Language.Seq c1a' c2a),
                          (\<Gamma>c, {xsc'}, Language.Seq c1c' c2c))
                            \<in> refinement_s (separable_lift sl fl)"
          using IH by(auto)
      }
      ultimately show "\<exists>ca'.
        SmallStep.step \<Gamma>a (c1a;; c2a, separable_lift sl fl xsc) (ca', separable_lift sl fl xsc') \<and>
        ((\<Gamma>a,{separable_lift sl fl xsc'},ca'), (\<Gamma>c,{xsc'},cc'))
          \<in> refinement_s (separable_lift sl fl)"
        by(auto simp:Seq)

    next
      case SeqSkip
      with Step have skipa: "c1a = Language.Skip" by(blast)

      have "SmallStep.step \<Gamma>a (c1a;; c2a, separable_lift sl fl xsc)
                              (c2a, separable_lift sl fl xsc')"
        unfolding SeqSkip skipa
        by(rule SmallStep.step.SeqSkip)
      moreover {
        have execa: "Semantic.exec \<Gamma>a c1a (separable_lift sl fl xsc) (separable_lift sl fl xsc)"
          unfolding skipa
          by(cases "separable_lift sl fl xsc", auto intro:Semantic.exec.Skip)

        have "xsc \<in> P2c"
        proof(cases xsc)
          case (Normal sc)
          hence "Semantic.Normal (sl sc) = separable_lift sl fl xsc"
            by(simp add:separable_lift_def)
          also from Pc have "separable_lift sl fl xsc \<in> separable_lift sl fl ` P1c"
            by(auto)
          also note Step.hyps(2)
          finally have "sl sc \<in> P"
            by(rule Step.prems(3))
          with Normal have Pa: "separable_lift sl fl xsc \<in> Semantic.xstate.Normal ` P"
            by(simp add:separable_lift_def)
          moreover from Normal have nofault: "separable_lift sl fl xsc \<notin> Semantic.xstate.Fault ` F"
            by(auto simp:separable_lift_def)

          from Step.prems(2) execa Pa nofault show ?thesis
            by(cases rule:valid_sE, auto simp:Normal separable_lift_def intro:postNormal)

        next
          case (Abrupt sc)
          hence "Semantic.Abrupt (sl sc) = separable_lift sl fl xsc"
            by(simp add:separable_lift_def)
          also from Pc have "separable_lift sl fl xsc \<in> separable_lift sl fl ` P1c"
            by(auto)
          also note Step.hyps(2)
          finally have "sl sc \<in> A"
            by(rule Step.prems(4))
          thus ?thesis
            unfolding Abrupt by(rule postAbrupt)

        next
          case (Fault fc)
          hence "Semantic.Fault (fl fc) = separable_lift sl fl xsc"
            by(simp add:separable_lift_def)
          also from Pc have "separable_lift sl fl xsc \<in> separable_lift sl fl ` P1c"
            by(auto)
          also note Step.hyps(2)
          finally have "fl fc \<in> F"
            by(rule Step.prems(5))
          thus ?thesis
            unfolding Fault by(rule postFault)

        next
          case Stuck

          from Step.prems(6)
          show "xsc \<in> P2c"
            unfolding Stuck
          proof
            assume "Semantic.xstate.Stuck \<in> P2c"
            thus "Semantic.xstate.Stuck \<in> P2c" .
          next
            assume ns: "\<forall>xsc. xsc \<in> P1c \<longrightarrow> \<not> \<Gamma>c\<turnstile> \<langle>c1c,xsc\<rangle> \<Rightarrow> Semantic.Stuck"

            have "Semantic.exec \<Gamma>c c1c xsc Semantic.Stuck"
              unfolding Stuck by(rule Semantic.exec.StuckProp)
            with Pc ns
            show "Semantic.xstate.Stuck \<in> P2c"
              by(auto)
          qed
        qed
        hence "((\<Gamma>a, {separable_lift sl fl xsc'}, c2a), (\<Gamma>c, {xsc'}, cc'))
                        \<in> refinement_s (separable_lift sl fl)"
          unfolding SeqSkip by(auto intro:refinement_s_strengthen[OF Step.prems(1)])
      }
      ultimately show ?thesis by(blast)

    next
      case (SeqThrow sc)

      from SeqThrow
      have normala: "separable_lift sl fl xsc = Semantic.Normal (sl sc)"
       and normala': "separable_lift sl fl xsc' = Semantic.Normal (sl sc)"
        unfolding separable_lift_def by(auto)

      from SeqThrow Step.hyps
      have throwa: "c1a = Language.Throw"
        by(simp)

      have "SmallStep.step \<Gamma>a (Language.Seq c1a c2a, separable_lift sl fl xsc)
                              (Language.Throw, separable_lift sl fl xsc')"
        unfolding throwa normala normala'
        by(rule SmallStep.step.SeqThrow)
      moreover have "((\<Gamma>a, {separable_lift sl fl xsc'}, Language.Throw),
                      (\<Gamma>c, {xsc'}, cc')) \<in> refinement_s (separable_lift sl fl)"
      proof(rule refinement_s.Step)
        show "separable_lift sl fl ` {xsc'} \<subseteq> {separable_lift sl fl xsc'}"
          by(auto)
        show "(cc' = THROW) = (THROW = THROW)"
          by(simp add:SeqThrow)

        assume "cc' = SKIP" thus "THROW = SKIP"
          by(simp add:SeqThrow)

      next
        fix xsc'_h xsc'' cc''
        assume "xsc'_h \<in> {xsc'}"
           and "SmallStep.step \<Gamma>c (cc',xsc'_h) (cc'',xsc'')"
        hence "SmallStep.step \<Gamma>c (cc',xsc') (cc'',xsc'')"
          by(simp)
        then show "\<exists>ca'.
          SmallStep.step \<Gamma>a (Language.Throw, separable_lift sl fl xsc'_h)
                            (ca', separable_lift sl fl xsc'') \<and>
             ((\<Gamma>a, {separable_lift sl fl xsc''}, ca'), (\<Gamma>c, {xsc''}, cc''))
                  \<in> refinement_s (separable_lift sl fl)"
          unfolding SeqThrow by(cases)
      qed
      ultimately show "\<exists>ca'.
        SmallStep.step \<Gamma>a (Language.Seq c1a c2a, separable_lift sl fl xsc)
                          (ca', separable_lift sl fl xsc') \<and>
        ((\<Gamma>a, {separable_lift sl fl xsc'}, ca'), (\<Gamma>c, {xsc'}, cc'))
               \<in> refinement_s (separable_lift sl fl)"
        by(blast)
  
    next
      case (FaultProp f)
      then show ?thesis
        using redex_Seq_ne by(auto)
  
    next
      case StuckProp
      then show ?thesis
        using redex_Seq_ne by(auto)
  
    next
      case (AbruptProp f)
      then show ?thesis
        using redex_Seq_ne by(auto)
    qed
  qed
qed

section \<open>Utility predicates.\<close>
definition "noFault = - Semantic.Fault ` UNIV"
definition "noAbrupt = - Semantic.Abrupt ` UNIV"
definition "noStuck = - {Semantic.Stuck}"

lemma refinement_s_noAbrupt_SeqI:
  assumes refines_c1: "((\<Gamma>a,P1a \<inter> noAbrupt,c1a),(\<Gamma>c,P1c \<inter> noAbrupt,c1c))
                          \<in> refinement_s (separable_lift sl fl)"
      and refines_c2: "((\<Gamma>a,P2a \<inter> noAbrupt,c2a),(\<Gamma>c,P2c \<inter> noAbrupt,c2c))
                          \<in> refinement_s (separable_lift sl fl)"
      and valid: "HoarePartialDef.valid \<Gamma>a F P c1a Q {}"
      and preFault: "\<And>fa. Semantic.Fault fa \<in> P1a \<Longrightarrow> fa \<in> F"
      and preNormal: "\<And>sa. Semantic.Normal sa \<in> P1a \<Longrightarrow> sa \<in> P"
      and propStuck: "(\<forall>xsc. xsc \<in> P1c \<longrightarrow> \<not>Semantic.exec \<Gamma>c c1c xsc Semantic.Stuck) \<or>
                      Semantic.Stuck \<in> P2c"
      and postFault: "\<And>fc. fl fc \<in> F \<Longrightarrow> Semantic.Fault fc \<in> P2c"
      and postNormal: "\<And>sc. sl sc \<in> Q \<Longrightarrow> Semantic.Normal sc \<in> P2c"
    shows "((\<Gamma>a,P1a \<inter> noAbrupt,Language.Seq c1a c2a), (\<Gamma>c,P1c \<inter> noAbrupt,Language.Seq c1c c2c))
            \<in> refinement_s (separable_lift sl fl)"
proof(rule refinement_s_SeqI[where P1a="P1a \<inter> noAbrupt" and P1c="P1c \<inter> noAbrupt" and
                                   P2a="P2a \<inter> noAbrupt" and P2c="P2c \<inter> noAbrupt" and A="{}",
                             OF refines_c1 refines_c2 valid])
  from preFault show "\<And>fa. Semantic.xstate.Fault fa \<in> P1a \<inter> noAbrupt \<Longrightarrow> fa \<in> F"
    unfolding noAbrupt_def by(auto)
  show "\<And>sa. Abrupt sa \<in> P1a \<inter> noAbrupt \<Longrightarrow> sa \<in> {}"
    unfolding noAbrupt_def by(auto)
  from preNormal show "\<And>sa. Semantic.xstate.Normal sa \<in> P1a \<inter> noAbrupt \<Longrightarrow> sa \<in> P"
    unfolding noAbrupt_def by(auto)
  from propStuck show "(\<forall>xsc. xsc \<in> P1c \<inter> noAbrupt \<longrightarrow> \<not> \<Gamma>c\<turnstile> \<langle>c1c,xsc\<rangle> \<Rightarrow> Semantic.xstate.Stuck) \<or>
                       Semantic.xstate.Stuck \<in> P2c \<inter> noAbrupt"
    unfolding noAbrupt_def by(auto)
  from postFault show "\<And>fc. fl fc \<in> F \<Longrightarrow> Semantic.xstate.Fault fc \<in> P2c \<inter> noAbrupt"
    unfolding noAbrupt_def by(auto)
  show "\<And>sc. sl sc \<in> {} \<Longrightarrow> Abrupt sc \<in> P2c \<inter> noAbrupt"
    unfolding noAbrupt_def by(auto)
  from postNormal show "\<And>sc. sl sc \<in> Q \<Longrightarrow> Semantic.xstate.Normal sc \<in> P2c \<inter> noAbrupt"
    unfolding noAbrupt_def by(auto)
qed

lemma refinement_s_noStuck_noAbrupt_SeqI:
  assumes refines_c1: "((\<Gamma>a,P1a \<inter> noStuck \<inter> noAbrupt,c1a),(\<Gamma>c,P1c \<inter> noStuck \<inter> noAbrupt,c1c))
                          \<in> refinement_s (separable_lift sl fl)"
      and refines_c2: "((\<Gamma>a,P2a \<inter> noStuck \<inter> noAbrupt,c2a),(\<Gamma>c,P2c \<inter> noStuck \<inter> noAbrupt,c2c))
                          \<in> refinement_s (separable_lift sl fl)"
      and valid: "HoarePartialDef.valid \<Gamma>a F P c1a Q {}"
      and preFault: "\<And>fa. Semantic.Fault fa \<in> P1a \<Longrightarrow> fa \<in> F"
      and preNormal: "\<And>sa. Semantic.Normal sa \<in> P1a \<Longrightarrow> sa \<in> P"
      and noStuck: "\<And>xsc. xsc \<in> P1c \<Longrightarrow> xsc \<noteq> Semantic.Stuck \<Longrightarrow>
                            \<not> Semantic.exec \<Gamma>c c1c xsc Semantic.Stuck"
      and postFault: "\<And>fc. fl fc \<in> F \<Longrightarrow> Semantic.Fault fc \<in> P2c"
      and postNormal: "\<And>sc. sl sc \<in> Q \<Longrightarrow> Semantic.Normal sc \<in> P2c"
    shows "((\<Gamma>a,P1a \<inter> noStuck \<inter> noAbrupt,Language.Seq c1a c2a),
           (\<Gamma>c,P1c \<inter> noStuck \<inter> noAbrupt,Language.Seq c1c c2c))
            \<in> refinement_s (separable_lift sl fl)"
proof(rule refinement_s_noAbrupt_SeqI[where P1a="P1a \<inter> noStuck" and P1c="P1c \<inter> noStuck" and
                                            P2a="P2a \<inter> noStuck" and P2c="P2c \<inter> noStuck",
                                      OF refines_c1 refines_c2 valid])
  from preFault show "\<And>fa. Semantic.xstate.Fault fa \<in> P1a \<inter> noStuck \<Longrightarrow> fa \<in> F"
    unfolding noStuck_def by(auto)
  from preNormal show "\<And>sa. Semantic.xstate.Normal sa \<in> P1a \<inter> noStuck \<Longrightarrow> sa \<in> P"
    unfolding noStuck_def by(auto)
  from noStuck show "(\<forall>xsc. xsc \<in> P1c \<inter> noStuck \<longrightarrow> \<not> \<Gamma>c\<turnstile> \<langle>c1c,xsc\<rangle> \<Rightarrow> Semantic.xstate.Stuck) \<or>
                     Semantic.xstate.Stuck \<in> P2c \<inter> noStuck"
    unfolding noStuck_def by(auto)
  from postFault show "\<And>fc. fl fc \<in> F \<Longrightarrow> Semantic.xstate.Fault fc \<in> P2c \<inter> noStuck"
    unfolding noStuck_def by(auto)
  from postNormal show "\<And>sc. sl sc \<in> Q \<Longrightarrow> Semantic.xstate.Normal sc \<in> P2c \<inter> noStuck"
    unfolding noStuck_def by(auto)
qed

lemma refinement_s_noFault_noStuck_noAbrupt_SeqI:
  assumes refines_c1: "((\<Gamma>a,P1a \<inter> noFault \<inter> noStuck \<inter> noAbrupt,c1a),
                        (\<Gamma>c,P1c \<inter> noFault \<inter> noStuck \<inter> noAbrupt,c1c))
                          \<in> refinement_s (separable_lift sl fl)"
      and refines_c2: "((\<Gamma>a,P2a \<inter> noFault \<inter> noStuck \<inter> noAbrupt,c2a),
                        (\<Gamma>c,P2c \<inter> noFault \<inter> noStuck \<inter> noAbrupt,c2c))
                          \<in> refinement_s (separable_lift sl fl)"
      and valid: "HoarePartialDef.valid \<Gamma>a {} P c1a Q {}"
      and preNormal: "\<And>sa. Semantic.Normal sa \<in> P1a \<Longrightarrow> sa \<in> P"
      and noStuck: "\<And>xsc. xsc \<in> P1c \<Longrightarrow> xsc \<noteq> Semantic.Stuck \<Longrightarrow> \<nexists>fc. xsc = Semantic.Fault fc \<Longrightarrow>
                            \<not> Semantic.exec \<Gamma>c c1c xsc Semantic.Stuck"
      and postNormal: "\<And>sc. sl sc \<in> Q \<Longrightarrow> Semantic.Normal sc \<in> P2c"
    shows "((\<Gamma>a,P1a \<inter> noFault \<inter> noStuck \<inter> noAbrupt,Language.Seq c1a c2a),
           (\<Gamma>c,P1c \<inter> noFault \<inter> noStuck \<inter> noAbrupt,Language.Seq c1c c2c))
            \<in> refinement_s (separable_lift sl fl)"
proof(rule refinement_s_noStuck_noAbrupt_SeqI[where P1a="P1a \<inter> noFault" and P1c="P1c \<inter> noFault" and
                                                    P2a="P2a \<inter> noFault" and P2c="P2c \<inter> noFault" and
                                                    F="{}",
                                              OF refines_c1 refines_c2 valid])
  show "\<And>fa. Semantic.xstate.Fault fa \<in> P1a \<inter> noFault \<Longrightarrow> fa \<in> {}"
    unfolding noFault_def by(auto)
  from preNormal show "\<And>sa. Semantic.xstate.Normal sa \<in> P1a \<inter> noFault \<Longrightarrow> sa \<in> P"
    unfolding noFault_def by(auto)
  from noStuck show "\<And>xsc. xsc \<in> P1c \<inter> noFault \<Longrightarrow>
                           xsc \<noteq> Semantic.xstate.Stuck \<Longrightarrow>
                           \<not> \<Gamma>c\<turnstile> \<langle>c1c,xsc\<rangle> \<Rightarrow> Semantic.xstate.Stuck"
    unfolding noFault_def by(auto)
  show "\<And>fc. fl fc \<in> {} \<Longrightarrow> Semantic.xstate.Fault fc \<in> P2c \<inter> noFault"
    unfolding noFault_def by(auto)
  from postNormal show "\<And>sc. sl sc \<in> Q \<Longrightarrow> Semantic.xstate.Normal sc \<in> P2c \<inter> noFault"
    unfolding noFault_def by(auto)
qed

end