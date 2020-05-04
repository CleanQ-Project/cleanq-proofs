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

type_synonym ('sa,'fa,'sc,'fc) state_rel_s =
  "(('sa,'fa) Semantic.xstate \<times> ('sc,'fc) Semantic.xstate) set"

text \<open>General data refinement of abstract computation ca with context \<Gamma>a by concrete computation
  cc with context \<Gamma>c.  For any abstract state xsa and concrete state xsc in the state
  relation, if the concrete computation takes a step to a state xsc', there exists a related
  abstract state xsa', to which ca may also step, and the resulting 'next-step' computations must
  also be related by refinement.

  Moreover, the refinement may only terminate if the specification also terminates, and throws a
  fault exactly when the specification does.\<close>
inductive_set refinement_s ::
  "('sa,'fa,'sc,'fc) state_rel_s \<Rightarrow> ('sa,'pa,'fa) Semantic.body \<Rightarrow> ('sc,'pc,'fc) Semantic.body \<Rightarrow>
   (('sa,'pa,'fa) Language.com \<times> ('sc,'pc,'fc) Language.com) set"
  for sr :: "(('sa,'fa) Semantic.xstate \<times> ('sc,'fc) Semantic.xstate) set"
  and \<Gamma>a :: "('sa,'pa,'fa) Semantic.body"
  and \<Gamma>c :: "('sc,'pc,'fc) Semantic.body"
  where Step:
    "(\<And>xsa xsc xsc' cc'. (xsa,xsc) \<in> sr \<Longrightarrow> SmallStep.step \<Gamma>c (cc,xsc) (cc',xsc') \<Longrightarrow>
      (\<exists>xsa' ca'. (xsa',xsc') \<in> sr \<and>
                  SmallStep.step \<Gamma>a (ca,xsa) (ca',xsa') \<and>
                  (ca',cc') \<in> refinement_s sr \<Gamma>a \<Gamma>c)) \<Longrightarrow>
     (\<And>xsa xsc. (xsa,xsc) \<in> sr \<Longrightarrow> SmallStep.final (cc,xsc) \<Longrightarrow> SmallStep.final (ca,xsa)) \<Longrightarrow>
     (cc = Language.Throw \<longleftrightarrow> ca = Language.Throw) \<Longrightarrow>
     (ca,cc) \<in> refinement_s sr \<Gamma>a \<Gamma>c"

text \<open>An elimination rule form of the above lemma, making it easy to access an equivalent abstract
  transition in proofs.\<close>
lemma refinement_s_stepE:
    fixes sr \<Gamma>a \<Gamma>c xsa xsc xsc' ca cc cc'
  assumes refines: "(ca,cc) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
      and staterel: "(xsa,xsc) \<in> sr"
      and concrete_step: "SmallStep.step \<Gamma>c (cc,xsc) (cc',xsc')"
  obtains (abstract_step) xsa' ca'
    where "(xsa',xsc') \<in> sr"
      and "SmallStep.step \<Gamma>a (ca,xsa) (ca',xsa')"
      and "(ca',cc') \<in> refinement_s sr \<Gamma>a \<Gamma>c"
  using refines
proof(cases rule:refinement_s.cases)
  case Step
  with staterel concrete_step obtain xsa' ca'
    where "(xsa', xsc') \<in> sr"
      and "SmallStep.step \<Gamma>a (ca, xsa) (ca', xsa')"
      and "(ca',cc') \<in> refinement_s sr \<Gamma>a \<Gamma>c"
    by(blast)
  thus ?thesis by(rule abstract_step)
qed

lemma refinement_s_finalE:
    fixes sr \<Gamma>a \<Gamma>c ca cc
  assumes refines: "(ca,cc) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
      and staterel: "(xsa,xsc) \<in> sr"
      and finalc: "SmallStep.final (cc,xsc)"
    shows "SmallStep.final (ca,xsa)"
  using assms by(auto elim:refinement_s.cases)

lemma refinement_s_throwcE:
  fixes sr \<Gamma>a \<Gamma>c ca cc
  assumes refines: "(ca,cc) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
      and throw: "cc = Language.Throw"
  shows "ca = Language.Throw"
  using assms by(auto elim:refinement_s.cases)

lemma refinement_s_throwaE:
  fixes sr \<Gamma>a \<Gamma>c ca cc
  assumes refines: "(ca,cc) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
      and throw: "ca = Language.Throw"
  shows "cc = Language.Throw"
  using assms by(auto elim:refinement_s.cases)

lemma refinement_steps:
    fixes sr \<Gamma>a \<Gamma>c xsa xsc ca cc Ec
  assumes refines: "(ca,cc) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
      and staterel: "(xsa,xsc) \<in> sr"
      and concrete_steps: "(rtranclp (SmallStep.step \<Gamma>c)) (cc,xsc) Ec"
    shows "\<exists>Ea. (snd Ea,snd Ec) \<in> sr \<and> (fst Ea,fst Ec) \<in> refinement_s sr \<Gamma>a \<Gamma>c \<and>
                      (rtranclp (SmallStep.step \<Gamma>a)) (ca,xsa) Ea"
  using concrete_steps
proof(induct Ec rule:rtranclp_induct)
  case base
  with refines staterel
  have "(snd (ca,xsa), snd (cc,xsc)) \<in> sr"
   and "(fst (ca,xsa), fst (cc,xsc)) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
   and "(rtranclp (SmallStep.step \<Gamma>a)) (ca,xsa) (ca,xsa)"
    by(auto)
  then show ?case by(blast)

next
  case (step Dc Ec)
  then obtain Da
    where srD: "(snd Da, snd Dc) \<in> sr"
      and rD: "(fst Da, fst Dc) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
      and stepsDa: "(rtranclp (SmallStep.step \<Gamma>a)) (ca, xsa) Da"
    by(blast)

  from step(2) have step_Dc: "SmallStep.step \<Gamma>c (fst Dc, snd Dc) (fst Ec, snd Ec)" by(simp)
  
  obtain xsa' ca'
    where srE: "(xsa',snd Ec) \<in> sr"
      and step_Da: "SmallStep.step \<Gamma>a Da (ca',xsa')"
      and rD: "(ca',fst Ec) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
    by(auto intro:refinement_s_stepE[OF rD srD step_Dc])

  note stepsDa
  also note step_Da
  finally have "(rtranclp (SmallStep.step \<Gamma>a)) (ca, xsa) (ca',xsa')" .
  with srE rD show ?case by(auto)
qed

lemma refinement_s_stepsE:
    fixes sr \<Gamma>a \<Gamma>c xsa xsc ca cc Ec
  assumes refines: "(ca,cc) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
      and staterel: "(xsa,xsc) \<in> sr"
      and concrete_steps: "(rtranclp (SmallStep.step \<Gamma>c)) (cc,xsc) (cc',xsc')"
  obtains (abstract_steps) ca' xsa'
    where "(xsa',xsc') \<in> sr"
      and "(ca',cc') \<in> refinement_s sr \<Gamma>a \<Gamma>c"
      and "(rtranclp (SmallStep.step \<Gamma>a)) (ca,xsa) (ca',xsa')"
proof -
  from refinement_steps[OF assms] obtain Ea
    where "(snd Ea, snd (cc', xsc')) \<in> sr"
      and "(fst Ea, fst (cc', xsc')) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
          "(rtranclp (SmallStep.step \<Gamma>a)) (ca, xsa) Ea"
    by(blast)
  moreover obtain ca' xsa'
    where "Ea = (ca', xsa')" by(cases Ea, auto)
  ultimately show ?thesis
    by(auto dest:abstract_steps)
qed

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
  "('sa,'fa,'sc,'fc) state_rel_s \<Rightarrow> ('sa,'pa,'fa) Semantic.body \<Rightarrow> ('sc,'pc,'fc) Semantic.body \<Rightarrow>
   ('sa,'pa,'fa) trace_s \<Rightarrow> ('sc,'pc,'fc) trace_s \<Rightarrow> bool"
  for sr :: "('sa,'fa,'sc,'fc) state_rel_s"
  and \<Gamma>a :: "('sa,'pa,'fa) Semantic.body"
  and \<Gamma>c :: "('sc,'pc,'fc) Semantic.body"
  where
    Start: "trace_refines_s sr \<Gamma>a \<Gamma>c [] []" |
    Step:  "trace_refines_s sr \<Gamma>a \<Gamma>c Ta Tc \<Longrightarrow> (xsa,xsc) \<in> sr \<Longrightarrow>
              (ca,cc) \<in> refinement_s sr \<Gamma>a \<Gamma>c \<Longrightarrow>
              trace_refines_s sr \<Gamma>a \<Gamma>c ((ca,xsa)#Ta) ((cc,xsc)#Tc)"

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

text \<open>If cc refines ca, then for any trace of cc beginning in a state which has an abstract
  equivalent, there exists a corresponding abstract trace of which the concrete trace is a
  refinement, in the sense defined above i.e. program refinement implies trace refinement.\<close>
lemma trace_refinement_s:
  fixes Tc \<Gamma>a \<Gamma>c ca cc sr
  assumes refines: "(ca,cc) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
      and concrete_trace: "Tc \<in> finite_traces_s \<Gamma>c cc"
      and initial_a: "\<exists>xsa. (xsa, snd (last Tc)) \<in> sr"
    shows "\<exists>Ta. Ta \<in> finite_traces_s \<Gamma>a ca \<and> trace_refines_s sr \<Gamma>a \<Gamma>c Ta Tc"
  using finite_trace_nonempty_s[OF concrete_trace] concrete_trace initial_a
  text \<open>There are no empty traces.\<close>
proof(induct Tc rule:list_nonempty_induct)
  case (single E)
  text \<open>For the singleton trace (just the starting state), we only need pick some corresponding
    abstract state to form the abstract trace (we can start in any state, whether or not there are
    transitions out of it).\<close>
  then obtain xsa_i where "(xsa_i, snd E) \<in> sr" by(auto)
  moreover from single(1) refines have "(ca,fst E) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
    by(cases rule:finite_traces_s.cases, simp)
  moreover note trace_refines_s.Start
  ultimately have "trace_refines_s sr \<Gamma>a \<Gamma>c [(ca,xsa_i)] [(fst E, snd E)]"
    by(blast intro:trace_refines_s.Step)
  with finite_traces_s.Start show ?case by(auto)

next
  case (cons Ec Tc)
  hence ne_Tc: "Tc \<noteq> []" by(blast)

  text \<open>Find the abstract initial state corresponding to the concrete initial state.\<close>
  from cons have ext_concrete_trace: "Ec # Tc \<in> finite_traces_s \<Gamma>c cc" by(blast)
  hence "Tc \<in> finite_traces_s \<Gamma>c cc"
    by(cases rule:finite_traces_s.cases, insert ne_Tc, auto)
  moreover from cons obtain xsa_i
    where "(xsa_i, snd (last Tc)) \<in> sr" by(auto)
  text \<open>Then by the inductive hypothesis we have a matching trace up to step n-1.\<close>
  ultimately obtain Ta
    where abstract_trace: "Ta \<in> finite_traces_s \<Gamma>a ca"
      and IH: "trace_refines_s sr \<Gamma>a \<Gamma>c Ta Tc"
    by(auto dest:cons(2))

  text \<open>The traces are the same length.\<close>
  from IH have ne_Ta: "Ta \<noteq> []"
    by(cases rule:trace_refines_s.cases, insert ne_Tc, auto)

  text \<open>As they're non-empty, we can take the last element of the abstract trace, and the last two
    elements of the concrete trace (as it's been extended).\<close>
  obtain cc2 xsc2 where rw_Ec: "Ec = (cc2,xsc2)" by(cases Ec, auto)
  from ne_Tc obtain cc1 xsc1 Tc' where rw_Tc: "Tc = (cc1,xsc1) # Tc'" by(cases Tc, auto)
  from ne_Ta obtain ca1 xsa1 Ta' where rw_Ta: "Ta = (ca1,xsa1) # Ta'" by(cases Ta, auto)

  text \<open>Now we can use refinement to find an abstract transition corresponding to the cc1->cc2
    concrete transition.\<close>
  from rw_Ec rw_Tc ne_Tc
  have "SmallStep.step \<Gamma>c (cc1,xsc1) (cc2,xsc2)"
    by(cases rule:finite_traces_s.cases[OF ext_concrete_trace], auto)
  moreover from IH ne_Ta rw_Ta rw_Tc
  have "(xsa1,xsc1) \<in> sr"
    by(cases rule:trace_refines_s.cases, auto)
  moreover from IH ne_Ta rw_Ta rw_Tc
  have "(ca1, cc1) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
    by(cases rule:trace_refines_s.cases, auto)
  ultimately obtain xsa2 ca2
    where sr_step: "(xsa2, xsc2) \<in> sr"
      and abstract_step: "SmallStep.step \<Gamma>a (ca1, xsa1) (ca2, xsa2)"
      and refine_step: "(ca2, cc2) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
    by(auto elim:refinement_s_stepE)

  text \<open>The new abstract state corresponds in exactly the way that trace refinement demands.\<close>
  from abstract_trace abstract_step
  have "(ca2,xsa2) # Ta \<in> finite_traces_s \<Gamma>a ca"
    unfolding rw_Ta by(rule finite_traces_s.Step)
  moreover from IH sr_step refine_step
  have "trace_refines_s sr \<Gamma>a \<Gamma>c ((ca2, xsa2)#Ta) (Ec # Tc)"
    unfolding rw_Ec by(rule trace_refines_s.Step)
  ultimately show ?case by(blast)
qed

text \<open>Elimination form of the above, for getting one's grubby little hands on an abstract trace.\<close>
lemma trace_refinement_sE:
    fixes Tc \<Gamma>a \<Gamma>c ca cc sr
  assumes refines: "(ca,cc) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
      and concrete_trace: "Tc \<in> finite_traces_s \<Gamma>c cc"
      and initial_a: "\<exists>xsa. (xsa, snd (last Tc)) \<in> sr"
  obtains (abstract_trace) Ta
    where "Ta \<in> finite_traces_s \<Gamma>a ca"
      and "trace_refines_s sr \<Gamma>a \<Gamma>c Ta Tc"
  using trace_refinement_s[OF assms] by(blast)

text \<open>A mode-preserving state relation only relates Normal-Normal etc.\<close>
definition
  mode_preserving :: "('sa,'fa,'sc,'fc) state_rel_s \<Rightarrow> bool"
where
  "mode_preserving sr \<longleftrightarrow> (\<forall>xsa xsc. (xsa,xsc) \<in> sr \<longrightarrow>
    (((\<exists>sa. xsa = Semantic.Normal sa) \<longleftrightarrow> (\<exists>sc. xsc = Semantic.Normal sc)) \<and>
     ((\<exists>sa. xsa = Semantic.Abrupt sa) \<longleftrightarrow> (\<exists>sc. xsc = Semantic.Abrupt sc)) \<and>
     ((\<exists>fa. xsa = Semantic.Fault fa) \<longleftrightarrow> (\<exists>fc. xsc = Semantic.Fault fc)) \<and>
     (xsa = Semantic.Stuck \<longleftrightarrow> xsc = Semantic.Stuck)))"

definition
  separable_sr :: "('sa \<times> 'sc) set \<Rightarrow> ('fa \<times> 'fc) set \<Rightarrow> ('sa,'fa,'sc,'fc) state_rel_s"
where
  "separable_sr sr fr = {(Semantic.Stuck, Semantic.Stuck)}
    \<union> ((\<lambda>(sa,sc). (Semantic.Normal sa, Semantic.Normal sc)) ` sr)
    \<union> ((\<lambda>(sa,sc). (Semantic.Abrupt sa, Semantic.Abrupt sc)) ` sr)
    \<union> ((\<lambda>(fa,fc). (Semantic.Fault fa, Semantic.Fault fc)) ` fr)"

(* XXX - move *)
lemma final_s_cases:
  assumes "SmallStep.final cfg"
  obtains
    (Skip) xs where "cfg = (Language.Skip, xs)"
  | (Throw) s where "cfg = (Language.Throw, Semantic.Normal s)"
  using assms unfolding SmallStep.final_def by(cases cfg, auto)

definition no_spontaneous_abrupt :: "('sa,'fa,'sc,'fc) state_rel_s \<Rightarrow> bool"
  where "no_spontaneous_abrupt sr \<longleftrightarrow> (\<forall>xsa xsc.
          (xsa,xsc) \<in> sr \<longrightarrow> (\<exists>sc. xsc = Semantic.Abrupt sc) \<longrightarrow> (\<exists>sa. xsa = Semantic.Abrupt sa)
        )"

definition faults_preserved :: "('sa,'fa,'sc,'fc) state_rel_s \<Rightarrow> bool"
  where "faults_preserved sr \<longleftrightarrow> (\<forall>xsa xsc.
          (xsa,xsc) \<in> sr \<longrightarrow> (\<exists>fa. xsa = Semantic.Fault fa) \<longrightarrow> (\<exists>fc. xsc = Semantic.Fault fc)
        )"

definition abrupt_closed :: "('sa,'fa,'sc,'fc) state_rel_s \<Rightarrow> bool"
  where "abrupt_closed sr \<longleftrightarrow> (\<forall>sa sc.
          (Semantic.Normal sa, Semantic.Normal sc) \<in> sr \<longrightarrow>
          (Semantic.Abrupt sa, Semantic.Abrupt sc) \<in> sr
        )"

definition wf_sr :: "('sa,'fa,'sc,'fc) state_rel_s \<Rightarrow> bool"
  where "wf_sr sr \<longleftrightarrow> no_spontaneous_abrupt sr \<and> abrupt_closed sr \<and> faults_preserved sr"

lemma wf_sr_nsaE:
  fixes sr xsa sc
  assumes "wf_sr sr" and "(xsa, Semantic.Abrupt sc) \<in> sr"
  obtains sa where "xsa = Semantic.Abrupt sa"
  using assms unfolding wf_sr_def no_spontaneous_abrupt_def by(auto)

lemma wf_sr_fpE:
  fixes sr fa xsc
  assumes "wf_sr sr" and "(Semantic.Fault fa, xsc) \<in> sr"
  obtains fc where "xsc = Semantic.Fault fc"
  using assms unfolding wf_sr_def faults_preserved_def by(auto)

lemma wf_sr_acE:
  fixes sr sa sc
  assumes "wf_sr sr" and "(Semantic.Normal sa, Semantic.Normal sc) \<in> sr"
  shows "(Semantic.Abrupt sa, Semantic.Abrupt sc) \<in> sr"
  using assms unfolding wf_sr_def abrupt_closed_def by(auto)

lemma separable_sr_wf:
  "wf_sr (separable_sr sr fr)"
  unfolding wf_sr_def no_spontaneous_abrupt_def abrupt_closed_def separable_sr_def
            faults_preserved_def
  by(auto)

lemma refinement_exec_s:
    fixes ca cc sr \<Gamma>a \<Gamma>c xsa xsc xsc'
  assumes refines: "(ca,cc) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
      and bigstepc: "Semantic.exec \<Gamma>c cc xsc xsc'"
      and sr: "(xsa,xsc) \<in> sr"
      and wf_sr: "wf_sr sr"
    shows "\<exists>xsa'. Semantic.exec \<Gamma>a ca xsa xsa' \<and> (xsa',xsc') \<in> sr"
proof(cases "isAbr xsc'")
  case True
  then obtain sc where rw_xsc': "xsc' = Semantic.Abrupt sc" by(auto elim:isAbrE)

  show ?thesis
  proof(cases "xsc = xsc'")
    case True
    with rw_xsc' exec_impl_steps[OF bigstepc]
    have stepsc: "(rtranclp (SmallStep.step \<Gamma>c)) (cc,xsc) (Language.Skip,xsc)"
      by(auto)

    obtain ca' xsa'
      where sr': "(xsa', xsc) \<in> sr"
        and refines': "(ca', Language.Skip) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
        and bigstepa: "(rtranclp (SmallStep.step \<Gamma>a)) (ca, xsa) (ca', xsa')"
      by(auto intro:refinement_s_stepsE[OF refines sr stepsc])

    have "SmallStep.final (Language.Skip,xsc)"
      unfolding SmallStep.final_def by(auto)
    with sr' refines' have finala: "SmallStep.final (ca',xsa')"
      by(auto elim:refinement_s_finalE)

    from finala show ?thesis
    proof(cases rule:final_s_cases)
      case (Skip xs)
      with bigstepa sr' True show ?thesis
        by(auto intro:steps_Skip_impl_exec)

    next
      case (Throw sa)
      with wf_sr True rw_xsc' sr' show ?thesis
        by(auto elim:wf_sr_nsaE)
    qed

  next
    case False
    with rw_xsc' exec_impl_steps[OF bigstepc]
    have stepsc: "(rtranclp (SmallStep.step \<Gamma>c)) (cc,xsc) (Language.Throw, Semantic.Normal sc)"
      by(auto)

    obtain ca' xsa'
      where sr': "(xsa', Semantic.Normal sc) \<in> sr"
        and refines': "(ca', Language.Throw) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
        and bigstepa: "(rtranclp (SmallStep.step \<Gamma>a)) (ca, xsa) (ca', xsa')"
      by(auto intro:refinement_s_stepsE[OF refines sr stepsc])

    have "SmallStep.final (Language.Throw, Semantic.Normal sc)"
      unfolding SmallStep.final_def by(auto)
    with sr' refines' have finala: "SmallStep.final (ca',xsa')"
      by(auto elim:refinement_s_finalE)

    from finala show ?thesis
    proof(cases rule:final_s_cases)
      case (Skip xs)
      with refines' show ?thesis by(auto dest:refinement_s_throwcE)
    next
      case (Throw sa)
      with bigstepa have "Semantic.exec \<Gamma>a ca xsa (Semantic.Abrupt sa)"
        by(auto intro:steps_Throw_impl_exec)
      moreover {
        from Throw sr' have "(Semantic.Normal sa, Semantic.Normal sc) \<in> sr"
          by(simp)
        with wf_sr have "(Semantic.Abrupt sa, Semantic.Abrupt sc) \<in> sr"
          by(auto elim:wf_sr_acE)
        with rw_xsc' have "(Semantic.Abrupt sa, xsc') \<in> sr" by(simp)
      }
      ultimately show ?thesis by(blast)
    qed
  qed
next
  case False
  with exec_impl_steps[OF bigstepc]
  have stepsc: "(rtranclp (SmallStep.step \<Gamma>c)) (cc,xsc) (Language.Skip,xsc')"
    unfolding isAbr_def by(cases xsc', auto)

  obtain ca' xsa'
    where sr': "(xsa', xsc') \<in> sr"
      and refines': "(ca', Language.Skip) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
      and bigstepa: "(rtranclp (SmallStep.step \<Gamma>a)) (ca, xsa) (ca', xsa')"
    by(auto intro:refinement_s_stepsE[OF refines sr stepsc])

  have "SmallStep.final (Language.Skip, xsc')"
    unfolding SmallStep.final_def by(auto)
  with sr' refines' have finala: "SmallStep.final (ca',xsa')"
    by(auto elim:refinement_s_finalE)

  from finala show ?thesis
  proof(cases rule:final_s_cases)
    case (Skip xs)
    with bigstepa have "Semantic.exec \<Gamma>a ca xsa xsa'"
      by(auto intro:steps_Skip_impl_exec)
    with sr' show ?thesis by(blast)
  next
    case (Throw sa)
    with refines' show ?thesis by(auto dest:refinement_s_throwaE)
  qed
qed

lemma refinement_exec_sE:
    fixes ca cc sr \<Gamma>a \<Gamma>c xsa xsc xsc'
  assumes refines: "(ca,cc) \<in> refinement_s sr \<Gamma>a \<Gamma>c"
      and bigstepc: "Semantic.exec \<Gamma>c cc xsc xsc'"
      and sr: "(xsa,xsc) \<in> sr"
      and wf_sr: "wf_sr sr"
  obtains xsa' where "Semantic.exec \<Gamma>a ca xsa xsa'" and "(xsa',xsc') \<in> sr"
  using refinement_exec_s[OF assms] by(blast)

lemma valid_sE:
  fixes \<Gamma> F P c Q A s t
  assumes valid: "HoarePartialDef.valid \<Gamma> F P c Q A" 
      and exec: "Semantic.exec \<Gamma> c s t"
      and pre: "s \<in> Semantic.Normal ` P"
      and nofault: "t \<notin> Semantic.Fault ` F"
    obtains (Normal) "t \<in> Semantic.Normal ` Q" | (Abrupt) "t \<in> Semantic.Abrupt ` A"
  using assms unfolding HoarePartialDef.valid_def by(blast)

lemma exec_steps_cases:
  fixes \<Gamma> c s t
  assumes exec: "Semantic.exec \<Gamma> c s t"
  obtains (Prop_Abr) x
    where "(rtranclp (SmallStep.step \<Gamma>)) (c,s) (Language.Skip,t)"
      and "s = t" and "t = Semantic.Abrupt x"
        | (Throw_Abr) x
    where "(rtranclp (SmallStep.step \<Gamma>)) (c,s) (Language.Throw,Semantic.Normal x)"
      and "s \<noteq> t" and "t = Semantic.Abrupt x"
    | (Normal) "(rtranclp (SmallStep.step \<Gamma>)) (c,s) (Language.Skip,t)" and "\<not>isAbr t"
proof(cases "isAbr t")
  case True
  then obtain x where rw_t: "t = Semantic.Abrupt x" by(cases t, auto)

  show ?thesis
  proof(cases "s = t")
    case True
    with rw_t exec_impl_steps[OF exec]
    have "(rtranclp (SmallStep.step \<Gamma>)) (c,s) (Language.Skip,t)" by(auto)
    from Prop_Abr[OF this True rw_t] show ?thesis .
  next
    case False
    with rw_t exec_impl_steps[OF exec]
    have "(rtranclp (SmallStep.step \<Gamma>)) (c,s) (Language.Throw,Semantic.Normal x)" by(auto)
    from Throw_Abr[OF this False rw_t] show ?thesis .
  qed
next
  case False
  with exec_impl_steps[OF exec]
  have "(rtranclp (SmallStep.step \<Gamma>)) (c,s) (Language.Skip,t)" by(cases t, auto)
  from Normal[OF this False] show ?thesis .
qed     

text \<open>Refinement preserves (partial) Hoare triples\<close>
lemma refinement_valid_s:
    fixes ca cc sr fr \<Gamma>a \<Gamma>c F P Q A
  assumes refines: "(ca,cc) \<in> refinement_s (separable_sr sr fr) \<Gamma>a \<Gamma>c"
      and valida: "HoarePartialDef.valid \<Gamma>a F P ca Q A"
    shows "HoarePartialDef.valid \<Gamma>c (fr``F) (sr``P) cc (sr``Q) (sr``A)"
proof(rule HoarePartialDef.validI)
  fix sc xsc'
  assume execc: "Semantic.exec \<Gamma>c cc (Semantic.Normal sc) xsc'"
     and imgP: "sc \<in> sr `` P"
     and noF: "xsc' \<notin> Semantic.xstate.Fault ` fr `` F"

  from imgP obtain sa
    where saP: "sa \<in> P"
      and sr: "(sa,sc) \<in> sr"
    by(auto)

  from sr have "(Semantic.Normal sa, Semantic.Normal sc) \<in> separable_sr sr fr"
    unfolding separable_sr_def by(auto)
  with execc refines separable_sr_wf obtain xsa'
    where execa: "Semantic.exec \<Gamma>a ca (Semantic.Normal sa) xsa'"
      and xsr': "(xsa',xsc') \<in> separable_sr sr fr"
    by(auto elim!:refinement_exec_sE) (* XXX order of prems. *)

  note valida execa
  moreover from saP have "Semantic.Normal sa \<in> Semantic.Normal ` P"
    by(simp)
  moreover from noF have "xsa' \<notin> Semantic.Fault ` F"
  proof(rule contrapos_nn)
    assume "xsa' \<in> Semantic.Fault ` F"
    then obtain fa
      where rw_xsa': "xsa' = Semantic.Fault fa"
      and faF: "fa \<in> F"
      by(auto)

    from wf_sr_fpE[OF separable_sr_wf xsr'[unfolded rw_xsa']]
    obtain fc where rw_xsc': "xsc' = Semantic.Fault fc" by(blast)

    from faF rw_xsa' rw_xsc' xsr'
    have "fc \<in> fr `` F"
      unfolding separable_sr_def by(auto)
    with rw_xsc' show "xsc' \<in> Semantic.Fault ` fr `` F"
      by(auto)
  qed
  ultimately show "xsc' \<in> Semantic.Normal ` sr `` Q \<union> Semantic.Abrupt ` sr `` A"
  proof(cases rule:valid_sE)
    case Normal
    then obtain sa'
      where "xsa' = Semantic.Normal sa'" and "sa' \<in> Q"
      by(auto)
    with xsr' have "xsc' \<in> Semantic.xstate.Normal ` sr `` Q"
      unfolding separable_sr_def by(auto)
    thus ?thesis by(auto)
  next
    case Abrupt
    then obtain sa'
      where "xsa' = Semantic.Abrupt sa'" and "sa' \<in> A"
      by(auto)
    with xsr' have "xsc' \<in> Semantic.xstate.Abrupt ` sr `` A"
      unfolding separable_sr_def by(auto)
    thus ?thesis by(auto)
  qed
qed

text \<open>Refinement composes transitively.\<close>
lemma refinement_s_trans:
  "refinement_s srab \<Gamma>a \<Gamma>b O refinement_s srbc \<Gamma>b \<Gamma>c \<subseteq> refinement_s (srab O srbc) \<Gamma>a \<Gamma>c"
proof
  fix x
  assume "x \<in> refinement_s srab \<Gamma>a \<Gamma>b O refinement_s srbc \<Gamma>b \<Gamma>c"
  then obtain ca cc
    where "(ca,cc) \<in> refinement_s srab \<Gamma>a \<Gamma>b O refinement_s srbc \<Gamma>b \<Gamma>c"
      and rw_x: "x = (ca,cc)"
    by(cases x, auto)
  then obtain cb
    where refines_ab: "(ca,cb) \<in> refinement_s srab \<Gamma>a \<Gamma>b"
      and refines_bc: "(cb,cc) \<in> refinement_s srbc \<Gamma>b \<Gamma>c"
    by(auto)

  from refines_bc refines_ab
  show "x \<in> refinement_s (srab O srbc) \<Gamma>a \<Gamma>c"
    unfolding rw_x
  proof(induct cb cc arbitrary: ca rule:refinement_s.induct[case_names Step_c])
    case (Step_c cc cb)

    show ?case
    proof(rule refinement_s.Step)
      fix xsa xsc xsc' cc'
      assume "(xsa, xsc) \<in> srab O srbc"
      then obtain xsb
        where sr_ab: "(xsa,xsb) \<in> srab"
          and sr_bc: "(xsb,xsc) \<in> srbc"
        by(auto)

      assume step_c: "SmallStep.step \<Gamma>c (cc, xsc) (cc', xsc')"
      from Step_c.hyps(1)[OF sr_bc step_c]
      obtain xsb' cb'
        where sr_bc': "(xsb', xsc') \<in> srbc"
          and step_b: "SmallStep.step \<Gamma>b (cb,xsb) (cb',xsb')"
          and refines_bc': "(cb',cc') \<in> refinement_s srbc \<Gamma>b \<Gamma>c"
          and IH: "\<And>ca'. (ca',cb') \<in> refinement_s srab \<Gamma>a \<Gamma>b \<Longrightarrow>
                          (ca',cc') \<in> refinement_s (srab O srbc) \<Gamma>a \<Gamma>c"
        by(blast)

      from Step_c.prems sr_ab step_b
      obtain xsa' ca'
        where sr_ab': "(xsa',xsb') \<in> srab"
          and step_a: "SmallStep.step \<Gamma>a (ca,xsa) (ca',xsa')"
          and refines_ab': "(ca',cb') \<in> refinement_s srab \<Gamma>a \<Gamma>b"
        by(blast elim:refinement_s_stepE)

      from sr_ab' sr_bc'
      have "(xsa', xsc') \<in> srab O srbc"
        by(auto)
      moreover note step_a
      moreover from refines_ab'
      have "(ca', cc') \<in> refinement_s (srab O srbc) \<Gamma>a \<Gamma>c"
        by(rule IH)
      ultimately show "\<exists>xsa' ca'. (xsa', xsc') \<in> srab O srbc \<and>
                                  SmallStep.step \<Gamma>a (ca, xsa) (ca', xsa') \<and>
                                  (ca', cc') \<in> refinement_s (srab O srbc) \<Gamma>a \<Gamma>c"
        by(blast)
    next
      from Step_c.hyps have "(cc = Language.Throw) = (cb = Language.Throw)"
        by(auto)
      also from Step_c.prems have "... = (ca = Language.Throw)"
        by(auto elim:refinement_s_throwaE refinement_s_throwcE)
      finally show "(cc = Language.Throw) = (ca = Language.Throw)" .
    next
      fix xsa xsc
      assume sr_ac: "(xsa, xsc) \<in> srab O srbc"
         and final_c: "SmallStep.final (cc, xsc)"

      from sr_ac obtain xsb
        where sr_ab: "(xsa, xsb) \<in> srab"
          and sr_bc: "(xsb, xsc) \<in> srbc"
        by(auto)

      from final_c sr_bc Step_c.hyps have "SmallStep.final (cb, xsb)"
        by(blast)
      with sr_ab Step_c.prems show "SmallStep.final (ca, xsa)"
        by(auto elim:refinement_s_finalE)
    qed
  qed
qed

lemma refinement_s_SkipI:
  shows "(Language.Skip, Language.Skip) \<in> refinement_s xsr \<Gamma>a \<Gamma>c"
proof(rule refinement_s.Step)
  show "(SKIP = THROW) = (SKIP = THROW)" by(auto)
next
  fix xsa
  show "SmallStep.final (SKIP, xsa)"
    unfolding SmallStep.final_def by(simp)
next
  fix xsa xsc xsc' cc'
  assume stepc: "SmallStep.step \<Gamma>c(Language.com.Skip, xsc) (cc', xsc')"
  thus "\<exists>xsa' ca'.
          (xsa', xsc') \<in> xsr \<and>
          SmallStep.step \<Gamma>a (Language.com.Skip, xsa) (ca', xsa') \<and>
          (ca', cc') \<in> refinement_s xsr \<Gamma>a \<Gamma>c"
    by(blast elim:SmallStep.step.cases)
qed

lemma refinement_s_BasicI:
  assumes fun_rel: "\<And>sa sc. (sa,sc) \<in> sr \<Longrightarrow> (f sa, g sc) \<in> sr"
  shows "(Language.Basic f, Language.Basic g) \<in> refinement_s (separable_sr sr fr) \<Gamma>a \<Gamma>c"
proof(rule refinement_s.Step)
  show "(Language.com.Basic g = THROW) = (Language.com.Basic f = THROW)"
    by(auto)
next
  fix xsa xsc
  assume "SmallStep.final (Language.com.Basic g, xsc)"
  thus "SmallStep.final (Language.com.Basic f, xsa)"
    unfolding SmallStep.final_def by(auto)
next
  fix xsa xsc xsc' cc'
  assume sr: "(xsa, xsc) \<in> separable_sr sr fr"
     and stepc: "SmallStep.step \<Gamma>c(Language.com.Basic g, xsc) (cc', xsc')"

  show "\<exists>xsa' ca'.
          (xsa', xsc') \<in> separable_sr sr fr \<and>
          SmallStep.step \<Gamma>a (Language.com.Basic f, xsa) (ca', xsa') \<and>
          (ca', cc') \<in> refinement_s (separable_sr sr fr) \<Gamma>a \<Gamma>c"
  proof(cases xsc)
    case (Normal sc)
    with sr obtain sa where rw_xsa: "xsa = Semantic.Normal sa"
      unfolding separable_sr_def by(auto)

    from Normal stepc
    have rw_cc': "cc' = Language.Skip" and rw_xsc': "xsc' = Semantic.Normal (g sc)"
      by(auto elim:SmallStep.step.cases)

    from sr have "(sa,sc) \<in> sr"
      unfolding rw_xsa Normal separable_sr_def by(auto)
    hence "(Semantic.Normal (f sa), xsc') \<in> separable_sr sr fr"
      unfolding separable_sr_def rw_xsc' by(auto elim:fun_rel)
    moreover have "SmallStep.step \<Gamma>a (Language.Basic f, xsa) (Language.Skip, Semantic.Normal (f sa))"
      unfolding rw_xsa by(rule SmallStep.step.Basic)
    moreover have "(Language.Skip, cc') \<in> refinement_s (separable_sr sr fr) \<Gamma>a \<Gamma>c"
      unfolding rw_cc' by(rule refinement_s_SkipI)
    ultimately show ?thesis by(blast)

  next
    case (Abrupt sc)
    with sr obtain sa where rw_xsa: "xsa = Semantic.Abrupt sa"
      unfolding separable_sr_def by(auto)

    from Abrupt stepc
    have rw_cc': "cc' = Language.Skip" and rw_xsc': "xsc' = Semantic.Abrupt sc"
      by(auto elim:SmallStep.step.cases)

    from sr Abrupt rw_xsc'
    have "(Semantic.Abrupt sa,xsc') \<in> separable_sr sr fr" by(simp add:rw_xsa)
    moreover have "SmallStep.step \<Gamma>a (Language.Basic f, xsa) (Language.Skip, Semantic.Abrupt sa)"
      unfolding rw_xsa by(auto intro: SmallStep.step.AbruptProp)
    moreover have "(Language.Skip, cc') \<in> refinement_s (separable_sr sr fr) \<Gamma>a \<Gamma>c"
      unfolding rw_cc' by(rule refinement_s_SkipI)
    ultimately show ?thesis by(blast)

  next
    case (Fault fc)
    with sr obtain fa where rw_xsa: "xsa = Semantic.Fault fa"
      unfolding separable_sr_def by(auto)

    from Fault stepc
    have rw_cc': "cc' = Language.Skip" and rw_xsc': "xsc' = Semantic.Fault fc"
      by(auto elim:SmallStep.step.cases)

    from sr Fault rw_xsc'
    have "(Semantic.Fault fa,xsc') \<in> separable_sr sr fr" by(simp add:rw_xsa)
    moreover have "SmallStep.step \<Gamma>a (Language.Basic f, xsa) (Language.Skip, Semantic.Fault fa)"
      unfolding rw_xsa by(auto intro: SmallStep.step.FaultProp)
    moreover have "(Language.Skip, cc') \<in> refinement_s (separable_sr sr fr) \<Gamma>a \<Gamma>c"
      unfolding rw_cc' by(rule refinement_s_SkipI)
    ultimately show ?thesis by(blast)

  next
    case Stuck
    with sr have rw_xsa: "xsa = Semantic.Stuck"
      unfolding separable_sr_def by(auto)

    from Stuck stepc
    have rw_cc': "cc' = Language.Skip" and rw_xsc': "xsc' = Semantic.Stuck"
      by(auto elim:SmallStep.step.cases)

    from sr Stuck rw_xsc'
    have "(Semantic.Stuck,xsc') \<in> separable_sr sr fr" by(simp add:rw_xsa)
    moreover have "SmallStep.step \<Gamma>a (Language.Basic f, xsa) (Language.Skip, Semantic.Stuck)"
      unfolding rw_xsa by(auto intro: SmallStep.step.StuckProp)
    moreover have "(Language.Skip, cc') \<in> refinement_s (separable_sr sr fr) \<Gamma>a \<Gamma>c"
      unfolding rw_cc' by(rule refinement_s_SkipI)
    ultimately show ?thesis by(blast)
  qed
qed

end