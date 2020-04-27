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
  also be related by refinement.\<close>
inductive_set refinement_s ::
  "('sa,'fa,'sc,'fc) state_rel_s \<Rightarrow> ('sa,'pa,'fa) Semantic.body \<Rightarrow> ('sc,'pc,'fc) Semantic.body \<Rightarrow>
   (('sa,'pa,'fa) Language.com \<times> ('sc,'pc,'fc) Language.com) set"
  for sr :: "(('sa,'fa) Semantic.xstate \<times> ('sc,'fc) Semantic.xstate) set"
  and \<Gamma>a :: "('sa,'pa,'fa) Semantic.body"
  and \<Gamma>c :: "('sc,'pc,'fc) Semantic.body"
  where Step:
    "(\<And>xsa xsc xsc' cc'. (xsa,xsc) \<in> sr \<and> SmallStep.step \<Gamma>c (cc,xsc) (cc',xsc') \<Longrightarrow>
      (\<exists>xsa' ca'. (xsa',xsc') \<in> sr \<and>
                  SmallStep.step \<Gamma>a (ca,xsa) (ca',xsa') \<and>
                  (ca',cc') \<in> refinement_s sr \<Gamma>a \<Gamma>c)) \<Longrightarrow>
     (ca,cc) \<in> refinement_s sr \<Gamma>a \<Gamma>c"

text \<open>An elimination rule form of the above lemma, making it easy to access an equivalent abstract
  transition in proofs.\<close>
lemma refinement_sE:
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
    by(auto elim:refinement_sE)

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

end