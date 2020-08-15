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



section \<open>Set Model Simpl proofs\<close>

text \<open>
  Due to problems importing both SIMPL and COMPLX we split the files and have all the proofs
  using SIMPL in this file
\<close>

theory CleanQ_SetModel_Simpl
(*<*)
imports 
  Main
  CleanQ_SetModel
  "../Simpl/Simpl"
begin
(*>*)


(*<*)
(* Define some global variables to make Simpl/Complex proofs work *)
record 'g CleanQ_Set_State_vars = 
  SetRB_'  :: "nat CleanQ_Set_State"
(*>*)


(* ==================================================================================== *)
subsection \<open>Integration in SIMPL\<close>
(* ==================================================================================== *)

text \<open>
  We now integrate the the CleanQ Set Model into SIMPL. For each of the two operations,
  enqueue and dequeue, we specify a Hoare-triple with pre and post conditions, and
  the operation.
\<close>


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue Operation\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We first show, that we can define a Hoare triple for the enqueue operations from both
  agents X and Y, and that in both cases the invariant is preserved.
\<close>

lemma CleanQ_Set_enq_x_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<in> SX \<acute>SetRB \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_enq_x b \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  by(vcg, simp only: CleanQ_Set_enq_x_Invariants)

lemma CleanQ_Set_enq_y_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<in> SY \<acute>SetRB \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_enq_y b \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  by(vcg, simp only: CleanQ_Set_enq_y_Invariants) 


text \<open>
  The same applies for the multi-step \verb+eneuque_n+ operation.
\<close>

lemma CleanQ_Set_enq_n_x_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> (\<forall>b \<in> B. b \<in> (SX \<acute>SetRB)) \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_enq_n_x B \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  apply(vcg) using CleanQ_Set_enq_n_x_Invariants by blast

lemma CleanQ_Set_enq_n_y_preserves_invariants : 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> (\<forall>b \<in> B. b \<in> (SY \<acute>SetRB)) \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_enq_n_y B \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  apply(vcg) using CleanQ_Set_enq_n_y_Invariants by blast



text \<open>
  The enqueue operation  happens in two steps. The buffer element is removed
  from one set and added to a new set. We can express this as two sequential operations
  in the next lemma, where we show that the invariant is still preserved and that 
  the outcome is the same, as with the definition above.
\<close>

lemma CleanQ_Set_enq_x_two_step:
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<in> SX \<acute>SetRB \<rbrace>
        \<acute>SetRB :== \<acute>SetRB \<lparr> SX := (SX \<acute>SetRB) - {b} \<rparr> ;;
        \<acute>SetRB :== \<acute>SetRB \<lparr> TXY := (TXY \<acute>SetRB) \<union> {b} \<rparr>  
      \<lbrace> \<acute>SetRB = CleanQ_Set_enq_x b rb' \<and> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  by(vcg, auto simp:CleanQ_Set_Invariants_simp CleanQ_Set_enq_x_def)
  

lemma CleanQ_Set_enq_y_two_step:
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<in> SY \<acute>SetRB \<rbrace>
        \<acute>SetRB :== \<acute>SetRB \<lparr> SY := (SY \<acute>SetRB) - {b} \<rparr> ;;
        \<acute>SetRB :== \<acute>SetRB \<lparr> TYX := (TYX \<acute>SetRB) \<union> {b} \<rparr>  
      \<lbrace> \<acute>SetRB = CleanQ_Set_enq_y b rb' \<and> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  by(vcg, auto simp:CleanQ_Set_Invariants_simp CleanQ_Set_enq_y_def)
  


text \<open>
  Next we can define this conditionally, where we only execute the enqueue operation, 
  when we are owning the buffer. 
\<close>

lemma CleanQ_Set_enq_x_conditional :
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace> 
         IF b \<in> SX \<acute>SetRB THEN 
          \<acute>SetRB :== (CleanQ_Set_enq_x b \<acute>SetRB) 
         FI 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<notin> (SX \<acute>SetRB) \<rbrace>" 
  by(vcg, auto simp:CleanQ_Set_enq_x_Invariants CleanQ_Set_enq_x_def 
                    CleanQ_Set_Invariants_simp)
  

lemma CleanQ_Set_enq_y_conditional :
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace> 
         IF b \<in> SY \<acute>SetRB THEN 
          \<acute>SetRB :== (CleanQ_Set_enq_y b \<acute>SetRB) 
         FI 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<and>  b \<notin> (SY \<acute>SetRB) \<rbrace>" 
  by(vcg, auto simp:CleanQ_Set_enq_y_Invariants CleanQ_Set_enq_y_def 
                    CleanQ_Set_Invariants_simp)



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  We first show, that we can define a Hoare triple for the dequeue operations from both
  agents X and Y, and that in both cases the invariant is preserved.
\<close>

lemma CleanQ_Set_deq_x_preserves_invariants: 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<in> TYX \<acute>SetRB \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_deq_x b \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  by(vcg, simp only: CleanQ_Set_deq_x_Invariants)

lemma CleanQ_Set_deq_y_preserves_invariants: 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<in> TXY \<acute>SetRB \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_deq_y b \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  by(vcg, simp only: CleanQ_Set_deq_y_Invariants)


text \<open>
  The same applies for the multi-step \verb+eneuque_n+ operation.
\<close>

lemma CleanQ_Set_deq_n_x_preserves_invariants: 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> (\<forall> b \<in> B. b \<in> TYX \<acute>SetRB) \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_deq_n_x B \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  apply(vcg) using CleanQ_Set_deq_n_x_Invariants by blast

lemma CleanQ_Set_deq_n_y_preserves_invariants: 
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> (\<forall> b \<in> B. b \<in> TXY \<acute>SetRB) \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_deq_n_y B \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  apply(vcg) using CleanQ_Set_deq_n_y_Invariants by blast


text \<open>
  The dequeue operation effectively happens in two steps. The buffer element is removed
  from one set and added to a new set. We can express this as two sequential operations
  in the next lemma, where we show that the invariant is still preserved and that 
  the outcome is the same, as with the definition above.
\<close>

lemma CleanQ_Set_deq_x_two_step:
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<in> TYX \<acute>SetRB \<rbrace>
        \<acute>SetRB :== \<acute>SetRB \<lparr> TYX := (TYX \<acute>SetRB) - {b} \<rparr> ;;
        \<acute>SetRB :== \<acute>SetRB \<lparr> SX := (SX \<acute>SetRB) \<union> {b} \<rparr>  
      \<lbrace> \<acute>SetRB = CleanQ_Set_deq_x b rb' \<and> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  by(vcg, simp add: CleanQ_Set_deq_x_def CleanQ_Set_Invariants_simp, auto)

lemma CleanQ_Set_deq_y_two_step:
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>SetRB \<and> CleanQ_Set_Invariants K \<acute>SetRB \<and> b \<in> TXY \<acute>SetRB \<rbrace>
        \<acute>SetRB :== \<acute>SetRB \<lparr> TXY := (TXY \<acute>SetRB) - {b} \<rparr> ;;
        \<acute>SetRB :== \<acute>SetRB \<lparr> SY := (SY \<acute>SetRB) \<union> {b} \<rparr>  
      \<lbrace> \<acute>SetRB = CleanQ_Set_deq_y b rb' \<and> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>"
  by(vcg, simp add: CleanQ_Set_deq_y_def CleanQ_Set_Invariants_simp, auto)


text \<open>
  Next we can define this conditionally, where we only execute the enqueue operation, 
  when we are owning the buffer
\<close>

lemma CleanQ_Set_deq_x_conditional:
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace> 
         IF b \<in> TYX \<acute>SetRB THEN 
          \<acute>SetRB :== (CleanQ_Set_deq_x b \<acute>SetRB) 
         FI 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>" 
  by (vcg, meson CleanQ_Set_deq_x_Invariants)

lemma CleanQ_Set_deq_y_conditional:
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace> 
         IF b \<in> TXY \<acute>SetRB THEN 
          \<acute>SetRB :== (CleanQ_Set_deq_y b \<acute>SetRB) 
         FI 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<rbrace>" 
  by (vcg, meson CleanQ_Set_deq_y_Invariants)




(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Combining Enqueue and Dequeue\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We can now combine the enqeueue and dequeue operations and pass a buffer around the 
  queue and back to the originator. We prove this by showing the state is the same.
\<close>

lemma CleanQ_Set_ops_combine : 
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<and> rb = \<acute>SetRB \<and> b \<in> SX \<acute>SetRB \<rbrace> 
        \<acute>SetRB :== (CleanQ_Set_enq_x b \<acute>SetRB) ;;
        \<acute>SetRB :== (CleanQ_Set_deq_y b \<acute>SetRB) ;;
        \<acute>SetRB :== (CleanQ_Set_enq_y b \<acute>SetRB) ;;
        \<acute>SetRB :== (CleanQ_Set_deq_x b \<acute>SetRB) 
      \<lbrace> CleanQ_Set_Invariants K \<acute>SetRB \<and> rb = \<acute>SetRB \<and> b \<in> SX \<acute>SetRB \<rbrace>" 
  apply(vcg, auto simp:CleanQ_Set_ops CleanQ_Set_Invariants_simp)
  using insert_absorb by fastforce
  
(*<*)
end
(*>*)