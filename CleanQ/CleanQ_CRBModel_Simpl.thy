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



section \<open>CleanQ Abstract Concurrent Ring Buffer Model\<close>

text \<open>
  This model is the concurrent version of the ring buffer. The \verb+enqueue+ and \verb+deqeue+
  operations are executed in two steps and the frame condition needs to be relaxed in order
  to allow the "other" side to take concurrent actions. 
\<close>

theory CleanQ_CRBModel_Simpl
(*<*) 
  imports CleanQ_CRBModel
          "../Simpl/Vcg"
(*>*)  
begin

(* ==================================================================================== *)
subsection \<open>CleanQ Abstract Concurrent Ring Buffer Model State\<close>
(* ==================================================================================== *)

text \<open>
  the model is exactly the same and we reuse the RB Model. 
\<close>

(*<*)
(* Define some global variables to make Simpl/Complex proofs work *)
record 'g CleanQ_CRB_State_vars = 
  RingCRB_'  :: "nat CleanQ_RB_State"
  b_' :: "nat"
(*>*)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Pre-Post Conditions for the Enqueue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  We now define the hoare triples for the enqueue operation. Those are needed to later
  for the interference proof. There are a total of three predicates for the enqueue
  operation in small step semantics, while the predicates P and R define the big 
  step semantics.

  \verb+{P} write_head {Q} incr_head {R}+ 

  We now provide abbreviations for each of the predicate P, Q, and R for the \verb+enqueue+
  operation as seen from Y and X.   
\<close>

paragraph \<open>Enqueue P\<close>

text \<open>
  The P predicate is the pre-condition for the \verb+enqueue+ operation. For the operation
  to succeed, the state must satisfy the Invariant plus an enqueue must be possible, i.e.
  there is space in the descriptor ring to hold the buffer. Lastly, the buffer to be 
  enqueued must be owned by the agent i.e. a member of the set SX or SY respectively.
  We provide two abbreviations for this, one for each side:\<close>

abbreviation "CleanQ_RB_enq_x_P K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> 
                                          CleanQ_RB_enq_x_possible rb \<and> b \<in> rSX rb"

abbreviation "CleanQ_RB_enq_y_P K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> 
                                          CleanQ_RB_enq_y_possible rb \<and> b \<in> rSY rb"

paragraph \<open>Enqueue Q\<close>

text \<open>
  The Q predicate is the post-condition for the write part of the  \verb+enqueue+ operation, 
  and the pre-condition of the increment part of the \verb+enqueue+ operation. The write
  operation does not transfer ownership of the buffer yet, thus the buffer remains in
  SX or SY respectively and the enqueue still remains possible. However, we now know, 
  that the buffer is written to the head location of the ring, and that this location
  is not \verb+None+.
\<close>

abbreviation "CleanQ_RB_enq_x_Q K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> 
                                          CleanQ_RB_enq_x_possible rb \<and> b \<in> rSX rb \<and> 
                                          b = CleanQ_RB_read_head_x rb \<and> 
                                          \<not>CleanQ_RB_head_none_x rb "

abbreviation "CleanQ_RB_enq_y_Q K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> 
                                          CleanQ_RB_enq_y_possible rb \<and> b \<in> rSY rb \<and>
                                           b = CleanQ_RB_read_head_y rb \<and> 
                                           \<not>CleanQ_RB_head_none_y rb "

paragraph \<open>Enqueue R\<close>


text \<open>
  The R predicate is the post condition for both, the increment head part as well as the
  full \verb+enqueue+ operation. We now that the buffer is now no longer in the owning 
  sets SX and SY. Note, we cannot make a state about whether it is in the ring, because
  the other side may have already taken it out. Also, we cannot make any statements
  about whether we can enqueue again.
\<close>

abbreviation "CleanQ_RB_enq_y_R K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> b \<notin> rSX rb"

abbreviation "CleanQ_RB_enq_x_R K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> b \<notin> rSY rb"

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Pre-Post Conditions for the Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We now define the hoare triples for the dequeue operation. Those are needed to later
  for the interference proof. There are a total of three predicates for the dequeue
  operation in small step semantics, while the predicates P and R define the big 
  step semantics.

  \verb+{P} read_tail {Q} incr_tail {R}+ 

  We now provide abbreviations for each of the predicate P, Q, and R for the \verb+dequeue+
  operation as seen from Y and X.   
\<close>


paragraph \<open>Dequeue P\<close>

text \<open>
  The P predicate is the pre-condition for the \verb+dequeue+ operation. For this operation
  to succeed, the state must satisfy teh Invariant plus a dequeue must be possible, i.e.
  the ring must not be empty. 
\<close>

abbreviation "CleanQ_RB_deq_x_P K rb \<equiv> CleanQ_RB_Invariants K rb \<and> 
                                        CleanQ_RB_deq_x_possible rb"

abbreviation "CleanQ_RB_deq_y_P K rb \<equiv> CleanQ_RB_Invariants K rb \<and> 
                                          CleanQ_RB_deq_y_possible rb"


paragraph \<open>Dequeue Q\<close>

text \<open>
  The Q predicate is the post-condition of the read part of the \verb+dequeue+ operation, 
  and the pre-condition of the increment tail part. Just reading the buffer does not
  change the ownership of the buffer and it remains in the ownership of the ring. As
  such, a dequeue is still possible.
\<close>

abbreviation "CleanQ_RB_deq_x_Q K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> 
                                          CleanQ_RB_deq_x_possible rb \<and> 
                                          b = CleanQ_RB_read_tail_x rb"

abbreviation "CleanQ_RB_deq_y_Q K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> 
                                          CleanQ_RB_deq_y_possible rb \<and> 
                                          b = CleanQ_RB_read_tail_y rb"

paragraph \<open>Dequeue R\<close>

text \<open>
  The R predicate is the post-condition of the \verb+dequeue+ operation in big step
  semantics, as well as the post condition of the increment tail part. We now know
  that the buffer is in the ownership of the subjects i.e. an eleemnt of SX or SY 
  respectively. We now do not know whether we can dequeue again. 
\<close>

abbreviation "CleanQ_RB_deq_x_R K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> b \<in> rSX rb"
abbreviation "CleanQ_RB_deq_y_R K rb b \<equiv> CleanQ_RB_Invariants K rb \<and> b \<in> rSY rb"


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Hoare Triples for the Enqueue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  We now show that the \verb+enqueue+ operation satisfies the pre and post conditions
  for the predicates P, Q and R. 
\<close>


paragraph \<open>Writing the Head Element\<close>

text \<open>
  We show the Hoare triple with \verb+{P) write_head {Q}+.
\<close>

lemma  CleanQ_RB_write_head_x_hoare:
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_P K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_write_head_x b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_enq_x_Q K \<acute> RingCRB b  \<rbrace>"                                                 
  apply(vcg, auto simp: CleanQ_RB_write_head_x_Invariant[symmetric] 
                        CleanQ_RB_write_head_x_can_enq_x[symmetric]
                        CleanQ_RB_write_head_read_head_x CleanQ_RB_head_write_x_not_none)
  by(simp add: CleanQ_RB_write_head_x_def)


lemma  CleanQ_RB_write_head_y_hoare:
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_y_P K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_write_head_y b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_enq_y_Q K \<acute> RingCRB b  \<rbrace>"                                                 
  apply(vcg, auto simp: CleanQ_RB_write_head_y_Invariant[symmetric] 
                        CleanQ_RB_write_head_y_can_enq_y[symmetric]
                        CleanQ_RB_write_head_read_head_y CleanQ_RB_head_write_y_not_none)
  by(simp add: CleanQ_RB_write_head_y_def)


paragraph \<open>Incrementing the Head Pointer\<close>

text \<open>
  We show the Hoare triple with \verb+{Q) incr_head {R}+.
\<close>

lemma  CleanQ_RB_incr_head_x_hoare:
  "\<Gamma>\<turnstile> \<lbrace>  CleanQ_RB_enq_x_Q K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_incr_head_x b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_enq_x_R K \<acute> RingCRB b  \<rbrace>"
  apply(vcg, simp add: CleanQ_RB_enq_x_equiv_incr_head CleanQ_RB_enq_x_inv_all)
  by (simp add: CleanQ_RB_enq_x_result)

lemma  CleanQ_RB_incr_head_y_hoare:
  "\<Gamma>\<turnstile> \<lbrace>  CleanQ_RB_enq_y_Q K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_incr_head_y b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_enq_y_R K \<acute> RingCRB b  \<rbrace>"
  apply(vcg, simp add: CleanQ_RB_enq_y_equiv_incr_head CleanQ_RB_enq_y_inv_all)
  by (simp add: CleanQ_RB_enq_y_result)


paragraph \<open>Full Enqueue Operation\<close>

text \<open>
  We show the Hoare triple with \verb+{P) enq {R}+.
\<close>

lemma CleanQ_RB_enq_x_hoare : 
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_P K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_write_head_x b \<acute>RingCRB) ;;
        \<acute>RingCRB :== (CleanQ_RB_incr_head_x b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_enq_x_R K \<acute>RingCRB b \<rbrace>"
  apply(vcg) using CleanQ_RB_enq_x_inv_all CleanQ_RB_enq_x_result by fastforce
 

lemma CleanQ_RB_enq_y_hoare : 
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_y_P K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_write_head_y b \<acute>RingCRB) ;;
        \<acute>RingCRB :== (CleanQ_RB_incr_head_y b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_enq_y_R K \<acute>RingCRB b \<rbrace>"
  apply(vcg) using CleanQ_RB_enq_y_inv_all CleanQ_RB_enq_y_result by fastforce



(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Hoare Triples for the Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  We now show that the \verb+dequeue+ operation satisfies the pre and post conditions
  for the predicates P, Q and R. 
\<close>


paragraph \<open>Reading the Tail Element\<close>

text \<open>
  We show the Hoare triple with \verb+{P) read_tail {Q}+.
\<close>

lemma  CleanQ_RB_read_tail_x_hoare:
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_deq_x_P K \<acute>RingCRB \<rbrace> 
        \<acute>b :== (CleanQ_RB_read_tail_x \<acute>RingCRB)
      \<lbrace> CleanQ_RB_deq_x_Q K \<acute>RingCRB \<acute>b  \<rbrace>"  
  by(vcg)

lemma  CleanQ_RB_read_tail_y_hoare:
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_deq_y_P K \<acute>RingCRB \<rbrace> 
        \<acute>b :== (CleanQ_RB_read_tail_y \<acute>RingCRB)
      \<lbrace> CleanQ_RB_deq_y_Q K \<acute>RingCRB \<acute>b  \<rbrace>"  
  by(vcg)


paragraph \<open>Incrementing the Tail Pointer\<close>

text \<open>
  We show the Hoare triple with \verb+{Q) incr_tail {R}+.
\<close>

lemma  CleanQ_RB_incr_tail_x_hoare:
  "\<Gamma>\<turnstile> \<lbrace>  CleanQ_RB_deq_x_Q K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_incr_tail_x b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_deq_x_R K \<acute> RingCRB b  \<rbrace>"
  apply(vcg, auto)
  using CleanQ_RB_deq_x_all_inv apply blast
  by (simp add: CleanQ_RB_deq_x_result CleanQ_RB_read_tail_x_def)

lemma  CleanQ_RB_incr_tail_y_hoare:
  "\<Gamma>\<turnstile> \<lbrace>  CleanQ_RB_deq_y_Q K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_incr_tail_y b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_deq_y_R K \<acute> RingCRB b  \<rbrace>"
  apply(vcg, auto)
  using CleanQ_RB_deq_y_all_inv apply blast
  by (simp add: CleanQ_RB_deq_y_result CleanQ_RB_read_tail_y_def)

 
paragraph \<open>Full Dequeue Operation\<close>

text \<open>
  We show the Hoare triple with \verb+{P) deq {R}+.
\<close>

lemma CleanQ_RB_deq_x_hoare : 
  "\<Gamma>\<turnstile> \<lbrace>  CleanQ_RB_deq_x_P K \<acute>RingCRB  \<rbrace> 
        \<acute>b :== (CleanQ_RB_read_tail_x \<acute>RingCRB) ;;
        \<acute>RingCRB :== (CleanQ_RB_incr_tail_x \<acute>b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_deq_x_R K \<acute>RingCRB \<acute>b  \<rbrace>"
  apply(vcg, auto)
  using CleanQ_RB_deq_x_all_inv apply blast
  by (simp add: CleanQ_RB_deq_x_result CleanQ_RB_read_tail_x_def)

lemma CleanQ_RB_deq_y_hoare : 
  "\<Gamma>\<turnstile> \<lbrace>  CleanQ_RB_deq_y_P K \<acute>RingCRB  \<rbrace> 
        \<acute>b :== (CleanQ_RB_read_tail_y \<acute>RingCRB) ;;
        \<acute>RingCRB :== (CleanQ_RB_incr_tail_y \<acute>b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_deq_y_R K \<acute>RingCRB \<acute>b  \<rbrace>"
  apply(vcg, auto)
  using CleanQ_RB_deq_y_all_inv apply blast
  by (simp add: CleanQ_RB_deq_y_result CleanQ_RB_read_tail_y_def)

(* ==================================================================================== *)
subsection \<open>Interference pairs\<close>
(* ==================================================================================== *)
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We are now showing the interference proofs for the different step. There are two threads
  in the system, each of which can execute the enqueue and dequeue operations independently.
  
  The system looks like this:

    \verb+ (enq_x | deq_x)  ||  (enq_y | deq_y)+

  While each of the four operations consists of two steps. reading/writing the buffer slot
  and updating the head/tail pointer respectively.

  We fix one side (X) and show that the other side cannot interfere with each of the
  possible interference pairs. The correctness of the other side follows by symmetry.
\<close>

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue X, Enqueue Y\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open> 
  The Enqueue operation has the form: \verb+{P} write_head {Q} increment_head {R}+.
  We show, that the predicates of the Hoare triples remain valid, regardless of the 
  operation of the other side.
\<close>



paragraph \<open>Y writes the descriptor ring\<close>

lemma CleanQ_CRB_Enqueue_X_P_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace>"
  apply(vcg, simp add: CleanQ_RB_write_head_y_can_enq_x[symmetric] CleanQ_RB_write_head_y_Invariant[symmetric])  
  by (simp add: CleanQ_RB_write_head_y_def)

lemma CleanQ_CRB_Enqueue_X_Q_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_Q K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_enq_x_Q K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto simp add: CleanQ_RB_write_head_y_can_enq_x[symmetric]
                            CleanQ_RB_write_head_y_Invariant[symmetric])
 
  apply (simp add: CleanQ_RB_write_head_y_def)
  apply (simp add: CleanQ_RB_read_head_x_def CleanQ_RB_write_head_y_def)
  by (simp add: CleanQ_RB_head_none_x_def CleanQ_RB_write_head_y_def)


lemma CleanQ_CRB_Enqueue_X_R_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_R K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_enq_x_R K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto simp:CleanQ_RB_write_head_y_Invariant[symmetric])  
  by (simp add: CleanQ_RB_write_head_y_def)


  

paragraph \<open>Y increments the head\<close>

lemma CleanQ_CRB_Enqueue_X_P_incr_head:
"\<Gamma>\<turnstile> \<lbrace>  rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_RB_enq_x_P K rb bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace>"
  apply(vcg, auto)
    apply (meson CleanQ_RB_enq_y_inv_all CleanQ_RB_write_head_y_Invariant)
  apply (meson CleanQ_RB_enq_y_enq_x_possible CleanQ_RB_write_head_y_Invariant CleanQ_RB_write_head_y_can_enq_x)
  by (simp add: CleanQ_RB_enq_y_def CleanQ_RB_write_head_y_def)


lemma CleanQ_CRB_Enqueue_X_Q_incr_head:
"\<Gamma>\<turnstile> \<lbrace>  rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_RB_enq_x_Q K rb bx   \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_RB_enq_x_Q K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto)
  apply (meson CleanQ_RB_enq_y_inv_all CleanQ_RB_write_head_y_Invariant)
  apply (meson CleanQ_RB_enq_y_enq_x_possible CleanQ_RB_write_head_y_Invariant CleanQ_RB_write_head_y_can_enq_x)
    apply (simp add: CleanQ_RB_enq_y_def CleanQ_RB_write_head_y_def)
   apply (simp add: CleanQ_RB_enq_y_def CleanQ_RB_read_head_x_def CleanQ_RB_write_head_y_def)
  by (simp add: CleanQ_RB_enq_y_def CleanQ_RB_head_none_x_def CleanQ_RB_write_head_y_def)
  
  
lemma CleanQ_CRB_Enqueue_X_R_incr_head:
"\<Gamma>\<turnstile> \<lbrace> rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_RB_enq_x_R K rb bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_RB_enq_x_R K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto)
  apply (meson CleanQ_RB_enq_y_inv_all CleanQ_RB_write_head_y_Invariant)
  by (simp add: CleanQ_RB_enq_y_def CleanQ_RB_write_head_y_def)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue X, Dequeue X\<close>
(* ------------------------------------------------------------------------------------ *)

paragraph \<open>Y reads the descriptor ring\<close>

lemma CleanQ_CRB_Enqueue_X_P_read_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace> 
     \<acute>b :== CleanQ_RB_read_tail_y \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace>"
  by(vcg)

lemma CleanQ_CRB_Enqueue_X_Q_read_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_Q K \<acute>RingCRB bx  \<rbrace> 
     \<acute>b :== CleanQ_RB_read_tail_y \<acute>RingCRB
  \<lbrace>  CleanQ_RB_enq_x_Q K \<acute>RingCRB bx \<rbrace>"
  by(vcg)

lemma CleanQ_CRB_Enqueue_X_R_read_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_R K \<acute>RingCRB bx  \<rbrace> 
     \<acute>b :== CleanQ_RB_read_tail_y \<acute>RingCRB
  \<lbrace>  CleanQ_RB_enq_x_R K \<acute>RingCRB bx \<rbrace>"
   by(vcg)

paragraph \<open>Y increments the tail pointer\<close>

lemma CleanQ_CRB_Enqueue_X_P_incr_tail:
"\<Gamma>\<turnstile> \<lbrace>  b = CleanQ_RB_read_tail_y  \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_deq_y_possible \<acute>RingCRB \<and> CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace> 
      \<acute>RingCRB  :== CleanQ_RB_incr_tail_y b  \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace>"
  apply(vcg, auto simp:CleanQ_RB_deq_y_all_inv CleanQ_RB_deq_y_enq_x_possible )  
  using CleanQ_RB_deq_y_no_change by blast

lemma CleanQ_CRB_Enqueue_X_Q_incr_tail:
"\<Gamma>\<turnstile> \<lbrace>  b = CleanQ_RB_read_tail_y  \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_deq_y_possible \<acute>RingCRB \<and> CleanQ_RB_enq_x_Q K \<acute>RingCRB bx  \<rbrace> 
     \<acute>RingCRB  :== CleanQ_RB_incr_tail_y b  \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_enq_x_Q K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto simp:CleanQ_RB_deq_y_all_inv CleanQ_RB_deq_y_enq_x_possible ) 
  using CleanQ_RB_deq_y_no_change apply blast
  apply (metis CleanQ_RB_Invariants_def CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def I2_rb_img_def I4_rb_valid_def IntI empty_iff prod.sel(1) rb_deq_def rb_deq_list_was_in)
  by (metis CleanQ_RB_Invariants_def CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def I2_rb_img_def I4_rb_valid_def IntI empty_iff prod.sel(1) rb_deq_def rb_deq_list_was_in)

lemma CleanQ_CRB_Enqueue_X_R_incr_tail:
"\<Gamma>\<turnstile> \<lbrace>  b = CleanQ_RB_read_tail_y  \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_deq_y_possible \<acute>RingCRB \<and> CleanQ_RB_enq_x_R K \<acute>RingCRB bx  \<rbrace> 
     \<acute>RingCRB  :== CleanQ_RB_incr_tail_y b  \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_enq_x_R K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto simp:CleanQ_RB_deq_y_all_inv CleanQ_RB_deq_y_enq_x_possible )
  by (metis CleanQ_RB_Invariants_def CleanQ_RB_deq_y_possible_def CleanQ_RB_read_tail_y_def 
            I2_rb_img_def I4_rb_valid_def IntI empty_iff prod.sel(1) rb_deq_def rb_deq_list_was_in)





(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue X, Enqueue Y\<close>
(* ------------------------------------------------------------------------------------ *)

paragraph \<open>Y writes the descriptor ring\<close>

lemma CleanQ_CRB_Dequeue_X_P_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_deq_x_P K \<acute>RingCRB  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_deq_x_P K \<acute>RingCRB \<rbrace>"
  apply(vcg)
  by (meson CleanQ_RB_write_head_y_Invariant CleanQ_RB_write_head_y_can_deq_x)

lemma CleanQ_CRB_Dequeue_X_Q_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_deq_x_Q K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_deq_x_Q K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, simp add: CleanQ_RB_write_head_y_can_enq_x[symmetric]
                      CleanQ_RB_write_head_y_can_deq_x[symmetric] )
  by (metis CleanQ_RB_Invariants_def CleanQ_RB_deq_x_possible_def
      CleanQ_RB_read_tail_x_def CleanQ_RB_write_head_y_I4 CleanQ_RB_write_head_y_Invariant 
      CleanQ_RB_write_head_y_can_deq_x CleanQ_RB_write_head_y_list I4_rb_valid_def prod.sel(1) 
      rb_deq_def rb_deq_list_was_head rb_valid_implies_ptr_valid)
 
lemma CleanQ_CRB_Dequeue_X_R_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_deq_x_R K \<acute>RingCRB bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
  \<lbrace>  CleanQ_RB_deq_x_R K \<acute>RingCRB bx \<rbrace>"
  apply(vcg)
  by (metis CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(4) 
      CleanQ_RB_write_head_y_Invariant CleanQ_RB_write_head_y_def)  

paragraph \<open>Y increments the head pointer\<close>

lemma CleanQ_CRB_Dequeue_X_P_incr_head:
"\<Gamma>\<turnstile> \<lbrace>  rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_RB_deq_x_P K \<acute>RingCRB \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_RB_deq_x_P K \<acute>RingCRB  \<rbrace>"
  apply(vcg)
  by (simp add: CleanQ_RB_enq_y_deq_x_possible CleanQ_RB_enq_y_inv_all)
  

  
lemma CleanQ_CRB_Dequeue_X_Q_incr_head:
"\<Gamma>\<turnstile> \<lbrace>  rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_RB_deq_x_Q K rb bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_RB_deq_x_Q K \<acute>RingCRB bx \<rbrace>"
  apply(vcg, auto) 
  apply (meson CleanQ_RB_enq_y_inv_all CleanQ_RB_write_head_y_Invariant)
  apply (meson CleanQ_RB_enq_y_deq_x_possible CleanQ_RB_write_head_y_Invariant)
  unfolding CleanQ_RB_read_tail_x_def CleanQ_RB_write_head_y_def CleanQ_RB_enq_y_def
  unfolding rb_read_tail_def rb_write_head_def rb_enq_def
  by (simp add: rb_incr_head_def)
  

lemma CleanQ_CRB_Dequeue_X_R_incr_head:
"\<Gamma>\<turnstile> \<lbrace>  rb = CleanQ_RB_write_head_y b \<acute>RingCRB \<and> b \<in> rSY \<acute>RingCRB \<and> CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> CleanQ_RB_deq_x_R K rb bx  \<rbrace> 
   \<acute>RingCRB :== CleanQ_RB_incr_head_y b rb 
  \<lbrace>  CleanQ_RB_deq_x_R K \<acute>RingCRB bx \<rbrace>"
  apply(vcg)
  by (metis CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(2) 
      CleanQ_RB_State.update_convs(4) CleanQ_RB_enq_y_inv_all CleanQ_RB_enq_y_split_equal 
      CleanQ_RB_incr_head_y_def CleanQ_RB_write_head_y_Invariant)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue X, Dequeue X\<close>
(* ------------------------------------------------------------------------------------ *)

lemma CleanQ_RB_enq_interfernce_1 :
"\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RingCRB \<and> CleanQ_RB_Invariants K \<acute>RingCRB \<and> 
     enq =  CleanQ_RB_enq_x_possible \<acute>RingCRB \<and> deq =  CleanQ_RB_deq_x_possible \<acute>RingCRB \<and>
     CleanQ_RB_deq_y_possible \<acute>RingCRB \<and> enq2 = CleanQ_RB_enq_y_possible \<acute>RingCRB   \<rbrace> 
    \<acute>b :== (CleanQ_RB_read_tail_y \<acute>RingCRB) 
    \<lbrace> rb' = \<acute>RingCRB \<and> CleanQ_RB_Invariants K \<acute> RingCRB \<and>
      enq =  CleanQ_RB_enq_x_possible \<acute>RingCRB \<and> deq =  CleanQ_RB_deq_x_possible \<acute>RingCRB \<and>
     CleanQ_RB_deq_y_possible \<acute>RingCRB \<and> enq2 = CleanQ_RB_enq_y_possible \<acute>RingCRB   \<rbrace>"
  by(vcg)
  

lemma CleanQ_RB_enq_interfernce_2 :
  "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RingCRB \<and> CleanQ_RB_Invariants K \<acute> RingCRB  \<and>
        deq =  CleanQ_RB_deq_x_possible \<acute>RingCRB \<and>
       CleanQ_RB_deq_y_possible \<acute>RingCRB \<and> enq2 = CleanQ_RB_enq_y_possible \<acute>RingCRB  \<and>
         b = CleanQ_RB_read_tail_y \<acute>RingCRB  \<rbrace> 
      \<acute>RingCRB :== (CleanQ_RB_incr_tail_y b \<acute>RingCRB) 
      \<lbrace> CleanQ_RB_Invariants K \<acute> RingCRB \<and> 
        CleanQ_RB_enq_x_possible \<acute>RingCRB \<and> deq =  CleanQ_RB_deq_x_possible \<acute>RingCRB \<and>
       enq2 = CleanQ_RB_enq_y_possible \<acute>RingCRB  \<and>  b \<in> rSY \<acute>RingCRB 
       \<rbrace>"

  apply (vcg, simp add: CleanQ_RB_deq_y_all_inv)
  by(simp add: CleanQ_RB_deq_y_enq_x_possible CleanQ_RB_deq_y_deq_x_possible 
               CleanQ_RB_deq_y_enq_y_possible CleanQ_RB_deq_y_result CleanQ_RB_read_tail_y_def)


lemma CleanQ_RB_enq_interfernce_3 :
    "\<Gamma>\<turnstile> \<lbrace>  rb' = \<acute>RingCRB \<and> CleanQ_RB_Invariants K \<acute> RingCRB \<and>
           enq = CleanQ_RB_enq_x_possible \<acute>RingCRB \<and> deq =  CleanQ_RB_deq_x_possible \<acute>RingCRB \<and>
           CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> deq2 =  CleanQ_RB_deq_y_possible \<acute>RingCRB \<and>
           b \<in> rSY \<acute>RingCRB  \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_write_head_y b \<acute>RingCRB)
        \<lbrace> CleanQ_RB_Invariants K \<acute> RingCRB \<and> b \<in> rSY \<acute>RingCRB  \<and>
         enq = CleanQ_RB_enq_x_possible \<acute>RingCRB \<and> deq =  CleanQ_RB_deq_x_possible \<acute>RingCRB \<and>
         CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> deq2 = CleanQ_RB_deq_y_possible \<acute>RingCRB \<rbrace>"
  apply(vcg)
  by (metis CleanQ_RB_State.ext_inject CleanQ_RB_State.surjective CleanQ_RB_State.update_convs(4) 
      CleanQ_RB_write_head_y_Invariant CleanQ_RB_write_head_y_can_deq_x CleanQ_RB_write_head_y_can_deq_y 
      CleanQ_RB_write_head_y_can_enq_x CleanQ_RB_write_head_y_can_enq_y CleanQ_RB_write_head_y_def)

lemma CleanQ_RB_enq_interfernce_4 :
 "\<Gamma>\<turnstile> \<lbrace> rb' = \<acute>RingCRB \<and> CleanQ_RB_Invariants K \<acute> RingCRB \<and>
        enq = CleanQ_RB_enq_x_possible \<acute>RingCRB \<and>
        CleanQ_RB_enq_y_possible \<acute>RingCRB \<and> deq2 =  CleanQ_RB_deq_y_possible \<acute>RingCRB \<and>
        b \<in> rSY \<acute>RingCRB \<and> rb = (CleanQ_RB_write_head_y b \<acute>RingCRB)   \<rbrace>
        \<acute>RingCRB :== (CleanQ_RB_incr_head_y b rb) 
        \<lbrace> CleanQ_RB_Invariants K \<acute> RingCRB \<and> b \<notin> rSY \<acute>RingCRB \<and>
         enq = CleanQ_RB_enq_x_possible \<acute>RingCRB \<and> CleanQ_RB_deq_x_possible \<acute>RingCRB \<and>
         deq2 =  CleanQ_RB_deq_y_possible \<acute>RingCRB 
 \<rbrace>"
  apply(vcg, simp add:CleanQ_RB_enq_y_inv_all CleanQ_RB_enq_y_enq_x_possible)
  apply (simp add: CleanQ_RB_enq_y_result CleanQ_RB_enq_y_deq_x_possible)
  by (meson CleanQ_RB_enq_y_deq_y_possible)

end 