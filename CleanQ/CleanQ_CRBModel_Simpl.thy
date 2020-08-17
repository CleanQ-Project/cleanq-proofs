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
  by(vcg, auto)

lemma  CleanQ_RB_write_head_y_hoare:
  "\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_y_P K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_write_head_y b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_enq_y_Q K \<acute> RingCRB b  \<rbrace>"                                                 
  by(vcg, auto)


paragraph \<open>Incrementing the Head Pointer\<close>

text \<open>
  We show the Hoare triple with \verb+{Q) incr_head {R}+.
\<close>

lemma  CleanQ_RB_incr_head_x_hoare:
  "\<Gamma>\<turnstile> \<lbrace>  CleanQ_RB_enq_x_Q K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_incr_head_x b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_enq_x_R K \<acute> RingCRB b  \<rbrace>"
  apply(vcg, auto simp:CleanQ_RB_enq_x_inv_all)
  by (simp add: CleanQ_RB_enq_x_result)


lemma  CleanQ_RB_incr_head_y_hoare:
  "\<Gamma>\<turnstile> \<lbrace>  CleanQ_RB_enq_y_Q K \<acute>RingCRB b \<rbrace> 
        \<acute>RingCRB :== (CleanQ_RB_incr_head_y b \<acute>RingCRB)
      \<lbrace> CleanQ_RB_enq_y_R K \<acute> RingCRB b  \<rbrace>"
  apply(vcg, auto simp:CleanQ_RB_enq_y_inv_all)
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
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_P K \<acute>RingCRB bx \<rbrace> 
      \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
    \<lbrace> CleanQ_RB_enq_x_P K \<acute>RingCRB bx \<rbrace>"
  by(vcg, auto)  

lemma CleanQ_CRB_Enqueue_X_Q_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_Q K \<acute>RingCRB bx \<rbrace> 
      \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
    \<lbrace> CleanQ_RB_enq_x_Q K \<acute>RingCRB bx \<rbrace>"
  by(vcg, auto) 

lemma CleanQ_CRB_Enqueue_X_R_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_R K \<acute>RingCRB bx \<rbrace> 
      \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
    \<lbrace> CleanQ_RB_enq_x_R K \<acute>RingCRB bx \<rbrace>"
  by(vcg, auto)  


paragraph \<open>Y increments the head\<close>

lemma CleanQ_CRB_Enqueue_X_P_incr_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_y_Q K \<acute>RingCRB b \<and>  CleanQ_RB_enq_x_P K \<acute>RingCRB bx \<rbrace> 
     \<acute>RingCRB :== CleanQ_RB_incr_head_y b \<acute>RingCRB
    \<lbrace> CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace>"
  by(vcg, auto simp:CleanQ_RB_enq_y_enq_x_possible CleanQ_RB_enq_y_inv_all)

lemma CleanQ_CRB_Enqueue_X_Q_incr_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_y_Q K \<acute>RingCRB b \<and>  CleanQ_RB_enq_x_Q K \<acute>RingCRB bx \<rbrace> 
     \<acute>RingCRB :== CleanQ_RB_incr_head_y b \<acute>RingCRB 
    \<lbrace> CleanQ_RB_enq_x_Q K \<acute>RingCRB bx \<rbrace>"
  by(vcg, auto simp: CleanQ_RB_enq_y_inv_all CleanQ_RB_enq_y_enq_x_possible)
  
lemma CleanQ_CRB_Enqueue_X_R_incr_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_y_Q K \<acute>RingCRB b \<and>  CleanQ_RB_enq_x_R K \<acute>RingCRB bx \<rbrace> 
     \<acute>RingCRB :== CleanQ_RB_incr_head_y b \<acute>RingCRB 
    \<lbrace> CleanQ_RB_enq_x_R K \<acute>RingCRB bx \<rbrace>"
  by(vcg, auto simp: CleanQ_RB_enq_y_inv_all CleanQ_RB_enq_y_def)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue X, Dequeue X\<close>
(* ------------------------------------------------------------------------------------ *)

paragraph \<open>Y reads the descriptor ring\<close>

lemma CleanQ_CRB_Enqueue_X_P_read_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace> 
       \<acute>b :== CleanQ_RB_read_tail_y \<acute>RingCRB 
    \<lbrace> CleanQ_RB_enq_x_P K \<acute>RingCRB bx  \<rbrace>"
  by(vcg)

lemma CleanQ_CRB_Enqueue_X_Q_read_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_Q K \<acute>RingCRB bx \<rbrace> 
       \<acute>b :== CleanQ_RB_read_tail_y \<acute>RingCRB
    \<lbrace> CleanQ_RB_enq_x_Q K \<acute>RingCRB bx \<rbrace>"
  by(vcg)

lemma CleanQ_CRB_Enqueue_X_R_read_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_x_R K \<acute>RingCRB bx \<rbrace> 
       \<acute>b :== CleanQ_RB_read_tail_y \<acute>RingCRB
    \<lbrace> CleanQ_RB_enq_x_R K \<acute>RingCRB bx \<rbrace>"
   by(vcg)


paragraph \<open>Y increments the tail pointer\<close>

lemma CleanQ_CRB_Enqueue_X_P_incr_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_deq_y_Q K \<acute>RingCRB b \<and> CleanQ_RB_enq_x_P K \<acute>RingCRB bx \<rbrace> 
       \<acute>RingCRB  :== CleanQ_RB_incr_tail_y b  \<acute>RingCRB 
    \<lbrace> CleanQ_RB_enq_x_P K \<acute>RingCRB bx \<rbrace>"
  by(vcg, auto simp:CleanQ_RB_deq_y_all_inv CleanQ_RB_deq_y_enq_x_possible )  


lemma CleanQ_CRB_Enqueue_X_Q_incr_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_deq_y_Q K \<acute>RingCRB b \<and> CleanQ_RB_enq_x_Q K \<acute>RingCRB bx \<rbrace> 
       \<acute>RingCRB  :== CleanQ_RB_incr_tail_y b  \<acute>RingCRB 
    \<lbrace> CleanQ_RB_enq_x_Q K \<acute>RingCRB bx \<rbrace>"
  by(vcg, auto simp:CleanQ_RB_deq_y_all_inv CleanQ_RB_deq_y_enq_x_possible)
  

lemma CleanQ_CRB_Enqueue_X_R_incr_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_deq_y_Q K \<acute>RingCRB b \<and> CleanQ_RB_enq_x_R K \<acute>RingCRB bx  \<rbrace> 
       \<acute>RingCRB  :== CleanQ_RB_incr_tail_y b  \<acute>RingCRB 
    \<lbrace> CleanQ_RB_enq_x_R K \<acute>RingCRB bx \<rbrace>"
  by(vcg, auto simp:CleanQ_RB_deq_y_all_inv CleanQ_RB_deq_y_enq_x_possible )


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue X, Enqueue Y\<close>
(* ------------------------------------------------------------------------------------ *)

paragraph \<open>Y writes the descriptor ring\<close>

lemma CleanQ_CRB_Dequeue_X_P_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_deq_x_P K \<acute>RingCRB \<rbrace> 
     \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
    \<lbrace> CleanQ_RB_deq_x_P K \<acute>RingCRB \<rbrace>"
  by(vcg, auto)

lemma CleanQ_CRB_Dequeue_X_Q_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_deq_x_Q K \<acute>RingCRB bx \<rbrace> 
       \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
    \<lbrace> CleanQ_RB_deq_x_Q K \<acute>RingCRB bx \<rbrace>"
  by(vcg, auto)
  
lemma CleanQ_CRB_Dequeue_X_R_write_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_deq_x_R K \<acute>RingCRB bx \<rbrace> 
       \<acute>RingCRB :== CleanQ_RB_write_head_y b \<acute>RingCRB 
    \<lbrace> CleanQ_RB_deq_x_R K \<acute>RingCRB bx \<rbrace>"
  by(vcg, auto)


paragraph \<open>Y increments the head pointer\<close>

lemma CleanQ_CRB_Dequeue_X_P_incr_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_y_Q K \<acute>RingCRB b \<and> CleanQ_RB_deq_x_P K \<acute>RingCRB \<rbrace> 
       \<acute>RingCRB :== CleanQ_RB_incr_head_y b \<acute>RingCRB 
    \<lbrace> CleanQ_RB_deq_x_P K \<acute>RingCRB \<rbrace>"
  by(vcg, auto simp:CleanQ_RB_enq_y_inv_all CleanQ_RB_enq_y_deq_x_possible)
  
lemma CleanQ_CRB_Dequeue_X_Q_incr_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_y_Q K \<acute>RingCRB b \<and> CleanQ_RB_deq_x_Q K \<acute>RingCRB bx \<rbrace> 
       \<acute>RingCRB :== CleanQ_RB_incr_head_y b \<acute>RingCRB 
    \<lbrace> CleanQ_RB_deq_x_Q K \<acute>RingCRB bx \<rbrace>"
  by(vcg, auto simp:CleanQ_RB_enq_y_inv_all CleanQ_RB_enq_y_deq_x_possible) 
  
 
lemma CleanQ_CRB_Dequeue_X_R_incr_head:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_enq_y_Q K \<acute>RingCRB b \<and> CleanQ_RB_deq_x_R K \<acute>RingCRB bx \<rbrace> 
       \<acute>RingCRB :== CleanQ_RB_incr_head_y b \<acute>RingCRB 
    \<lbrace> CleanQ_RB_deq_x_R K \<acute>RingCRB bx \<rbrace>"
  by(vcg, auto simp:CleanQ_RB_enq_y_inv_all)
  
  
(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue X, Dequeue X\<close>
(* ------------------------------------------------------------------------------------ *)


paragraph \<open>Y reads the descriptor ring\<close>

lemma CleanQ_CRB_Dequeue_X_P_read_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_deq_x_P K \<acute>RingCRB \<rbrace> 
       \<acute>b :== CleanQ_RB_read_tail_y \<acute>RingCRB 
    \<lbrace> CleanQ_RB_deq_x_P K \<acute>RingCRB \<rbrace>"
  by(vcg)

lemma CleanQ_CRB_Dequeue_X_Q_read_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_deq_x_Q K \<acute>RingCRB bx \<rbrace> 
       \<acute>b :== CleanQ_RB_read_tail_y \<acute>RingCRB  
    \<lbrace> CleanQ_RB_deq_x_Q K \<acute>RingCRB bx \<rbrace>"
  by(vcg)
  
lemma CleanQ_CRB_Dequeue_X_R_read_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_deq_x_R K \<acute>RingCRB bx \<rbrace> 
       \<acute>b :== CleanQ_RB_read_tail_y \<acute>RingCRB 
    \<lbrace> CleanQ_RB_deq_x_R K \<acute>RingCRB bx \<rbrace>"
  by(vcg)


paragraph \<open>Y increments the tail pointer\<close>

lemma CleanQ_CRB_Dequeue_X_P_incr_tail:
"\<Gamma>\<turnstile>\<lbrace> CleanQ_RB_deq_y_Q K \<acute>RingCRB by \<and> CleanQ_RB_deq_x_P K \<acute>RingCRB \<rbrace> 
      \<acute>RingCRB :== CleanQ_RB_incr_tail_y by \<acute>RingCRB 
   \<lbrace> CleanQ_RB_deq_x_P K \<acute>RingCRB   \<rbrace>"
  by(vcg, auto simp: CleanQ_RB_deq_y_deq_x_possible CleanQ_RB_deq_y_all_inv)

lemma CleanQ_CRB_Dequeue_X_Q_incr_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_deq_y_Q K \<acute>RingCRB by \<and> CleanQ_RB_deq_x_Q K \<acute>RingCRB bx \<rbrace> 
       \<acute>RingCRB :== CleanQ_RB_incr_tail_y by \<acute>RingCRB   
    \<lbrace> CleanQ_RB_deq_x_Q K \<acute>RingCRB bx \<rbrace>"
  by(vcg, auto simp:CleanQ_RB_deq_y_all_inv CleanQ_RB_deq_y_deq_x_possible)

lemma CleanQ_CRB_Dequeue_X_R_incr_tail:
"\<Gamma>\<turnstile> \<lbrace> CleanQ_RB_deq_y_Q K \<acute>RingCRB by \<and> CleanQ_RB_deq_x_R K \<acute>RingCRB bx \<rbrace> 
       \<acute>RingCRB :== CleanQ_RB_incr_tail_y by \<acute>RingCRB 
    \<lbrace> CleanQ_RB_deq_x_R K \<acute>RingCRB bx \<rbrace>"
  by(vcg, auto simp:CleanQ_RB_deq_y_all_inv)


end 