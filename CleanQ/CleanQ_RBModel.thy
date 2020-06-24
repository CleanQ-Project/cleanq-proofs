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



section \<open>CleanQ Abstract Ring Buffer Model\<close>

text \<open>
  The second refinement is from unbounded lists to bounded buffer rings for transferring
  ownership between two agents. As a consequence, the \verb+enqueue+ operation may fail, 
  because there is no more space in the ring buffer. 
\<close>

theory CleanQ_RBModel 
(*<*) imports  
    CleanQ_ListModel
    CleanQ_ModularIntervals
begin
(*>*)

(* ==================================================================================== *)
subsection \<open>CleanQ Abstract Ring Buffer Model State\<close>
(* ==================================================================================== *)

text \<open>
  We take the state of the CleanQ list model and refine it to use a bounded, circular
  buffer instead of the lists as transfer sets between the two agents. Again, there is
  one queue (ring buffer) going from $X$ to $Y$ and another one, for the opposit
  direction. Expressing the buffers owned by $X$ and $Y$ remain the same. 

  \<^item> rSX: this is the set of buffers owned by X.
  \<^item> rSY: this is the set of buffers owned by Y.
  \<^item> rTXY: this is a descriptor ring of buffers in transfer from X to Y.
  \<^item> rTYX: this is a descriptor ring of buffers in transfer from Y to X.
\<close>

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Bounded Descriptor Ring\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We first define the type of a the bounded, circular descriptor ring, which we call
  ring buffer (RB). A ring buffer has a well-defined size, or number of slots, which
  defines the amount of elements it can hold.  We define the ring buffer as a function
  from nat to the element. Head and tail define the valid elements in the ring.\<close>

record 'a CleanQ_RB =
  ring :: "nat \<Rightarrow> 'a"
  head :: nat
  tail :: nat
  size :: nat

text \<open>
  A ringbuffer has a certain set of valid entries. We now provide definitions to 
  create the list of entries. Note, this is not [(tail rb) ..<(head rb)]. As there
  might be a wrap around (e.g. head = 4 tail = 8). We use the nonzero modulus
  locale to work out the elements.
\<close>

definition rb_valid_entries :: "'a CleanQ_RB \<Rightarrow> nat list"
  where "rb_valid_entries rb = (nonzero_modulus.list_between 
                                       (size rb) (tail rb) (head rb))"


text \<open>
  Using the valid entries, we can define the buffer elements in the descriptor ring
  by mapping them onto the ring-function of the CleanQ RB:
\<close>

definition CleanQ_RB_list :: "'a CleanQ_RB \<Rightarrow> 'a list"
  where "CleanQ_RB_list rb = map (ring rb) (rb_valid_entries rb)"

text \<open>
  We say a queue is full, if the enqueue operation would lead to the case
  where the head pointer == tail pointer.
\<close>

definition rb_full :: "'a CleanQ_RB \<Rightarrow> bool"
  where "rb_full rb = ((((head rb) + 1) mod (size rb)) = (tail rb))"

definition rb_empty :: "'a CleanQ_RB \<Rightarrow> bool"
  where "rb_empty rb = ((head rb) = (tail rb))"


lemma 
  assumes sz: "size rb > 1" and  hh: "head rb < size rb" and ll: "tail rb < size rb"
    shows "rb_empty rb \<longleftrightarrow> rb_valid_entries rb = []"
proof
  show "rb_empty rb \<Longrightarrow> rb_valid_entries rb = []"
  proof -
    assume e: "rb_empty rb"
    from e have eq:  "((head rb) = (tail rb))"
      unfolding rb_empty_def by(simp)

    from sz have nz:
      "nonzero_modulus (size rb)"
      by (simp add: nonzero_modulus.intro)

    from eq nz have el:  
      "(nonzero_modulus.list_between (size rb) (tail rb) (head rb)) = []"
       using nonzero_modulus.uptol_eq[where N="size rb" and l="tail rb" and h="head rb"]
       by(auto)

    from el show ?thesis  
      unfolding rb_valid_entries_def by(simp)
  qed
next
  show "rb_valid_entries rb = [] \<Longrightarrow> rb_empty rb"
  proof - 
    assume e: "rb_valid_entries rb = []"

    from sz have nz:
      "nonzero_modulus (size rb)"
      by (simp add: nonzero_modulus.intro)    

    from e sz nz have eq:
      "(tail rb) = (head rb)"
      unfolding rb_valid_entries_def 
      using hh ll  nonzero_modulus.uptol_eq_both[where N="size rb" and l="tail rb" and h="head rb"]
      by(auto)

    from eq show ?thesis 
      unfolding rb_empty_def by(auto)
  qed
qed



text \<open>
  We provide functions that increment the head and tail pointers of the queue.
\<close>

definition rb_incr_head :: "'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB"
  where "rb_incr_head rb = rb \<lparr> head := ((head rb) + 1) mod (size rb) \<rparr>"

definition rb_incr_tail :: "'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB"
  where "rb_incr_tail rb = rb \<lparr> tail := ((tail rb) + 1) mod (size rb) \<rparr>"


(*lemma 
  assumes notfull: "\<not>(rb_full rb)"  and  hdinc: "rb' = rb \<lparr>   \<rparr>
*)



text \<open>
  Writing an entry into the ring buffer then corresponds to a function update.
\<close>

definition CleanQ_RB_upd :: "nat \<Rightarrow> 'a \<Rightarrow> 'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB"
  where "CleanQ_RB_upd i b rb = rb \<lparr> ring := (ring rb)(i := b) \<rparr>"


definition rb_enq :: "'a \<Rightarrow> 'a CleanQ_RB \<Rightarrow> 'a CleanQ_RB" 
  where "rb_enq b rb = rb \<lparr> ring := (ring rb)((head rb) := b),
                            head := ((head rb) + 1) mod (size rb) \<rparr>"

definition rb_deq :: "'a CleanQ_RB \<Rightarrow> ('a \<times> 'a CleanQ_RB)"
  where "rb_deq rb = ((ring rb) (tail rb),  
                      rb \<lparr> tail := ((tail rb) + 1) mod (size rb) \<rparr> )"

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>System State\<close>
(* ------------------------------------------------------------------------------------ *)


text \<open>
  We now define the updated system state using \verb+Cleanq_RB+  for the transfer sets
  between $X$ and $Y$. 
 \<close>

record 'a CleanQ_RB_State =
  rSX  :: "'a set"
  rSY  :: "'a set"
  rTXY :: "'a CleanQ_RB"
  rTYX :: "'a CleanQ_RB"


text \<open>
  Like the abstract list model,  we do not specify the representation of the buffer 
  elements. This can be a single, fixed-sized page frame, a variable-sized base-limit 
  segment, or a set of memory locations. 
\<close>


(*<*)
(* Define some global variables to make Simpl/Complex proofs work *)
record 'g CleanQ_RB_State_vars = 
  RingRB_'  :: "nat CleanQ_RB_State"
(*>*)


(* ==================================================================================== *)
subsection \<open>State Lifting Function\<close>
(* ==================================================================================== *)

text \<open>
  The CleanQ RB model is a data refinement of the CleanQ List Model. We can define an
  interpretation function. That lifts the CleanQ RB model state into the CleanQ
  list model state by extracting a list of buffers as a subset of the ringbuffer. 
  We first define a function to convert the ringbuffer representation in to a list, which
  we use the nonzero_modulus locale to produce a list of indices into the bounded
  buffer ring and apply them to the \verb+ring+ function of the ringbuffer.
\<close>


text \<open>
  Then we use this conversion int he state lifting from the RB model to the list model.
\<close>

definition CleanQ_RB2List :: "'a CleanQ_RB_State  \<Rightarrow> 'a CleanQ_List_State"
  where "CleanQ_RB2List l = \<lparr> lSX = rSX l, lSY = rSY l, 
                               lTXY = CleanQ_RB_list (rTXY l), 
                               lTYX = CleanQ_RB_list (rTYX l) \<rparr>"



(* ==================================================================================== *)
subsection \<open>CleanQ RB Model Invariants\<close>
(* ==================================================================================== *)

text \<open>
  We now revisit the invariants of the CleanQ list model and specify additional invariants
  for the CleanQ Ring Buffer model. 
\<close>


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I1: Constant Union (Image)\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  The union of all sets is constant. We formulate this as an image for 
  \verb+CleanQ_List+ where we take the set of the transfer lists and apply the 
  union.
\<close>

fun I1_rb_img :: "'a CleanQ_RB_State \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1_rb_img rb K \<longleftrightarrow> ((rSX rb) \<union> (rSY rb) 
                                \<union> set (CleanQ_RB_list (rTXY rb)) 
                                \<union> set (CleanQ_RB_list (rTYX rb))) = K"

text \<open>
  We can show that the image of the invariant satisfies the list invariant I1 when
  we apply the lifting function \verb+CleanQ_RB2List+ to the model state. We prove
  this in the following lemma.
\<close>

lemma I1_rb_img_lift:
  "I1_rb_img R K = I1_list_img (CleanQ_RB2List R) K"
  unfolding CleanQ_RB2List_def by(simp)

lemma "I1_rb_img R K = I1 (CleanQ_List2Set (CleanQ_RB2List R)) K"
  unfolding CleanQ_RB2List_def CleanQ_List2Set_def by(simp)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I2: Pairwise Empty (Image)\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
 All pairwise intersections are empty. Again, we formulate this as an image for
 \verb+CleanQ_RB+ by extracting the list of buffers from the ring.
\<close>

fun I2_rb_img :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I2_rb_img rb \<longleftrightarrow> rSX rb \<inter> rSY rb = {} 
           \<and> rSX rb \<inter> set (CleanQ_RB_list (rTXY rb)) = {} 
           \<and> rSX rb \<inter> set (CleanQ_RB_list (rTYX rb)) = {} 
           \<and> rSY rb \<inter> set (CleanQ_RB_list (rTXY rb)) = {} 
           \<and> rSY rb \<inter> set (CleanQ_RB_list (rTYX rb)) = {} 
           \<and> set (CleanQ_RB_list (rTXY rb)) \<inter> set (CleanQ_RB_list (rTYX rb)) = {}"


text \<open>
  Finally, we can show that the image of the Invariant I2 is equivalent to the list 
  version of this invariant, when we lift the CleanQ RB State to the CleanQ List State. 
  We prove this in the following lemma:
\<close>

lemma I2_rb_img_lift:
  "I2_rb_img R = I2_list_img (CleanQ_RB2List R)"
  unfolding CleanQ_RB2List_def by(simp)


lemma "I2_rb_img R = I2 (CleanQ_List2Set (CleanQ_RB2List R))"
  unfolding CleanQ_RB2List_def CleanQ_List2Set_def by(simp)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I3: Distinct Transferlists\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  Next we provide an interpretation of the I3 invariant in the ring buffer representation. 
\<close>

fun I3_rb_img :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I3_rb_img st_list \<longleftrightarrow> distinct (CleanQ_RB_list (rTXY st_list)) 
                             \<and> distinct (CleanQ_RB_list (rTYX st_list))"


lemma I3_rb_img_lift:
  "I3_rb_img R = I3 (CleanQ_RB2List R)"
  unfolding CleanQ_RB2List_def by(simp)


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>All CleanQ RB Invariants\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We combine all invariants for the abstract CleanQ RB model and define the unified 
  predicate \verb+CleanQ_RB_Invariants+.
\<close>

fun CleanQ_RB_Invariants :: "'a set \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> bool"
  where "CleanQ_RB_Invariants K rb \<longleftrightarrow> I1_rb_img rb K \<and> I2_rb_img rb \<and> I3_rb_img rb"


text \<open>
  Finally, we can show that when the CleanQ RB invariants are satisfied, this also
  satisfies the set invariants.
\<close>

lemma CleanQ_RB_Invariants_List_Invariants:
  "CleanQ_RB_Invariants K L \<Longrightarrow> CleanQ_List_Invariants K (CleanQ_RB2List L)"
  unfolding CleanQ_RB2List_def by simp


(* ==================================================================================== *)
subsection \<open>State Transition Operations\<close>
(* ==================================================================================== *)

text \<open>
  We now formulate the state transition operations in terms of the CleanQ RB model
  state. Again, the two agents can, independently from each other, perform one of 
  two operations, \verb+enqueue+ and \verb+dequeue+,  which trigger an ownership 
  transfer of buffer elements.  
\<close>

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Enqueue Operation\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  The \verb+enqueue+ operation is analogous to the List operations except that the elements
  are written into a slot in the descriptor ring and then the pointers adapted accordingly. 
\<close>

definition CleanQ_RB_enq_x :: "'a \<Rightarrow> 'a CleanQ_RB_State  \<Rightarrow> 'a CleanQ_RB_State"
  where "CleanQ_RB_enq_x b rb = rb \<lparr> rSX := (rSX rb) - {b}, rTXY := rb_enq b (rTXY rb) \<rparr>"

definition CleanQ_RB_enq_y :: "'a \<Rightarrow> 'a CleanQ_RB_State  \<Rightarrow> 'a CleanQ_RB_State"
  where "CleanQ_RB_enq_y b rb = rb \<lparr> rSY := (rSY rb) - {b}, rTYX := rb_enq b (rTYX rb) \<rparr>"



lemma 
  assumes notfull : "\<not> rb_full rb" and pos: "i = (head rb)"
  shows "(ring (rb_enq b rb)) i = b"
  using notfull pos unfolding rb_enq_def by(simp)


lemma
  assumes notfull : "\<not> rb_full rb" and dist: "b \<notin> set (CleanQ_RB_list rb)"
  shows "set (CleanQ_RB_list rb) \<subset> set (CleanQ_RB_list (rb_enq b rb))"
  using notfull dist unfolding rb_enq_def CleanQ_RB_list_def 
  apply(simp)
  
  
  sorry
(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Dequeue Operation\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  The \verb+dequeue+ operation is analogous to the List operations except that the elements
  are read from a slot in the descriptor ring and then the pointers adapted accordingly. 
\<close>

definition CleanQ_RB_deq_x :: "'a CleanQ_RB_State  \<Rightarrow> 'a CleanQ_RB_State"
  where "CleanQ_RB_deq_x rb = (let (b, rest) = rb_deq(rTYX rb) in rb \<lparr> rSY := (rSY rb) \<union> {b}, rTYX := rest \<rparr>)"

definition CleanQ_RB_deq_y :: "'a CleanQ_RB_State  \<Rightarrow> 'a CleanQ_RB_State"
  where "CleanQ_RB_deq_y rb = (let (b, rest) = rb_deq(rTXY rb) in rb \<lparr> rSY := (rSY rb) \<union> {b}, rTXY := rest \<rparr>)"


(* ==================================================================================== *)
subsection \<open>Pre- and post- conditions\<close>
(* ==================================================================================== *)


definition CleanQ_RB_enq_x_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_RB_State, 'a CleanQ_RB_State) Semantic.xstate set"
  where "CleanQ_RB_enq_x_pre K b =  Semantic.Normal ` {rb. I1_rb_img rb K \<and> I2_rb_img rb \<and> I3_rb_img rb \<and> b \<in> rSX rb }"

definition CleanQ_RB_enq_y_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_RB_State, 'a CleanQ_RB_State) Semantic.xstate set"
  where "CleanQ_RB_enq_y_pre K b = Semantic.Normal ` {rb. I1_rb_img rb K \<and> I2_rb_img rb \<and> I3_rb_img rb \<and> b \<in> rSY rb}"

definition CleanQ_RB_deq_x_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_RB_State, 'a CleanQ_RB_State) Semantic.xstate set"        
  where "CleanQ_RB_deq_x_pre K buf = Semantic.Normal ` {rb. I1_rb_img rb K \<and> I2_rb_img rb \<and> I3_rb_img rb \<and>
                                                        CleanQ_RB_list  (rTYX rb) \<noteq> [] \<and> buf = ring (rTYX rb) (tail (rTYX rb))}"
definition CleanQ_RB_deq_y_pre :: "'a set \<Rightarrow> 'a \<Rightarrow> ('a CleanQ_RB_State, 'a CleanQ_RB_State) Semantic.xstate set"        
  where "CleanQ_RB_deq_y_pre K buf = Semantic.Normal ` {rb. I1_rb_img rb K \<and> I2_rb_img rb \<and> I3_rb_img rb \<and>
                                                        CleanQ_RB_list  (rTXY rb) \<noteq> [] \<and> buf = ring (rTXY rb) (tail (rTXY rb))}"

(*


lemma 
 assumes notfull : "\<not> rb_full rb"  and  pos: "i = (head rb)"
   shows "CleanQ_RB_list (rb_enq b rb) = (CleanQ_RB_list rb) @ [b]"
  unfolding CleanQ_RB_list_def rb_enq_def 
proof (simp)

  have "map ((ring rb)(head rb := b))
     (nonzero_modulus.list_between (size rb) (tail rb)
       (Suc (head rb) mod size rb)) =
     map  ((ring rb)(head rb := b))
     (nonzero_modulus.list_between (size rb) (tail rb)
       (head rb)) @
    []"
    apply(simp) 
    



qed
  


lemma CleanQ_RB_enq_x_equal :
  assumes notfull : "\<not> rb_full (rTXY rb)"
    shows "CleanQ_RB2List (CleanQ_RB_enq_x b rb) = CleanQ_List_enq_x b (CleanQ_RB2List rb)"
  unfolding CleanQ_RB2List_def CleanQ_RB_enq_x_def CleanQ_List_enq_x_def rb_enq_def CleanQ_RB_list_def
  apply(simp)

(*

text \<open>
  The third refinement is trying to get as close to the C implementation as possible.
  The two transfer queues are modeled as \verb+CleanQ_RB+. Two of these are combined
  to a \verb+CleanQ_QP+ which consists of an RX and TX queue. The full state of the
  system is compromised of two queue pairs and modeled in the \verb+CleanQ_RB_State+
  recrod. Ther are two queue pairs; one for the client and the other one for the server.
  The TX queue ring buffer of the client is the RX queue ring buffer of the server and 
  the RX queue ring buffer of the client is the TX queue ring buffer of the sever. While
  these are the same, each of these queue records has their own position in the ring buffer.
  In total there are 4 position pointers in to the two Ring buffers. The SX and TX
  sets are still the same as in the abstract model since we can not make any statement
  about the sets owned by each of the sides. 
\<close>

definition dir_rx :: nat
  where "dir_rx = 1"

definition dir_tx :: nat
  where "dir_tx = 2"

text \<open>Single queue. corresponds to \verb+ffq_queue+.\<close>
record 'a CleanQ_RB =
  ring :: "nat \<Rightarrow> 'a"
  pos :: nat
  direction :: nat
  size :: nat

text \<open>A queue pair. corresponds to \verb+ffq_qp+.\<close>
record 'a CleanQ_QP =
  rx :: "'a CleanQ_RB"
  tx :: "'a CleanQ_RB"

text \<open>The full state. corresponds to the whole program state.\<close>
record 'a CleanQ_RB_State =
  qTXY :: "'a CleanQ_QP"
  qTYX :: "'a CleanQ_QP"
  SX :: "'a set"
  SY :: "'a set"


(* Need modular intervals to specify ring buffer properties *)
(*<*)
locale modulus = nonzero_modulus +
  assumes fixN: "N = 64"
begin
(*>*)
(* ==================================================================================== *)
subsection \<open>CleanQ Abstract Ring Buffer Model Invariants\<close>
(* ==================================================================================== *)

text \<open>Helper definitions to define invariants.\<close>
text \<open>Get a list of all the entries between two positions in the ring buffer. We extract
      an interval from a to b in a ring buffer i.e. if we want to extract from entry 5 to 
      1 in a ring of size 6, this will return the entries 5,6, and 1. \<close>
definition slice :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
  where "slice buf s e = [buf ((s+i) mod N). i <- [0..< e \<ominus> s]]"

text \<open>Get a list of the entries fro the XY direction.\<close>
definition slice_xy :: "'a CleanQ_RB_State \<Rightarrow> 'a list"
  where "slice_xy st = slice (ring (tx (qTXY st))) (pos (rx (qTYX st))) (pos (tx (qTXY st)))"

text \<open>Get a list of the entries fro the YX direction.\<close>
definition slice_yx :: "'a CleanQ_RB_State \<Rightarrow> 'a list"
  where "slice_yx st = slice (ring (tx (qTYX st))) (pos (rx (qTXY st))) (pos (tx (qTYX st)))"

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>Images of the previously defined invariants\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>Definition of I1 on the Ring buffer model: The union of all sets is constant.\<close>
fun I1_img :: "'a CleanQ_RB_State \<Rightarrow> 'a set \<Rightarrow> bool"
  where "I1_img rb K \<longleftrightarrow> ((SX rb) \<union> (SY rb) \<union> (set (slice_xy rb)) \<union> (set (slice_yx rb))) = K"

text \<open>Definition of I2 on the Ring buffer model: No Double Presenc.\<close>
fun I2_img :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I2_img rb \<longleftrightarrow>
    SX rb \<inter> SY rb = {} \<and> SX rb \<inter> set (slice_xy rb) = {} \<and> SX rb \<inter> set (slice_yx rb) = {} \<and> 
    SY rb \<inter> set (slice_xy rb) = {} \<and> SY rb \<inter> set (slice_yx rb) = {} \<and> 
    set (slice_xy rb) \<inter> set (slice_yx rb) = {}"

text \<open>Definition of I3 on the Ring buffer model: No duplicates in list.\<close>
fun I3_img :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I3_img rb \<longleftrightarrow> distinct ((slice_xy rb) @ (slice_yx rb))"


(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I4: The ring buffers are the same\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  In order for the model to work with the C code, there needs to be shared state
  similar to the C code. For an IPC queue there are normally two shared memory
  regions which are used as ring buffers. In this proof the client TX ring buffer
  is the same as the server RX ring buffer and the server TX ring buffer is the
  same as the client RX ring buffer.
\<close>
fun I4 :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I4 st \<longleftrightarrow> (ring (tx (qTXY st))) = (ring (rx (qTYX st))) \<and>
                   (ring (tx (qTYX st))) = (ring (rx (qTXY st)))"

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>I5: Ring buffers are in a valid state\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  A queue pair is in a valid state if the RX and TX queues have the right direction,
  The sizes of the ring buffers are fixed to some N and the position pointers are
  less than that N. This needs to be true for both queue pairs in \verb+CleanQ_RB_State+. 
\<close>
fun I5 :: "'a CleanQ_RB_State \<Rightarrow> bool"
  where "I5 st \<longleftrightarrow> (direction (tx (qTXY st))) = dir_tx \<and>
                   (direction (tx (qTYX st))) = dir_tx \<and>
                   (direction (rx (qTXY st))) = dir_rx \<and>
                   (direction (rx (qTYX st))) = dir_rx \<and>
                   size (tx (qTYX st)) = N \<and>
                   size (tx (qTXY st)) = N \<and>
                   size (rx (qTYX st)) = N \<and>
                   size (rx (qTXY st)) = N \<and>
                   pos (tx (qTYX st)) < N \<and>
                   pos (tx (qTXY st)) < N \<and>
                   pos (rx (qTYX st)) < N \<and>
                   pos (rx (qTXY st)) < N "

(*Don't think there is an ordering invariant since there are only 2 pointers into the ring buffer *)

(* ------------------------------------------------------------------------------------ *)
subsubsection \<open>CleanQ List Invariants\<close>
(* ------------------------------------------------------------------------------------ *)

text \<open>
  We combine all invariants for the abstract CleanQ list model and define the predicate 
  \verb+CleanQ_List_Invariants+.
\<close>

fun CleanQ_RB_Invariants :: "'a set \<Rightarrow> 'a CleanQ_RB_State \<Rightarrow> bool"
  where "CleanQ_RB_Invariants K rb \<longleftrightarrow> I1_img rb K \<and> I2_img rb \<and> I3_img rb \<and> I4 rb \<and> I5 rb"
*)*)

end (*Modulus end *)
