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



(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CleanQ_SimpleQ
imports "../autocorres/autocorres/AutoCorres"
begin

external_file "CleanQ_SimpleQ.c"

install_C_file "CleanQ_SimpleQ.c"
autocorres "CleanQ_SimpleQ.c"

context CleanQ_SimpleQ begin

(* Ring Buffer C parser output. *)
thm rb_init_body_def
thm rb_can_enq_body_def
thm rb_enq_body_def
thm rb_can_deq_body_def
thm rb_deq_body_def

(* SimpleQ C parser output. *)

thm simpleq_enq_body_def
thm simpleq_deq_body_def
thm simpleq_enq_x_body_def
thm simpleq_enq_y_body_def
thm simpleq_deq_x_body_def
thm simpleq_deq_y_body_def

(* SimpleQ Init C parser output. *)
thm init_x_body_def
thm init_y_body_def
thm init_queue_body_def


end
end
