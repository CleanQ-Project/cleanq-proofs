/*
 * Copyright (c) 2020, ETH Zurich
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice, this
 *    list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#ifdef COMPILE
#define _GNU_SOURCE
#include <assert.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#else
#define NULL ((void*)0)
#endif

///< this is the architecture cache line size in bytes
#define ARCH_CACHELINE_SIZE_BYTES 64

///< this is the architecture cache line size in machine words (8 bytes)
#define ARCH_CACHELINE_SIZE_WORDS 8

///< this is the default size in buffer for this example
#define CONFIG_DEFAULT_BUFFER_SIZE 4096

///< this is the default queue size
#define CONFIG_DEFAULT_QUEUE_SIZE 4

///< this is the number of buffers agent X does enqueue at the beginning
#define CONFIG_DEFAULT_ENQ_BUFS 8

///< this is the total number of buffers (K)
#define CONFIG_DEFAULT_NUM_BUFS 128

/* a few basic type definitions */
typedef unsigned long u64_t;
typedef unsigned int u32_t;
typedef unsigned short u16_t;
typedef unsigned char u8_t;

/* error types */

///< the operation succeeded
#define ERR_OK 0

///< the queue was full
#define ERR_QUEUE_FULL -1

///< the queue was emtpy
#define ERR_QUEUE_EMTPY -2

///< no owned buffers
#define ERR_NO_BUFFERS -3

/*
 * ======================================================================================
 * Ring Buffer Implementation
 * ======================================================================================
 */

///< this defines an element in the descriptor ring.
struct buffer {
    u64_t region;
    u64_t offset;
    u64_t length;
    u64_t valid_offset;
    u64_t valid_length;
    u64_t flags;
#ifdef COMPILE
    struct buffer* nextfree;
    struct buffer* self;
#endif
};

///< this defines a ring buffer
struct rb {
    ///< this is the head pointer of the ring buffer
    u32_t head;

    ///< this is the tail pointer of the ring buffer
    u32_t tail;

    ///< this is the size of the ring buffer
    u32_t size;

    ///< this is the memory holding the ring buffer
    struct buffer* ring;
};

/*
 * --------------------------------------------------------------------------------------
 * Initialization
 * --------------------------------------------------------------------------------------
 */

static void rb_init(struct rb* rb, struct buffer* ring, u64_t size)
{
#ifdef COMPILE
    printf("RB init [%p | %lu ]\n", ring, size);
#endif
    rb->ring = ring;
    rb->size = size;
    rb->head = 0;
    rb->tail = 0;
}

/*
 * --------------------------------------------------------------------------------------
 * Enqueue Operation
 * --------------------------------------------------------------------------------------
 */

///< function to check if there is space to enqueue a new element
static int rb_can_enq(struct rb* rb)
{
    return (((rb->head + 1) % rb->size) != rb->tail);
}

///< enqueue function
static int rb_enq(struct rb* rb, struct buffer slot)
{
    if (!rb_can_enq(rb)) {
        return ERR_QUEUE_FULL;
    }

    rb->ring[rb->head] = slot;
    rb->head = (rb->head + 1) % rb->size;

    return ERR_OK;
}

/*
 * PRE:
 *
 * I_size: size0 == rb->size             # size is invariant
 * I_ring: ring0 == rb->ring             # ring pointer is invariant
 *
 * tail0 = rb->tail
 * head0 = rb->head
 */
static int rb_enq_unfolded(struct rb* rb, struct buffer slot)
{
    /*
     * E1:
     *
     * I_size: size0 == rb->size             # size is invariant
     * I_ring: ring0 == rb->ring             # ring pointer is invariant
     */
    u32_t head = rb->head;

    /*
     * E2:
     *
     * head == head0 == rb->head;            # the other side does not modify head, we haven't changed
     *
     * I_size: size0 == rb->size             # size is invariant
     * I_ring: ring0 == rb->ring             # ring pointer is invariant
     */
    u32_t tail = rb->tail;

    /*
     * E3:
     *
     * head == head0 == rb->head;            # the other side does not modify head, we haven't changed
     *
     * (tail + delta) mod size = rb->tail    # rb->tail could have advanced already
     *
     * I_size: size0 == rb->size             # size is invariant
     * I_ring: ring0 == rb->ring             # ring pointer is invariant
     */
    u32_t size = rb->size;

    /*
     * E4:
     *
     * head == head0 == rb->head;            # the other side does not modify head, we haven't changed
     *
     * (tail + delta) mod size = rb->tail    # rb->tail could have advanced already (other thread)
     *
     * size = rb->size                       # size is invariant
     *
     * I_size: size0 == rb->size
     * I_ring: ring0 == rb->ring
     */
    if ((((head + 1) % size) == tail)) {
        /*
         * E5:
         *
         * head == head0 == rb->head;            # the other side does not modify head, we haven't changed
         *
         * (tail + delta) mod size = rb->tail    # rb->tail could have advanced already (other thread)
         *
         * size = rb->size                       # size is invariant
         *
         * I_size: size0 == rb->size
         * I_ring: ring0 == rb->ring
         *
         *
         * ((head + 1) mod size == tail)        # with the local variables, this holds
         *
         * # using the value of tail wrt rb->tail, which may have increased by delta
         * ((head + 1) mod size == (tail + delta) mod size
         *
         * # so the equaly only holds if delta is zero.  should not be a problem here...,
         * delta > 0 --> (head + 1 mod size) != rb->tail
         *
         */
        return ERR_QUEUE_FULL;

    } else {

        /*
         * E6:
         *
         * head == head0 == rb->head;            # the other side does not modify head, we haven't changed
         *
         * (tail + delta) mod size = rb->tail    # rb->tail could have advanced already (other thread)
         *
         * size = rb->size                       # size is invariant
         *
         * I_size: size0 == rb->size
         * I_ring: ring0 == rb->ring
         *
         *
         * ((head + 1) mod size != tail)        # with the local variables, this holds
         *
         * # using the value of tail wrt rb->tail, which may have increased, this must still hold
         * ((head + 1) mod size != (tail + delta) mod size
         *
         * # there must be no delta, which makes this true!   its tail <= head  (mod size)
         * delta < (head - tail) mod size
         *
         */
        u32_t head2 = rb->head;

        /*
         * E7:
         *
         * head2 == head == head0 == rb->head;   # the other side does not modify head, we haven't changed
         *
         * (tail + delta) mod size = rb->tail    # rb->tail could have advanced already (other thread)
         *
         * size = rb->size                       # size is invariant
         *
         * I_size: size0 == rb->size
         * I_ring: ring0 == rb->ring
         *
         *
         * ((head + 1) mod size != tail)        # with the local variables, this holds
         *
         * # using the value of tail wrt rb->tail, which may have increased, this must still hold
         * ((head + 1) mod size != (tail + delta) mod size
         */
        struct buffer* ring = rb->ring;

        /*
         * E8:
         *
         * head2 == head == head0 == rb->head;   # the other side does not modify head, we haven't changed
         *
         * (tail + delta) mod size = rb->tail    # rb->tail could have advanced already (other thread)
         *
         * size = rb->size                       # size is invariant
         * ring = rb->ring                       # the ring is invariant
         *
         * I_size: size0 == rb->size
         * I_ring: ring0 == rb->ring
         *
         *
         * ((head + 1) mod size != tail)        # with the local variables, this holds
         *
         * # using the value of tail wrt rb->tail, which may have increased, this must still hold
         * ((head + 1) mod size != (tail + delta) mod size
         */
        ring[head2].region = slot.region;

        /*
         * E9:
         *
         * head2 == head == head0 == rb->head;   # the other side does not modify head, we haven't changed
         *
         * (tail + delta) mod size = rb->tail    # rb->tail could have advanced already (other thread)
         *
         * size = rb->size                       # size is invariant
         * ring = rb->ring                       # the ring is invariant
         *
         * I_size: size0 == rb->size
         * I_ring: ring0 == rb->ring
         *
         *
         * ((head + 1) mod size != tail)        # with the local variables, this holds
         *
         * # using the value of tail wrt rb->tail, which may have increased, this must still hold
         * ((head + 1) mod size != (tail + delta) mod size
         */
        ring[head2].offset = slot.offset;

        /*
         * E10:
         *
         * head2 == head == head0 == rb->head;   # the other side does not modify head, we haven't changed
         *
         * (tail + delta) mod size = rb->tail    # rb->tail could have advanced already (other thread)
         *
         * size = rb->size                       # size is invariant
         * ring = rb->ring                       # the ring is invariant
         *
         * I_size: size0 == rb->size
         * I_ring: ring0 == rb->ring
         *
         *
         * ((head + 1) mod size != tail)        # with the local variables, this holds
         *
         * # using the value of tail wrt rb->tail, which may have increased, this must still hold
         * ((head + 1) mod size != (tail + delta) mod size
         */
        ring[head2].length = slot.length;

        /*
         * E11:
         *
         * head2 == head == head0 == rb->head;   # the other side does not modify head, we haven't changed
         *
         * (tail + delta) mod size = rb->tail    # rb->tail could have advanced already (other thread)
         *
         * size = rb->size                       # size is invariant
         * ring = rb->ring                       # the ring is invariant
         *
         * I_size: size0 == rb->size
         * I_ring: ring0 == rb->ring
         *
         *
         * ((head + 1) mod size != tail)        # with the local variables, this holds
         *
         * # using the value of tail wrt rb->tail, which may have increased, this must still hold
         * ((head + 1) mod size != (tail + delta) mod size
         */
        ring[head2].valid_offset = slot.valid_offset;

        /*
         * E12:
         *
         * head2 == head == head0 == rb->head;   # the other side does not modify head, we haven't changed
         *
         * (tail + delta) mod size = rb->tail    # rb->tail could have advanced already (other thread)
         *
         * size = rb->size                       # size is invariant
         * ring = rb->ring                       # the ring is invariant
         *
         * I_size: size0 == rb->size
         * I_ring: ring0 == rb->ring
         *
         *
         * ((head + 1) mod size != tail)        # with the local variables, this holds
         *
         * # using the value of tail wrt rb->tail, which may have increased, this must still hold
         * ((head + 1) mod size != (tail + delta) mod size
         */
        ring[head2].valid_length = slot.valid_length;

        /*
         * E13:
         *
         * head2 == head == head0 == rb->head;   # the other side does not modify head, we haven't changed
         *
         * (tail + delta) mod size = rb->tail    # rb->tail could have advanced already (other thread)
         *
         * size = rb->size                       # size is invariant
         * ring = rb->ring                       # the ring is invariant
         *
         * I_size: size0 == rb->size
         * I_ring: ring0 == rb->ring
         *
         *
         * ((head + 1) mod size != tail)        # with the local variables, this holds
         *
         * # using the value of tail wrt rb->tail, which may have increased, this must still hold
         * ((head + 1) mod size != (tail + delta) mod size
         */
        ring[head2].flags = slot.flags;

        /*
         * E14:
         *
         * head2 == head == head0 == rb->head;   # the other side does not modify head, we haven't changed
         *
         * (tail + delta) mod size = rb->tail    # rb->tail could have advanced already (other thread)
         *
         * size = rb->size                       # size is invariant
         * ring = rb->ring                       # the ring is invariant
         *
         * I_size: size0 == rb->size
         * I_ring: ring0 == rb->ring
         *
         *
         * ((head + 1) mod size != tail)        # with the local variables, this holds
         *
         * # using the value of tail wrt rb->tail, which may have increased, this must still hold
         * ((head + 1) mod size != (tail + delta) mod size
         */
        u32_t head3 = rb->head;

        /*
         * E15:
         *
         * head3 == head2 == head == head0 == rb->head;   # the other side does not modify head, we haven't changed
         *
         * (tail + delta) mod size = rb->tail    # rb->tail could have advanced already (other thread)
         *
         * size = rb->size                       # size is invariant
         * ring = rb->ring                       # the ring is invariant
         *
         * I_size: size0 == rb->size
         * I_ring: ring0 == rb->ring
         *
         *
         * ((head + 1) mod size != tail)        # with the local variables, this holds
         *
         * # using the value of tail wrt rb->tail, which may have increased, this must still hold
         * ((head + 1) mod size != (tail + delta) mod size
         */
        u32_t size3 = rb->size;

        /*
         * E16:
         *
         * head3 == head2 == head == head0 == rb->head;   # the other side does not modify head, we haven't changed
         *
         * (tail + delta) mod size = rb->tail    # rb->tail could have advanced already (other thread)
         *
         * size3 == size = rb->size                       # size is invariant
         * ring = rb->ring                       # the ring is invariant
         *
         * I_size: size0 == rb->size
         * I_ring: ring0 == rb->ring
         *
         *
         * ((head + 1) mod size != tail)        # with the local variables, this holds
         *
         * # using the value of tail wrt rb->tail, which may have increased, this must still hold
         * ((head + 1) mod size != (tail + delta) mod size
         */
        rb->head = (head3 + 1) % size3;

        /*
         * E17:
         *
         * head3 == head2 == head == head0   ;   # the other side does not modify head, we haven't changed
         * rb->head = (head3 + 1) mod size       # we increased the head pointer
         *
         * (tail + delta) mod size = rb->tail    # rb->tail could have advanced already (other thread)
         *
         * size = rb->size                       # size is invariant
         * ring = rb->ring                       # the ring is invariant
         *
         * I_size: size0 == rb->size
         * I_ring: ring0 == rb->ring
         *
         *
         * ((head + 1) mod size != tail)        # with the local variables, this holds
         * ((head3 + 1) mod size != tail)       # with local variables this holds
         * (rb->head != tail)                   # we bumped rb->head, so filling that in.
         *
         * # using the value of tail wrt rb->tail, which may have increased, this must still hold
         * ((head + 1) mod size != (tail + delta) mod size
         * rb->head != (tail + delta) mod size
         */
        return ERR_OK;
    }
}

/*
 * POST
 *
 * I_size: size0 == rb->size
 * I_ring: ring0 == rb->ring
 *
 * rb->tail = tail0 + delta
 * r == ERR_OK --> rb->head = head0 + 1 mod rb->size
 * r != ERR_OK --> rb->head = head0
 */

/*
 * --------------------------------------------------------------------------------------
 * Dequeue Operation
 * --------------------------------------------------------------------------------------
 */

///< function to check if there is an element to dequeue
static int rb_can_deq(struct rb* rb)
{
    return (rb->head != rb->tail);
}

///< the dequeue operation
static int rb_deq(struct rb* rb, struct buffer* ret)
{
    if (!rb_can_deq(rb)) {
        return ERR_QUEUE_EMTPY;
    }

    *ret = rb->ring[rb->tail];
    rb->tail = (rb->tail + 1) % rb->size;

    return ERR_OK;
}

/*
 * PRE:
 *
 * I_size: size0 == rb->size             # size is invariant
 * I_ring: ring0 == rb->ring             # ring pointer is invariant
 *
 * tail0 = rb->tail
 * head0 = rb->head
 */
static int rb_deq_unfolded(struct rb* rb, struct buffer* ret)
{
    /*
     * D1:
     *
     * I_size: size0 == rb->size             # size is invariant
     * I_ring: ring0 == rb->ring             # ring pointer is invariant
     */
    u32_t head = rb->head;

    /*
    * D2:
    *
    * (head + delta) mod size = rb->head     # rb->head could have advanced already
    *
    * I_size: size0 == rb->size              # size is invariant
    * I_ring: ring0 == rb->ring              # ring pointer is invariant
    */
    u32_t tail = rb->tail;

    /*
     * D3:
     *
     * tail == tail0 == rb->tail              # the other side does not modify tail
     *
     * (head + delta) mod size = rb->head     # rb->head could have advanced already
     *
     * I_size: size0 == rb->size              # size is invariant
     * I_ring: ring0 == rb->ring              # ring pointer is invariant
     */
    if ((head == tail)) {

        /*
        * D4:
        *
        * tail == tail0 == rb->tail              # the other side does not modify tail
        *
        * (head + delta) mod size = rb->head     # rb->head could have advanced already
        *
        * head == tail                           # this is true for the local variables
        *
        * (head + delta) mod size == tail        # using head+delta for rb->head
        *
        * # so in fact, this could turn to be false, however it's not a problem here...
        * delta > 0 --> (head + delta) mod size != tail
        *
        * I_size: size0 == rb->size              # size is invariant
        * I_ring: ring0 == rb->ring              # ring pointer is invariant
        */
        return ERR_QUEUE_EMTPY;
    } else {

        /*
         * D5:
         *
         * tail == tail0 == rb->tail              # the other side does not modify tail
         *
         * (head + delta) mod size = rb->head     # rb->head could have advanced already
         *
         * head != tail                           # this is true for the local variables
         *
         * (head + delta) mod size != tail        # this must always be true here.
         *
         * delta < (head - tail) mod size
         *
         * I_size: size0 == rb->size              # size is invariant
         * I_ring: ring0 == rb->ring              # ring pointer is invariant
         */

        u32_t tail1 = rb->tail;

        /*
         * D6:
         *
         * tail1 = tail == tail0 == rb->tail      # the other side does not modify tail
         *
         * (head + delta) mod size = rb->head     # rb->head could have advanced already
         *
         * head != tail                           # this is true for the local variables
         *
         * (head + delta) mod size != tail        # this must always be true here.
         *
         * delta < (head - tail) mod size
         *
         * I_size: size0 == rb->size              # size is invariant
         * I_ring: ring0 == rb->ring              # ring pointer is invariant
         */
        struct buffer* ring = rb->ring;

        /*
         * D7:
         *
         * ring = rb->ring                        # the ring pointer is invariant
         *
         * tail1 = tail == tail0 == rb->tail      # the other side does not modify tail
         *
         * (head + delta) mod size = rb->head     # rb->head could have advanced already
         *
         * head != tail                           # this is true for the local variables
         *
         * (head + delta) mod size != tail        # this must always be true here.
         *
         * delta < (head - tail) mod size
         *
         * I_size: size0 == rb->size              # size is invariant
         * I_ring: ring0 == rb->ring              # ring pointer is invariant
         */
        ret->region = ring[tail1].region;

        /*
         * D8:
         *
         * ring = rb->ring                        # the ring pointer is invariant
         *
         * tail1 = tail == tail0 == rb->tail      # the other side does not modify tail
         *
         * (head + delta) mod size = rb->head     # rb->head could have advanced already
         *
         * head != tail                           # this is true for the local variables
         *
         * (head + delta) mod size != tail        # this must always be true here.
         *
         * delta < (head - tail) mod size
         *
         * I_size: size0 == rb->size              # size is invariant
         * I_ring: ring0 == rb->ring              # ring pointer is invariant
         */
        ret->offset = ring[tail1].offset;

        /*
         * D9:
         *
         * ring = rb->ring                        # the ring pointer is invariant
         *
         * tail1 = tail == tail0 == rb->tail      # the other side does not modify tail
         *
         * (head + delta) mod size = rb->head     # rb->head could have advanced already
         *
         * head != tail                           # this is true for the local variables
         *
         * (head + delta) mod size != tail        # this must always be true here.
         *
         * delta < (head - tail) mod size
         *
         * I_size: size0 == rb->size              # size is invariant
         * I_ring: ring0 == rb->ring              # ring pointer is invariant
         */
        ret->length = ring[tail1].length;

        /*
         * D10:
         *
         * ring = rb->ring                        # the ring pointer is invariant
         *
         * tail1 = tail == tail0 == rb->tail      # the other side does not modify tail
         *
         * (head + delta) mod size = rb->head     # rb->head could have advanced already
         *
         * head != tail                           # this is true for the local variables
         *
         * (head + delta) mod size != tail        # this must always be true here.
         *
         * delta < (head - tail) mod size
         *
         * I_size: size0 == rb->size              # size is invariant
         * I_ring: ring0 == rb->ring              # ring pointer is invariant
         */
        ret->valid_offset = ring[tail1].valid_offset;

        /*
         * D11:
         *
         * ring = rb->ring                        # the ring pointer is invariant
         *
         * tail1 = tail == tail0 == rb->tail      # the other side does not modify tail
         *
         * (head + delta) mod size = rb->head     # rb->head could have advanced already
         *
         * head != tail                           # this is true for the local variables
         *
         * (head + delta) mod size != tail        # this must always be true here.
         *
         * delta < (head - tail) mod size
         *
         * I_size: size0 == rb->size              # size is invariant
         * I_ring: ring0 == rb->ring              # ring pointer is invariant
         */
        ret->valid_length = ring[tail1].valid_length;

        /*
         * D12:
         *
         * ring = rb->ring                        # the ring pointer is invariant
         *
         * tail1 = tail == tail0 == rb->tail      # the other side does not modify tail
         *
         * (head + delta) mod size = rb->head     # rb->head could have advanced already
         *
         * head != tail                           # this is true for the local variables
         *
         * (head + delta) mod size != tail        # this must always be true here.
         *
         * delta < (head - tail) mod size
         *
         * I_size: size0 == rb->size              # size is invariant
         * I_ring: ring0 == rb->ring              # ring pointer is invariant
         */
        ret->flags = ring[tail1].flags;

        /*
         * D13:
         *
         * ring = rb->ring                        # the ring pointer is invariant
         *
         * tail1 = tail == tail0 == rb->tail      # the other side does not modify tail
         *
         * (head + delta) mod size = rb->head     # rb->head could have advanced already
         *
         * head != tail                           # this is true for the local variables
         *
         * (head + delta) mod size != tail        # this must always be true here.
         *
         * delta < (head - tail) mod size
         *
         * I_size: size0 == rb->size              # size is invariant
         * I_ring: ring0 == rb->ring              # ring pointer is invariant
         */
        u32_t size = rb->size;

        /*
         * D14:
         *
         * ring = rb->ring                        # the ring pointer is invariant
         * size = rb->size                        # size is invariant
         *
         * tail1 = tail == tail0 == rb->tail      # the other side does not modify tail
         *
         * (head + delta) mod size = rb->head     # rb->head could have advanced already
         *
         * head != tail                           # this is true for the local variables
         *
         * (head + delta) mod size != tail        # this must always be true here.
         *
         * delta < (head - tail) mod size
         *
         * I_size: size0 == rb->size              # size is invariant
         * I_ring: ring0 == rb->ring              # ring pointer is invariant
         */
        u32_t tail2 = rb->tail;

        /*
         * D15:
         *
         * ring = rb->ring                        # the ring pointer is invariant
         * size = rb->size                        # size is invariant
         *
         * tail2 = tail1 = tail == tail0 == rb->tail      # the other side does not modify tail
         *
         * (head + delta) mod size = rb->head     # rb->head could have advanced already
         *
         * head != tail                           # this is true for the local variables
         *
         * (head + delta) mod size != tail        # this must always be true here.
         *
         * delta < (head - tail) mod size
         *
         * I_size: size0 == rb->size              # size is invariant
         * I_ring: ring0 == rb->ring              # ring pointer is invariant
         */
        rb->tail = (tail2 + 1) % size;

        /*
         * D7:
         *
         * ring = rb->ring                        # the ring pointer is invariant
         * size = rb->size                        # size is invariant
         *
         * tail1 = tail == tail0 == rb->tail      # the other side does not modify tail
         *
         * (head + delta) mod size = rb->head     # rb->head could have advanced already
         *
         * head != tail                           # this is true for the local variables
         *
         * (head + delta) mod size != tail        # this must always be true here.
         *
         * (head + delta) mod size != (tail + 1) mod size    # this must always be true here.
         * (head + delta) mod size != rb->tail    # this must always be true here.
         *
         * delta < (head - tail) mod size
         *
         * I_size: size0 == rb->size              # size is invariant
         * I_ring: ring0 == rb->ring              # ring pointer is invariant
         */
        return ERR_OK;
    }
}

/*
 * POST
 *
 * I_size: size0 == rb->size
 * I_ring: ring0 == rb->ring
 *
 * rb->head = head0 + delta
 * r == ERR_OK --> rb->tail = tail0 + 1 mod rb->size
 * r != ERR_OK --> rb->tail = tail0
 */

/*
 * ======================================================================================
 * The SimpleQ Queue System
 * ======================================================================================
 */

///< this is the simple queue model
struct simpleq {
    ///< this is the receiving side of the queue
    struct rb* rx;

    ///< this is the sending side of the queue
    struct rb* tx;

    ///< owned buffers by this endpoint
    struct buffer* owned;

    ///< endpoint name
    char* name;
};

static int simpleq_enq(struct simpleq* sq, struct buffer buf)
{
#ifdef COMPILE
    printf("%s - enqueue to [%u..%u / %u]\n", sq->name, sq->tx->tail, sq->tx->head, sq->tx->size);
#endif
    return rb_enq(sq->tx, buf);
}

static int simpleq_deq(struct simpleq* sq, struct buffer* buf)
{
#ifdef COMPILE
    printf("%s - dequeue from [%u..%u / %u]\n", sq->name, sq->rx->tail, sq->rx->head, sq->rx->size);
#endif
    return rb_deq(sq->rx, buf);
}

static struct rb rxy;
static struct rb ryx;
static struct simpleq sqx;
static struct simpleq sqy;
static struct buffer* K_bufs;

static int simpleq_enq_x(void)
{
    if (sqx.owned == NULL) {
#ifdef COMPILE
        printf("%s - no available buffers\n", sqx.name);
#endif
        return ERR_NO_BUFFERS;
    }

    struct buffer* buf = sqx.owned;

#ifdef COMPILE
    buf->nextfree = sqx.owned;
    printf("%s - sending [%lx..%lx]\n", sqx.name, buf->offset, buf->offset + buf->length - 1);
#endif
    if (simpleq_enq(&sqx, *buf) != ERR_OK) {
#ifdef COMPILE
        printf("%s - enqueue failed\n", sqx.name);
        buf->nextfree = sqx.owned;
#endif

        sqx.owned = buf;
        return ERR_QUEUE_FULL;
    }
    return ERR_OK;
}

static int simpleq_enq_y(void)
{
    if (sqy.owned == NULL) {
#ifdef COMPILE
        printf("%s - no available buffers\n", sqy.name);
#endif
        return ERR_NO_BUFFERS;
    }

    struct buffer* buf = sqy.owned;

#ifdef COMPILE
    sqy.owned = buf->nextfree;
    printf("%s - sending [%lx..%lx]\n", sqy.name, buf->offset, buf->offset + buf->length - 1);
#endif

    if (simpleq_enq(&sqy, *buf) != ERR_OK) {
#ifdef COMPILE
        printf("%s - enqueue failed\n", sqy.name);
        buf->nextfree = sqy.owned;
#endif
        sqy.owned = buf;
        return ERR_QUEUE_FULL;
    }

    return ERR_OK;
}

static struct buffer deq_x_buf;
static int simpleq_deq_x(void)
{
    if (simpleq_deq(&sqx, &deq_x_buf) != ERR_OK) {
#ifdef COMPILE
        printf("%s - dequeue failed\n", sqx.name);
#endif
        return ERR_QUEUE_EMTPY;
    }

#ifdef COMPILE
    printf("%s - received [%lx..%lx]\n", sqx.name, deq_x_buf.offset, deq_x_buf.offset + deq_x_buf.length - 1);
    deq_x_buf.self->nextfree = sqx.owned;
    sqx.owned = deq_x_buf.self;
#endif

    return ERR_OK;
}

static struct buffer deq_y_buf;
static int simpleq_deq_y(void)
{

    if (simpleq_deq(&sqy, &deq_y_buf) != ERR_OK) {
#ifdef COMPILE
        printf("%s - dequeue failed\n", sqy.name);
#endif
        return ERR_QUEUE_EMTPY;
    }

#ifdef COMPILE
    printf("%s - received [%lx..%lx]\n", sqy.name, deq_y_buf.offset, deq_y_buf.offset + deq_y_buf.length - 1);
    deq_y_buf.self->nextfree = sqy.owned;
    sqy.owned = deq_y_buf.self;
#endif
    return ERR_OK;
}

/*
 * ======================================================================================
 * Initialization
 * ======================================================================================
 */

static void init_x(struct rb* rxy, struct buffer* txy, u64_t txy_size,
    struct rb* ryx, struct buffer* tyx, u64_t tyx_size)
{
    sqx.tx = rxy;
    sqx.rx = ryx;
    rb_init(sqx.tx, txy, txy_size);
    rb_init(sqx.rx, tyx, tyx_size);
#ifdef COMPILE
    sqx.name = "[X]";
#endif
}

static void init_y(struct rb* rxy, struct buffer* txy, u64_t txy_size,
    struct rb* ryx, struct buffer* tyx, u64_t tyx_size)
{
    sqy.tx = ryx;
    sqy.rx = rxy;
    rb_init(sqy.tx, tyx, tyx_size);
    rb_init(sqy.rx, txy, txy_size);
#ifdef COMPILE
    sqy.name = "[Y]";
#endif
}

static int init_queue(struct buffer* txy, u64_t txy_size,
    struct buffer* tyx, u64_t tyx_size, u64_t nbufs)
{
#ifdef COMPILE
    printf("Initializing Queue...\n");
#endif

    init_x(&rxy, txy, txy_size, &ryx, tyx, tyx_size);
    init_y(&rxy, txy, txy_size, &ryx, tyx, tyx_size);

    if (K_bufs == NULL) {
        return ERR_NO_BUFFERS;
    }

    for (u64_t i = 0; i < nbufs; i++) {
        K_bufs[i].offset = (i + 1) * CONFIG_DEFAULT_BUFFER_SIZE;
        K_bufs[i].length = CONFIG_DEFAULT_BUFFER_SIZE;
#ifdef COMPILE
        K_bufs[i].self = &K_bufs[i];
        K_bufs[i].nextfree = sqx.owned;
#endif
        sqx.owned = &K_bufs[i];
    }

    return ERR_OK;
}

/*
 * ======================================================================================
 * Runtime
 * ======================================================================================
 */

#ifdef COMPILE

static void* agent_x(void* arg)
{
    for (u64_t i = 0; i < CONFIG_DEFAULT_ENQ_BUFS; i++) {
        simpleq_enq_x();
    }

    for (int i = 0; i < 20; i++) {
        simpleq_deq_x();
        simpleq_enq_x();
    }

    for (int i = 0; i < 20; i++) {
        simpleq_deq_x();
        pthread_yield();
    }

    for (int i = 0; i < 20; i++) {
        while (!simpleq_deq_x())
            ;
        pthread_yield();
        while (!simpleq_deq_x())
            ;
        pthread_yield();
        while (!simpleq_deq_x())
            ;
    }

    u64_t count = 0;
    struct buffer* buf = sqx.owned;
    while (buf) {
        count++;
        buf = buf->nextfree;
    }

    printf("Received back %lu bufs\n", count);

    return arg;
}

static void* agent_y(void* arg)
{
    //while(true) {
    for (int i = 0; i < 20; i++) {
        simpleq_deq_y();
        simpleq_enq_y();
    }

    while (sqy.owned != NULL) {
        while (!simpleq_deq_y())
            ;
        simpleq_enq_y();
    }

    return arg;
}

int main(int argc, char** argv)
{
    int ret = 0;

    for (int i = 0; i < argc; i++) {
        printf("%s ", argv[i]);
    }
    printf("\n");

    K_bufs = calloc(CONFIG_DEFAULT_NUM_BUFS, sizeof(struct buffer));
    if (K_bufs == NULL) {
        printf("Failed to allocate memory. exiting...\n");
        return -1;
    }
    struct buffer* txy = calloc(CONFIG_DEFAULT_QUEUE_SIZE, sizeof(struct buffer));
    if (txy == NULL) {
        printf("Failed to allocate memory. exiting...\n");
        return -1;
    }

    struct buffer* tyx = calloc(CONFIG_DEFAULT_QUEUE_SIZE, sizeof(struct buffer));
    if (tyx == NULL) {
        printf("Failed to allocate memory. exiting...\n");
        return -1;
    }

    ret = init_queue(txy, CONFIG_DEFAULT_QUEUE_SIZE, tyx, CONFIG_DEFAULT_QUEUE_SIZE,
        CONFIG_DEFAULT_NUM_BUFS);
    if (ret != ERR_OK) {
        printf("FAILED TO INITALIZE THE QUEUE\n");
        return -1;
    }

    printf("Starting agents...\n");

    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(1, &cpuset);

    pthread_t threads[2];

    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setaffinity_np(&attr, sizeof(cpu_set_t), &cpuset);

    ret = pthread_create(&threads[0], &attr, agent_x, NULL);
    if (ret != 0) {
        printf("FAILED TO START THE AGENT X %i\n", ret);
    }

    CPU_ZERO(&cpuset);
    CPU_SET(2, &cpuset);

    pthread_attr_init(&attr);
    pthread_attr_setaffinity_np(&attr, sizeof(cpu_set_t), &cpuset);

    ret = pthread_create(&threads[1], &attr, agent_y, NULL);
    if (ret != 0) {
        printf("FAILED TO START THE AGENT Y %i\n", ret);
    }

    for (int i = 0; i < 2; i++) {
        pthread_join(threads[i], NULL);
    }

    printf("done...\n");
}

#endif
