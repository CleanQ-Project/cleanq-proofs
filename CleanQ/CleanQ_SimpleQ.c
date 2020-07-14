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
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <stdbool.h>
#include <pthread.h>
#include <assert.h>
#endif


#ifndef COMPILE
#define NULL ((void*)0)
#endif

///< this is the architecture cache line size in bytes
#define ARCH_CACHELINE_SIZE_BYTES 64

///< this is the architecture cache line size in machine words (8 bytes)
#define ARCH_CACHELINE_SIZE_WORDS 8


#define CONFIG_DEFAULT_BUFFER_SIZE 4096
#define CONFIG_DEFAULT_QUEUE_SIZE 4
#define CONFIG_DEFAULT_ENQ_BUFS 8
#define CONFIG_DEFAULT_NUM_BUFS 128


/* a few basic type definitions */
typedef unsigned long  u64_t;
typedef unsigned int   u32_t;
typedef unsigned short u16_t;
typedef unsigned char  u8_t;

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
struct buffer
{
    u64_t region;
    u64_t offset;
    u64_t length;
    u64_t valid_offset;
    u64_t valid_length;
    u64_t flags;
    struct buffer *_free;
    struct buffer *_self;
};


///< this defines a ring buffer
struct rb
{
    ///< this is the head pointer of the ring buffer
    u64_t head; 

    ///< this is the tail pointer of the ring buffer
    u64_t tail;

    ///< this is the size of the ring buffer
    u64_t size;

    ///< this is the memory holding the ring buffer
    struct buffer *ring;
};


/* 
 * --------------------------------------------------------------------------------------
 * Initialization
 * --------------------------------------------------------------------------------------
 */

void rb_init(struct rb *rb, struct buffer *ring, u64_t size)
{
    printf("RB init [%p | %lu ]\n", ring, size);
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
static bool rb_can_enq(struct rb *rb)
{
    return (((rb->head + 1) % rb->size) != rb->tail);
}

///< enqueue function
static int rb_enq(struct rb *rb, struct buffer slot)
{
    if (!rb_can_enq(rb)) {
        return ERR_QUEUE_FULL;
    }

    rb->ring[rb->head] = slot;
    rb->head = (rb->head + 1) % rb->size;

    return ERR_OK;
}

/* 
 * --------------------------------------------------------------------------------------
 * Dequeue Operation
 * --------------------------------------------------------------------------------------
 */


///< function to check if there is an element to dequeue
static bool rb_can_deq(struct rb *rb)
{
    return (rb->head != rb->tail);
}

///< the dequeue operation
static int rb_deq(struct rb *rb, struct buffer *ret)
{
    if (!rb_can_deq(rb)) {
        return ERR_QUEUE_EMTPY;
    }

    *ret = rb->ring[rb->tail];
    rb->tail = (rb->tail + 1) % rb->size;

    return ERR_OK;
}


/*
 * ======================================================================================
 * The SimpleQ Queue System
 * ======================================================================================
 */


///< this is the simple queue model
struct simpleq
{
    ///< this is the receiving side of the queue
    struct rb *rx;

    ///< this is the sending side of the queue
    struct rb *tx;

    ///< owned buffers by this endpoint
    struct buffer *owned;

    ///< endpoint name
    char *name;
};



static int simpleq_enq(struct simpleq *sq, struct buffer buf) 
{
    printf("%s - enqueue to [%lu..%lu / %lu]\n", sq->name, sq->tx->tail, sq->tx->head, sq->tx->size);
    return rb_enq(sq->tx, buf);
}

static int simpleq_deq(struct simpleq *sq, struct buffer *buf)
{
    printf("%s - dequeue from [%lu..%lu / %lu]\n", sq->name, sq->rx->tail, sq->rx->head, sq->rx->size);
    return rb_deq(sq->rx, buf);
}


static struct rb rxy;
static struct rb ryx;
static struct simpleq sqx;
static struct simpleq sqy;
static struct buffer *K_bufs;


static int simpleq_enq_x(void)
{
    if (sqx.owned == NULL) {
        printf("%s - no available buffers\n", sqx.name);
        return ERR_NO_BUFFERS;
    }

    struct buffer *buf = sqx.owned;
    sqx.owned = buf->_free;

    printf("%s - sending [%lx..%lx]\n", sqx.name, buf->offset, buf->offset + buf->length - 1);

    if (simpleq_enq(&sqx, *buf) != ERR_OK) {
        printf("%s - enqueue failed\n", sqx.name);
        buf->_free = sqx.owned;
        sqx.owned = buf;
        return ERR_QUEUE_FULL;
    }
    return ERR_OK;
}

static int simpleq_enq_y(void)
{
    if (sqy.owned == NULL) {
        printf("%s - no available buffers\n", sqy.name);
        return ERR_NO_BUFFERS;
    }

    struct buffer *buf = sqy.owned;
    sqy.owned = buf->_free;

    printf("%s - sending [%lx..%lx]\n", sqy.name, buf->offset, buf->offset + buf->length - 1);

    if (simpleq_enq(&sqy, *buf) != ERR_OK) {
        printf("%s - enqueue failed\n", sqy.name);
        buf->_free = sqy.owned;
        sqy.owned = buf;
        return ERR_QUEUE_FULL;
    }

    return ERR_OK;
}

static int simpleq_deq_x(void)
{
    struct buffer buf;
    if (simpleq_deq(&sqx, &buf) != ERR_OK) {
        printf("%s - dequeue failed\n", sqx.name);
        return ERR_QUEUE_EMTPY;
    }

    printf("%s - received [%lx..%lx]\n", sqx.name, buf.offset, buf.offset + buf.length - 1);

    buf._self->_free = sqx.owned;
    sqx.owned = buf._self;

    return ERR_OK;
}

static int simpleq_deq_y(void)
{
    struct buffer buf;
    if (simpleq_deq(&sqy, &buf) != ERR_OK) {
        printf("%s - dequeue failed\n", sqy.name);
        return ERR_QUEUE_EMTPY;
    }

    printf("%s - received [%lx..%lx]\n", sqy.name, buf.offset, buf.offset + buf.length - 1);

    buf._self->_free = sqy.owned;
    sqy.owned = buf._self;

    return ERR_OK;
}



/*
 * ======================================================================================
 * Initialization
 * ======================================================================================
 */


static void init_x(struct rb *rxy, struct buffer *txy, u64_t txy_size, 
                   struct rb *ryx, struct buffer *tyx, u64_t tyx_size)
{
    sqx.tx = rxy;
    sqx.rx = ryx;
    rb_init(sqx.tx, txy, txy_size);
    rb_init(sqx.rx, tyx, tyx_size);
    sqx.name = "[X]";
}

static void init_y(struct rb *rxy, struct buffer *txy, u64_t txy_size, 
                   struct rb *ryx, struct buffer *tyx, u64_t tyx_size)
{
    sqy.tx = ryx;
    sqy.rx = rxy;
    rb_init(sqy.tx, tyx, tyx_size);
    rb_init(sqy.rx, txy, txy_size);
    sqy.name = "[Y]";
}

static int init_queue(u64_t txy_size, u64_t tyx_size, u64_t nbufs)
{
    printf("Initializing Queue...\n");
    struct buffer *txy = calloc(txy_size, sizeof(struct buffer));
    if (txy == NULL) {
        return ERR_NO_BUFFERS;
    }

    struct buffer *tyx = calloc(tyx_size, sizeof(struct buffer));
    if (tyx == NULL) {
        free(txy);
        return ERR_NO_BUFFERS;
    }

    init_x(&rxy, txy, txy_size, &ryx, tyx, tyx_size);
    init_y(&rxy, txy, txy_size, &ryx, tyx, tyx_size);


    K_bufs = calloc(nbufs, sizeof(struct buffer));
    if (K_bufs == NULL) {
        free(txy);
        free(tyx);
        return ERR_NO_BUFFERS;
    }

    for (u64_t i = 0; i < nbufs; i++) {
        K_bufs[i].offset = (i+1) * CONFIG_DEFAULT_BUFFER_SIZE;
        K_bufs[i].length = CONFIG_DEFAULT_BUFFER_SIZE;
        K_bufs[i]._self = &K_bufs[i];
        K_bufs[i]._free = sqx.owned;
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

static void *agent_x(void *arg)
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
        while(!simpleq_deq_x());
        pthread_yield();
        while(!simpleq_deq_x());
        pthread_yield();
        while(!simpleq_deq_x());
    }

    u64_t count = 0;
    struct buffer *buf = sqx.owned;
    while (buf) {
        count++;
        buf = buf->_free;
    }

    printf("Received back %lu bufs\n", count);

    return arg;
}

static void *agent_y(void *arg)
{
    //while(true) {
    for (int i = 0; i < 20; i++) {
        simpleq_deq_y();
        simpleq_enq_y();
    }

    while (sqy.owned != NULL) {
        while(!simpleq_deq_y());
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

    ret = init_queue(CONFIG_DEFAULT_QUEUE_SIZE, CONFIG_DEFAULT_QUEUE_SIZE, CONFIG_DEFAULT_NUM_BUFS);
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
