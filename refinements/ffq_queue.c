/*
 * Copyright (c) 2016 ETH Zurich.
 * All rights reserved.
 *
 * This file is distributed under the terms in the attached LICENSE file.
 * If you do not find this file, copies can be found by writing to:
 * ETH Zurich D-INFK, Universitaetstr. 6, CH-8092 Zurich. Attn: Systems Group.
 */
//#include "cleanq_module.h"

#ifndef COMPILE
    #define NULL ((void*)0)
#endif

typedef unsigned int u64_t;
typedef unsigned short u16_t;
typedef unsigned int regionid_t;

#define ARCH_CACHELINE_SIZE 64
///< index into the FastForward queue
typedef u16_t ffq_idx_t;

///< payload type of the fast forward queue
typedef u64_t ffq_payload_t;

///< an empty FFQ slot has this value
#define FFQ_SLOT_EMPTY ((ffq_payload_t)-1)
#define FFQ_SLOT_FULL ((ffq_payload_t) 1)

/**
 * the size of a FFQ message in bytes
 * this should be a multiple of the archteicture's cacheline
 */
#define FFQ_MSG_BYTES  (1 * ARCH_CACHELINE_SIZE)

/**
 * the number of (payload) words a message consists of.
 */
#define FFQ_MSG_WORDS  (FFQ_MSG_BYTES / sizeof(ffq_payload_t))

#define FFQ_DEFAULT_SIZE 64

struct ffq_slot
//struct __attribute__((aligned(ARCH_CACHELINE_SIZE))) ffq_slot
{
    ffq_payload_t empty;
    ffq_payload_t rid;
    ffq_payload_t offset;
    ffq_payload_t len;
    ffq_payload_t valid_data;
    ffq_payload_t valid_len;
    ffq_payload_t flags;
    ffq_payload_t pad;
};

typedef enum {
    FFQ_DIRECTION_SEND,
    FFQ_DIRECTION_RECV
} ffq_direction_t;

struct ffq_queue
{
    volatile struct ffq_slot* slots;
    ffq_idx_t size;
    ffq_idx_t pos;
    ffq_direction_t direction;
};

struct ffq_qp {
    //struct cleanq q;
    struct ffq_queue* txq;
    struct ffq_queue* rxq;
};


int ffq_queue_init_tx(struct ffq_queue *q, void *buf);
int ffq_queue_init_rx(struct ffq_queue *q, void *buf);

static struct ffq_qp client;
static struct ffq_qp server;

/*
 * ===========================================================================
 * Send Functions
 * ===========================================================================
 */

 /**
  * @brief sends a message on the FFQ channel
  *
  * @param qp           The queue pair to send the buffer over
  * @param rid          Region id for the buffer
  * @param offset       Offset into the region
  * @param len          Length of the buffer
  * @param valid_data   Offset into the buffer where valid data starts
  * @param valid_len    Length of the valid data
  * @param flags        Flags
  */
int ffq_enqueue(struct ffq_queue *q,
                ffq_payload_t rid, ffq_payload_t offset, ffq_payload_t len,
                ffq_payload_t valid_data, ffq_payload_t valid_len, 
                ffq_payload_t flags)
{
    volatile struct ffq_slot *s = q->slots + q->pos;

    if (s->empty == FFQ_SLOT_FULL) { 
        return -1;
    } else {
        s->rid = rid;
        s->offset = offset;
        s->len = len;
        s->valid_data = valid_data;
        s->valid_len = valid_len;
        s->flags = flags;

        s->empty = FFQ_SLOT_FULL;

        q->pos++;
        if (q->pos == q->size) {
            q->pos = 0;
        }

        return 0;
    }
}


 /*
  * ===========================================================================
  * Recveive Functions
  * ===========================================================================
  */

 /**
  * @brief receive a message on the FFQ channel, assumes valid pointers!
  *
  * @param qp           The queue pair to receive the buffer over
  * @param rid          Region id for the buffer
  * @param offset       Offset into the region
  * @param len          Length of the buffer
  * @param valid_data   Offset into the buffer where valid data starts
  * @param valid_len    Length of the valid data
  * @param flags        Flags
  *
 */
int ffq_dequeue(struct ffq_queue *q,
                ffq_payload_t* rid, ffq_payload_t* offset, ffq_payload_t* len,
                ffq_payload_t* valid_data, ffq_payload_t* valid_len, 
                ffq_payload_t* flags)
{
    volatile struct ffq_slot *s = q->slots + q->pos;

    if (s->empty == FFQ_SLOT_EMPTY) {
        return -1;
    } else {
        *rid = s->rid;
        *offset = s->offset;
        *len = s->len;
        *valid_data = s->valid_data;
        *valid_len = s->valid_len;
        *flags = s->flags;

        s->empty = FFQ_SLOT_EMPTY;

        q->pos++;
        if (q->pos == q->size) {
            q->pos = 0;
        }
        return 0;
    }
}

/*
 * ===========================================================================
 * FFQ channel initialization
 * ===========================================================================
 */

/**
 * @brief Initialize UMP transmit queue state
 *
 * @param       c       Pointer to queue-state structure to initialize.
 * @param       buf     Pointer to ring buffer for the queue.
 * @param       slots   Size (in slots) of buffer.
 *
 * @returns SMLT_SUCCESS or error value
 *
 * The state structure and buffer must already be allocated and appropriately
 * aligned.
 */
int ffq_init_tx(struct ffq_queue *q, struct ffq_slot *buf)
{
    q->direction = FFQ_DIRECTION_SEND;
    q->size = FFQ_DEFAULT_SIZE ;
    q->slots = buf;
    q->pos = 0;

    for (ffq_idx_t i = 0; i < FFQ_DEFAULT_SIZE; i++) {
        q->slots[i].empty = FFQ_SLOT_EMPTY;
    }

    return 0;
}

/**
 * @brief Initialize FF receive queue state
 *
 * @param       c       Pointer to queue-state structure to initialize.
 * @param       buf     Pointer to ring buffer for the queue.
 * @param       slots   Size (in slots) of buffer.
 *
 * @returns SMLT_SUCCESS or error value
 *
 * The state structure and buffer must already be allocated and appropriately
 * aligned.
*/
int ffq_init_rx(struct ffq_queue *q, struct ffq_slot *buf)
{
    q->direction = FFQ_DIRECTION_RECV;
    q->size = FFQ_DEFAULT_SIZE;
    q->slots = buf;
    q->pos = 0;

    for (ffq_idx_t i = 0; i < FFQ_DEFAULT_SIZE; i++) {
        q->slots[i].empty = FFQ_SLOT_EMPTY;
    }

    return 0;
}



int ffq_init_pair(struct ffq_qp* q,
                  void* rx_buf,
                  void* tx_buf)
{
    int err = 0;
    int err2 = 0;

    err  = ffq_init_rx(q->rxq, rx_buf);
    if (err == 0) {
        err2 = ffq_init_tx(q->txq, tx_buf);
    }

    return err | err2;
}


#ifdef COMPILE
#define _GNU_SOURCE
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <stdbool.h>
#include <pthread.h>
#include <assert.h>

static void *sender(void* arg)
{
    struct ffq_qp* qp = (struct ffq_qp*) arg;

    int err = 0;
    ffq_payload_t rid = 123;    
    ffq_payload_t offset = 0;    
    ffq_payload_t len = 2048;    
    ffq_payload_t valid_data = 0;    
    ffq_payload_t valid_len = 0;    
    ffq_payload_t flags = 0;    

    for (int i = 0; i < FFQ_DEFAULT_SIZE-1; i++) {
        offset = 2048*i;
        err = ffq_enqueue(qp->txq, rid, offset, len, valid_data, 
                          valid_len, flags);
    }

    while (true) {
        err = ffq_dequeue(qp->rxq, &rid, &offset, &len, &valid_data, 
                          &valid_len, &flags);
        if (err == 0) {
            printf("[Sender]: received rid=%u offset=%u len=%u \n", rid, offset, len);
            err = -1;
            while (err != 0) {
                printf("[Sender]: sending rid=%u offset=%u len=%u \n", rid, offset, len);
                err = ffq_enqueue(qp->txq, rid, offset, len, valid_data, 
                                  valid_len, flags);
            }
        }
    }
}

static void *receiver(void* arg)
{
    struct ffq_qp* qp = (struct ffq_qp*) arg;

    int err = 0;
    ffq_payload_t rid;    
    ffq_payload_t offset;    
    ffq_payload_t len;    
    ffq_payload_t valid_data;    
    ffq_payload_t valid_len;    
    ffq_payload_t flags;    

    while (true) {
        err = ffq_dequeue(qp->rxq, &rid, &offset, &len, &valid_data, 
                          &valid_len, &flags);
        if (err == 0) {
            printf("[Receiver]: Received rid=%u offset=%u len=%u \n", rid, offset, len);
            err = -1;
            while (err != 0) {
                printf("[Receiver]: sending rid=%u offset=%u len=%u \n", rid, offset, len);
                err = ffq_enqueue(qp->txq, rid, offset, len, valid_data, 
                                  valid_len, flags);
            }
        }
    }
}

int main(int argc, char** argv)
{
    int ret = 0;

    client.rxq = calloc(1, sizeof(struct ffq_queue));
    client.txq = calloc(1, sizeof(struct ffq_queue));

    server.rxq = calloc(1, sizeof(struct ffq_queue));
    server.txq = calloc(1, sizeof(struct ffq_queue));
       
    struct ffq_slot* q_slots1 = calloc(FFQ_DEFAULT_SIZE, sizeof(struct ffq_slot));
    struct ffq_slot* q_slots2 = calloc(FFQ_DEFAULT_SIZE, sizeof(struct ffq_slot));

    ret = ffq_init_pair(&client, q_slots1, q_slots2);
    assert(ret == 0);
    ret = ffq_init_pair(&server, q_slots2, q_slots1);
    assert(ret == 0);
    
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(2, &cpuset);
    
    pthread_t threads[2];

    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setaffinity_np(&attr, sizeof(cpu_set_t), &cpuset);

    ret = pthread_create(&threads[0], &attr, sender, &client);
    assert(ret == 0);
    
    CPU_ZERO(&cpuset);
    CPU_SET(4, &cpuset);
    
    pthread_attr_init(&attr);
    pthread_attr_setaffinity_np(&attr, sizeof(cpu_set_t), &cpuset);

    ret = pthread_create(&threads[1], &attr, receiver, &server);
    assert(ret == 0);

    for (int i = 0; i < 2; i++) {
        pthread_join(threads[i], NULL);
    }
}

#endif
