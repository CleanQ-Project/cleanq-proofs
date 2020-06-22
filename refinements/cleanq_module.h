/*
 * Copyright (c) 2016 ETH Zurich.
 * All rights reserved.
 *
 * This file is distributed under the terms in the attached LICENSE file.
 * If you do not find this file, copies can be found by writing to:
 * ETH Zurich D-INFK, Universitaetstr. 6, CH-8092 Zurich. Attn: Systems Group.
 */
#ifndef QUEUE_INTERFACE_BACKEND_H_
#define QUEUE_INTERFACE_BACKEND_H_ 1


#ifdef COMPILE
struct capref {
    void* vaddr;
    u64_t paddr;   
    u64_t len;
};

struct cleanq;
#endif
/*
 * ===========================================================================
 * Backend function definitions
 * ===========================================================================
 */

 /**
  * @brief Registers a memory region. For direct queues this function
  *        Has to handle the communication to the device driver since
  *        there might also be a need to set up some local state for the
  *        direct queue that is device specific
  *
  * @param q         The device queue handle
  * @param cap       The capability of the memory region
  * @param reigon_id The region id
  *
  * @returns error on failure or SYS_ERR_OK on success
  */
typedef int (*cleanq_register_t)(struct cleanq *q, struct capref cap,
                                 regionid_t region_id);

 /**
  * @brief Deregisters a memory region. (Similar communication constraints
  *        as register)
  *
  * @param q         The device queue handle
  * @param reigon_id The region id
  *
  * @returns error on failure or SYS_ERR_OK on success
  */
typedef int (*cleanq_deregister_t)(struct cleanq *q, regionid_t region_id);


 /**
  * @brief Directly enqueues something into a hardware queue. Only used by
  *        direct endpoints
  *
  * @param q            The device queue handle
  * @param region_id    The region id of the buffer
  * @param offset       Offset into the region where the buffer starts
  * @param length       Length of the buffer
  * @param valid_data   Offset into the region where the valid data of the
  *                     buffer starts
  * @param valid_length Length of the valid data in this buffer
  * @param misc_flags   Misc flags
  *
  * @returns error on failure or SYS_ERR_OK on success
  */
typedef int (*cleanq_enqueue_t)(struct cleanq *q, regionid_t region_id,
                                unsigned int offset, unsigned int length,
                                unsigned int valid_offset,
                                unsigned int valid_length,
                                unsigned int misc_flags);

 /**
  * @brief Directly dequeus something from a hardware queue. Only used by
  *        direct endpoints
  *
  * @param q            The device queue handle
  * @param region_id    The region id of the buffer
  * @param offset       Return pointer to the offset into the region
  *                     where the buffer starts
  * @param length       Return pointer to the length of the buffer
  * @param valid_offset Return pointer to the offset into the region
  *                     where the valid data of the buffer starts
  * @param valid_length Return pointer to the length of the valid data of
  *                     this buffer
  * @param misc_flags   Misc flags
  *
  * @returns error on failure if the queue is empty or SYS_ERR_OK on success
  */
typedef int (*cleanq_dequeue_t)(struct cleanq *q, regionid_t* region_id,
                                   unsigned int* offset, unsigned int* length,
                                   unsigned int* valid_offset,
                                   unsigned int* valid_length,
                                   unsigned int* misc_flags);

// The functions that the backend has to set
struct cleanq_func_pointer {
    int (*enq)(struct cleanq *q, unsigned int region_id, unsigned int offset, unsigned int length,
               unsigned int valid_offset, unsigned int valid_length, unsigned int misc_flags);
    int (*deq)(struct cleanq *q, unsigned int* region_id, unsigned int* offset, unsigned int* length,
               unsigned int* valid_offset, unsigned int* valid_length, unsigned int* misc_flags);
};

struct cleanq {
    // Funciton pointers
    struct cleanq_func_pointer f;
    void *state;
};

#endif /* QUEUE_INTERFACE_BACKEND_H_ */
