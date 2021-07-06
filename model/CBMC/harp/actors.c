#include "actors.h"
#include <string.h>

/*
 Functions
*/

// Initialise global history
void initGlobalHistory() {
  memset(g_history, 0, MAX_TIME * sizeof(headerT));
}

// Initialise a pool
void initPool(ReqPool *reqPool) {
  memset(reqPool->pending, 0, POOL_SIZE * sizeof(headerT));
  reqPool->num_pending_operations = 0;
  reqPool->head = 0;
}

// Initialise a channel
void initChannel(Channel *ch) {
  memset(ch->pending, 0, CHANNEL_SIZE * sizeof(headerT));
  ch->num_pending_operations = 0;
  ch->head = 0;
}

// Initialise a write buffer
void initWriteBuffer(WrBuffer *wrBuffer) {
  memset(wrBuffer->pending, 0, W_BUFFER_SIZE * sizeof(headerT));
  wrBuffer->num_pending_operations = 0;
  wrBuffer->head = 0;
}


headerT nondet_headerT();

/*
 * This function can be used to give a nondeterministic WrReq or WrFnReq with 3 restrictions:
 *    address - fits in shared memory
 *    channel - is an existing channel
 *    mdata - is unique per write request
 */
headerT wrReqH_gen() {
  headerT header = nondet_headerT();
//  static unsigned long mdata_count = 0;

  __CPROVER_assume(header.type == WrReq || header.type == FnReq);
  __CPROVER_assume(header.address < MAX_LOC);
  __CPROVER_assume(header.channel <= MAX_CHANNELS);
  __CPROVER_assume(header.thread == 0);
//  header.mdata = mdata_count++;
  __CPROVER_assume(header.mdata < MAX_EVENTS);
  // when fields are initialised, simulation is faster
  if (header.type == FnReq) {
    header.data = 0;
    header.address = 0;
  }

  return header;
}

/*
 * This function can be used to give a nondeterministic RdReq with 3 restrictions:
 *    address - fits in shared memory
 *    channel - is an existing channel
 *    mdata - is unique per write request
 */
headerT rdReqH_gen() {
  headerT header = nondet_headerT();
//  static unsigned long mdata_count = 0;

  __CPROVER_assume(header.type == RdReq);
  __CPROVER_assume(header.address < MAX_LOC);
  __CPROVER_assume(header.channel <= MAX_CHANNELS);
  __CPROVER_assume(header.thread == 0);
//  header.mdata = mdata_count++;
  __CPROVER_assume(header.mdata < MAX_EVENTS);
  header.data = 0; // when fields are initialised, simulation is faster

  return header;
}



/*
 * This function can be used to give a nondeterministic CPU write:
 *    address - fits in shared memory
 */
headerT cpuWriteH_gen() {
  headerT header = nondet_headerT();

  __CPROVER_assume(header.type == CpuWrite);
  __CPROVER_assume(header.address < MAX_LOC);
  header.thread = 0;
  header.channel = 0;
  header.mdata = 0;

  return header;
}

/*
 * This function can be used to give a nondeterministic CPU fence:
 *    all arguments are fixed
 */
headerT cpuFenceH_gen() {
  headerT header = nondet_headerT();

  __CPROVER_assume(header.type == CpuFence);
  header.address = 0;
  header.thread = 0;
  header.channel = 0;
  header.mdata = 0;

  return header;
}

/*
 * This function can be used to give a nondeterministic CPU read:
 *    address - fits in shared memory
 */
headerT cpuReadH_gen() {
  headerT header = nondet_headerT();

  __CPROVER_assume(header.type == CpuRead);
  __CPROVER_assume(header.address < MAX_LOC);
  header.thread = 0;
  header.channel = 0;
  header.data = 0;
  header.mdata = 0;

  return header;
}

void addToWrReqPool(ReqPool *wrReqPool) {

  headerT wrReqH = wrReqH_gen();

  // Add this operation to the pending pool.
  int tail = (wrReqPool->head + wrReqPool->num_pending_operations) % POOL_SIZE;
  wrReqPool->pending[tail] = wrReqH;
  wrReqPool->num_pending_operations += 1;

  g_history[global_time++] = wrReqH;
  wrReq_issued++;
}

void addToRdReqPool(ReqPool *rdReqPool) {

  headerT rdReqH = rdReqH_gen();


  // Add this operation to the pending pool.
  int tail = (rdReqPool->head + rdReqPool->num_pending_operations) % POOL_SIZE;
  rdReqPool->pending[tail] = rdReqH;
  rdReqPool->num_pending_operations += 1;

  g_history[global_time++] = rdReqH;
  rdReq_issued++;
}

/*
 * For simulation purpouses, might want nops added
 */
void addNop() {

    headerT nopH;

    nopH.type = Nop;
    nopH.channel = 0;
    nopH.address = 0;
    nopH.data = 0;
    nopH.mdata = 0;

    g_history[global_time++] =nopH;
}



void flushChannel(Channel *upstreamChannels,
                  Channel *downstreamChannels,
                  unsigned char ch_index,
                  unsigned char *sharedMemory) {

/*  unsigned char downstreamElements = downstreamChannels[ch_index].num_pending_operations;
  unsigned char upstreamElements = upstreamChannels[ch_index].num_pending_operations;

  for (int i = 0; i < CHANNEL_SIZE; i++) {
    if (i < CHANNEL_SIZE - downstreamElements) {
        stepDownstreamChannel( downstreamChannels, ch_index, sharedMemory);
    }
#if SANITY_CHECK
      __CPROVER_assert(downstreamChannels[ch_index].num_pending_operations < CHANNEL_SIZE,
                       "Impossible to flush to a full  channel");
#endif
    if (i < CHANNEL_SIZE - upstreamElements) {
        stepUpstreamChannel( upstreamChannels, downstreamChannels, ch_index, sharedMemory);
    }
  }*/
}

// Steps the channel
void stepUpstreamChannel( Channel *upstreamChannels,
                          Channel *downstreamChannels,
                          unsigned char ch_index,
                          unsigned char *sharedMemory) {

  unsigned char ch_head = upstreamChannels[ch_index].head;
  unsigned char ch_tail = (ch_head + upstreamChannels[ch_index].num_pending_operations) % CHANNEL_SIZE;
  unsigned char data = upstreamChannels[ch_index].pending[ch_head].data;
  unsigned char address = upstreamChannels[ch_index].pending[ch_head].address;

  if (upstreamChannels[ch_index].pending[ch_head].type == WrReq) {
    sharedMemory[address] = data;
  } else if (upstreamChannels[ch_index].pending[ch_head].type == RdReq) {
    // Generate response
    headerT response = upstreamChannels[ch_index].pending[ch_head];
    response.type = RdRsp;
    response.data = sharedMemory[address];
    response.channel = ch_index;

    // data goes to channel
    unsigned char ch_index = response.channel;
    unsigned char ch_head = downstreamChannels[ch_index].head;
    unsigned char ch_tail = (ch_head + downstreamChannels[ch_index].num_pending_operations) % CHANNEL_SIZE;

    // Guard that channel is not occupied
    __CPROVER_assume(downstreamChannels[ch_index].num_pending_operations < CHANNEL_SIZE);

    downstreamChannels[ch_index].pending[ch_tail] = response;
    downstreamChannels[ch_index].num_pending_operations++;

  } else {
    // You should only have RdReq or WrReq on the channels
    __CPROVER_assume(0);
  }

  upstreamChannels[ch_index].head = (upstreamChannels[ch_index].head + 1) % CHANNEL_SIZE;
  upstreamChannels[ch_index].num_pending_operations--;
}

void stepDownstreamChannel( Channel *downstreamChannels,   // Steps the downstream channel
                            unsigned char ch_index,
                            unsigned char *sharedMemory) {

  unsigned char ch_head = downstreamChannels[ch_index].head;
  unsigned char ch_tail = (ch_head + downstreamChannels[ch_index].num_pending_operations) % CHANNEL_SIZE;

  headerT response = downstreamChannels[ch_index].pending[ch_head];
  g_history[global_time++] = response;

  downstreamChannels[ch_index].head = (downstreamChannels[ch_index].head + 1) % CHANNEL_SIZE;
  downstreamChannels[ch_index].num_pending_operations--;

}

// See if the channel already has a value
// WARNING: Coalescing writes to same address might be hard to model
//          Maybe I need to rethink this somehow
// DEPRECATED: The new model does not use this anymore
int check_channel(Channel *channels,
                  unsigned char ch_index,
                  unsigned char address,
                  unsigned char *data) {

  int found = 0;
  int mdata = -1;

  if(channels[ch_index].num_pending_operations == 0) {
    return 0;
  }

  unsigned char ch_head = channels[ch_index].head;
  unsigned char ch_tail = (ch_head + channels[ch_index].num_pending_operations) % CHANNEL_SIZE;

  for(int i=0;i < CHANNEL_SIZE; i++) {
    if ( (channels[ch_index].pending[ch_head].address == address) &&
         (mdata < channels[ch_index].pending[ch_head].mdata) ){
      *data = channels[ch_index].pending[ch_head].data;     // Store what value I found
      mdata = channels[ch_index].pending[ch_head].mdata;
      found++;
    }
    ch_head = (ch_head + 1) % CHANNEL_SIZE;
    if (ch_head == ch_tail)  break;
  }

  // Id did not find it
  if (found) return 1;                                             // I found it
  return 0;
}


// Steps the wrReqPool
void stepWrReqPool( ReqPool *wrReqPool,
                    Channel *upstreamChannels,
                    Channel *downstreamChannels,
                    unsigned char *sharedMemory) {

  // If the next operation is a fence, we only have one choice: remove the fence
  // from the pool. But otherwise we can apply any write from here until the
  // next fence.
  if (wrReqPool->pending[wrReqPool->head].type != FnReq) {
    // The following loops nondeterministically through the write operations
    // until the next fence.
    unsigned char offset = 0;
    unsigned char index = wrReqPool->head;
    unsigned char next_index;
    unsigned char tail = (wrReqPool->head + wrReqPool->num_pending_operations) % POOL_SIZE ;

    while (offset<POOL_SIZE) {

      next_index = (index + 1) % POOL_SIZE;

      // Nondeterministically choose to skip the index if we have
      // not reached the end of the pool and
      // next operation is not a fence
      if ( nondet_int() ||
           (next_index == tail) ||
           (wrReqPool->pending[next_index].type == FnReq) ) {
        break;
      }

      index = next_index;
      offset++;
    }
    // At this point, index is the write we would like to apply,
    // and offset is the number of operations we skipped over.

    // data goes to channel
    unsigned char ch_index = wrReqPool->pending[index].channel;
    if (ch_index == VA) {
      // Choose a channel non-deterministically
      ch_index = nondet_uchar();
      __CPROVER_assume( (ch_index >= 0) && (ch_index < MAX_CHANNELS));
    }

    unsigned char ch_head = upstreamChannels[ch_index].head;
    unsigned char ch_tail = (ch_head + upstreamChannels[ch_index].num_pending_operations) % CHANNEL_SIZE;

    // Guard that channel is not occupied
    __CPROVER_assume(upstreamChannels[ch_index].num_pending_operations < CHANNEL_SIZE);

    upstreamChannels[ch_index].pending[ch_tail] = wrReqPool->pending[index];
    upstreamChannels[ch_index].num_pending_operations++;

    // Record a write response
    headerT response = wrReqPool->pending[index] ;
    response.type = WrRsp;
    response.channel = ch_index;

    g_history[global_time++] = response;


    // Now reorganize the circular buffer to account for any operations that we skipped.
    // for (unsigned int temp = offset; temp > 0; temp--) {
    //  wrReqPool.pending[(index - temp) % POOL_SIZE] = wrReqPool.pending[(wrReqPool.head - temp - 1) % POOL_SIZE];
    //}
    for (int i = 0; i < POOL_SIZE; i++) {
      if ((wrReqPool->head < index) && ((i >= wrReqPool->head) && (i< index)))
        wrReqPool->pending[(i + 1) % POOL_SIZE] = wrReqPool->pending[i];
      if ((wrReqPool->head > index) && ((i >= wrReqPool->head) || (i< index)))
        wrReqPool->pending[(i + 1) % POOL_SIZE] = wrReqPool->pending[i];
    }
  }
  else if (wrReqPool->pending[wrReqPool->head].type == FnReq) {
    unsigned char ch_index = wrReqPool->pending[wrReqPool->head].channel;

    if (ch_index == VA) {
      for( int i=0; i < MAX_CHANNELS; i++) {
        __CPROVER_assume(upstreamChannels[i].num_pending_operations == 0);
#if SANITY_CHECK
      __CPROVER_assert(upstreamChannels[i].num_pending_operations == 0,
                       "Bad Flush");
#endif
      }
    } else {
        __CPROVER_assume(upstreamChannels[ch_index].num_pending_operations == 0);
#if SANITY_CHECK
      __CPROVER_assert(upstreamChannels[ch_index].num_pending_operations == 0,
                       "Bad Flush");
#endif
    }

    // Record a write fence response
    headerT response = wrReqPool->pending[wrReqPool->head];
    response.type = FnRsp;

    g_history[global_time++] = response;
  }


  // We have one fewer operation to deal with, and the head has moved on one place.
  wrReqPool->num_pending_operations -= 1;
  wrReqPool->head = (wrReqPool->head + 1) % POOL_SIZE;
}



// Steps the rdReqPool
void stepRdReqPool( ReqPool *rdReqPool,
                    Channel *upstreamChannels,
                    unsigned char *sharedMemory) {

  // Non-det choose the request to execute
  unsigned char offset = 0;
  unsigned char index = rdReqPool->head;
  unsigned char next_index;
  unsigned char tail = (rdReqPool->head + rdReqPool->num_pending_operations) & POOL_SIZE;

  while(offset< POOL_SIZE) {

    next_index = (index + 1) % POOL_SIZE;
    // Nondeterministically choose to apply the request at the current index
    // or stop because we reached the end of the pool
    if  ( nondet_int() ||
          (next_index == tail) ) {
      break;
    }

    // Or move on to the next index.
    index = next_index;
    offset++;
  }

    // data goes to channel
  unsigned char ch_index = rdReqPool->pending[index].channel;
  if (ch_index == VA) {
    // Choose a channel non-deterministically
    ch_index = nondet_uchar();
    __CPROVER_assume( (ch_index >= 0) && (ch_index < MAX_CHANNELS));
  }

  unsigned char ch_head = upstreamChannels[ch_index].head;
  unsigned char ch_tail = (ch_head + upstreamChannels[ch_index].num_pending_operations) % CHANNEL_SIZE;

  // Guard that channel is not occupied
  __CPROVER_assume(upstreamChannels[ch_index].num_pending_operations < CHANNEL_SIZE);

  upstreamChannels[ch_index].pending[ch_tail] = rdReqPool->pending[index];
  upstreamChannels[ch_index].num_pending_operations++;

  // Now reorganize the circular buffer to account for any operations that we skipped.

  //for (int temp = offset; temp > 0; temp--) {
  //  rdReqPool.pending[(index - temp) % POOL_SIZE] = rdReqPool.pending[(rdReqPool.head - temp - 1) % POOL_SIZE];
  //}
  for (int i = 0; i < POOL_SIZE; i++) {
    if ((rdReqPool->head < index) && ((i >= rdReqPool->head) && (i< index)))
        rdReqPool->pending[(i + 1) % POOL_SIZE] = rdReqPool->pending[i];
    if ((rdReqPool->head > index) && ((i >= rdReqPool->head) || (i< index)))
        rdReqPool->pending[(i + 1) % POOL_SIZE] = rdReqPool->pending[i];
  }

  // We have one fewer operation to deal with, and the head has moved on one place.
  rdReqPool->num_pending_operations -= 1;
  rdReqPool->head = (rdReqPool->head + 1) % POOL_SIZE;
}

/*
 * TSO cores
 */

// Generate a TSO core write
void tso_core_write( WrBuffer *wrBuffer,
                    unsigned char thread) {

  headerT cpuWriteH = cpuWriteH_gen();
  cpuWriteH.thread = thread;

  // Add this operation to the pending pool.
  int tail = (wrBuffer->head + wrBuffer->num_pending_operations) % W_BUFFER_SIZE;
  wrBuffer->pending[tail] = cpuWriteH;
  wrBuffer->num_pending_operations += 1;

  g_history[global_time++] = cpuWriteH;
  cpuWrites_issued++;
}

// Register a fence and flush the buffer
void tso_core_fence(WrBuffer *wrBuffer,
                    unsigned char thread) {

  __CPROVER_assume(wrBuffer->num_pending_operations == 0);
  headerT cpuFenceH = cpuFenceH_gen();
  cpuFenceH.thread = thread;
  g_history[global_time++] = cpuFenceH;
  cpuWrites_issued++;

}

// Step write buffer
void stepWriteBuffer(WrBuffer *wrBuffer,
                    unsigned char *sharedMemory) {

  unsigned char head = wrBuffer->head;
  unsigned char data = wrBuffer->pending[head].data;
  unsigned char address = wrBuffer->pending[head].address;

  sharedMemory[address] = data;

  wrBuffer->head = (wrBuffer->head + 1) % W_BUFFER_SIZE;
  wrBuffer->num_pending_operations--;
}

// See if the buffer already has a value
int check_buffer( WrBuffer *wrBuffer,
                  unsigned char address,
                  unsigned char *data) {

  int checked = wrBuffer->num_pending_operations;

  if(wrBuffer->num_pending_operations == 0) {
    return -1;
  }

  unsigned char ch_head = wrBuffer->head;
  unsigned char ch_tail = (ch_head + wrBuffer->num_pending_operations - 1) % W_BUFFER_SIZE;


  for(int i=0; i < W_BUFFER_SIZE; i++) {
    if (wrBuffer->pending[ch_tail].address == address) {
      *data = wrBuffer->pending[ch_tail].data;               // Store what value I found
      return 1;                                             // I found it
    }
    if (ch_tail == 0) {
      ch_tail = W_BUFFER_SIZE - 1;
    } else {
      ch_tail = (ch_tail - 1) % W_BUFFER_SIZE;
    }
    checked--;
    if (checked == 0) break;
  }

  // Id did not find it
  return -1;
}

// Generate a TSO core read
void tso_core_read(WrBuffer *wrBuffer,
                  unsigned char *sharedMemory,
                  unsigned char thread) {


  headerT cpuReadH = cpuReadH_gen();
  cpuReadH.thread = thread;

  // Actually do the read
  unsigned char rd_address = cpuReadH.address;
  unsigned char data;

  if (check_buffer(wrBuffer, rd_address, &data) == -1 )
    data = sharedMemory[rd_address];

  // Generate response
  headerT response = cpuReadH;
  response.type = CpuRead;
  response.data = data;

  g_history[global_time++] = response;
  cpuReads_issued++;
}


/*
 * SC cores
 */

// Generate a SC core write
void sc_core_write(unsigned char *sharedMemory,
                  unsigned char thread) {

  headerT cpuWriteH = cpuWriteH_gen();
  cpuWriteH.thread = thread;

  // Add this operation to the pending pool.
  unsigned char data = cpuWriteH.data;
  unsigned char address = cpuWriteH.address;

  sharedMemory[address] = data;

  g_history[global_time++] = cpuWriteH;
  cpuWrites_issued++;
}

// Generate a SC core read
void sc_core_read(unsigned char *sharedMemory,
                  unsigned char thread) {

  headerT cpuReadH = cpuReadH_gen();
  cpuReadH.thread = thread;

  // Actually do the read
  unsigned char rd_address = cpuReadH.address;
  cpuReadH.data = sharedMemory[rd_address];


  g_history[global_time++] = cpuReadH;
  cpuReads_issued++;
}
