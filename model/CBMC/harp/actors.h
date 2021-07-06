#ifndef ACTORS_H_
#define ACTORS_H_

#define SANITY_CHECK       1

/*
 FPGA Constants
*/

//#define MAX_RD_REQ          7             // The total number of RdReq that can be issued
//#define MAX_WR_REQ          7             // The total number of WrReq/WrFnReq that can be issued
#define MAX_TIME            30              // The total number of simulation tracked steps
#define CHANNEL_SIZE        2               // The maximum elements that can be in transition in a channel
#define POOL_SIZE           4               // The number of operations that can be in the pool at any time
#define MAX_CHANNELS        2               // The total amount of channels the system has.
#define MAX_LOC             6               // The size of the shared memory
#define VA                  MAX_CHANNELS    // Automatically choose the channel
#define MAX_EVENTS          10              // Used for mdata
//TODO: TODO:Make MAX_EVENTS dynamic


/*
 CPU Constants
*/
//#define MAX_CPU_WRITES      4             // The total number of CPU writes that can be issued
//#define MAX_CPU_READS       4             // The total number of CPU reads that can be issued
#define W_BUFFER_SIZE       2             // The write buffer size




// The supported type of user operations
typedef enum {
  Nop,
  WrReq,
  WrRsp,
  RdReq,
  RdRsp,
  FnReq,
  FnRsp,
  CpuWrite,
  CpuFence,
  CpuRead,
} operations;

// An instruction that was optional values based on what type it is
typedef struct {
  operations type;
  unsigned char channel;
  unsigned char thread;
  unsigned char address;
  unsigned char data;
  unsigned char mdata;
} headerT;

/*
 * FIU Structs
 */

// A request pool consists of.
typedef struct {
  // A circular buffer storing those operations that could be pending.
  headerT pending[POOL_SIZE];
  // The number of operations that are actually pending.
  unsigned char num_pending_operations;
  // The operation to be processed next; the pending operations are thus
  // pending[head], ... (head + num_pending_operations) % POOL_SIZE]
  unsigned char head;
} ReqPool;

// A channel is simillarly a circular buffer
typedef struct {
  // A circular buffer storing those operations that could be pending.
  headerT pending[CHANNEL_SIZE];
  // The number of operations that are actually pending.
  unsigned char num_pending_operations;
  // The operation to be processed next; the pending operations are thus
  // pending[head], ... (head + num_pending_operations) % POOL_SIZE]
  unsigned char head;
} Channel;


/*
 * CPU structs
 */

// A channel is simillarly a circular buffer
typedef struct {
  // A circular buffer storing those operations that could be pending.
  headerT pending[W_BUFFER_SIZE];
  // The number of operations that are actually pending.
  unsigned char num_pending_operations;
  // The operation to be processed next; the pending operations are thus
  // pending[head], ... (head + num_pending_operations) % POOL_SIZE]
  unsigned char head;
} WrBuffer;


headerT g_history[MAX_TIME];                    // A global history of the state
unsigned char global_time = 0;                   // Keep track of global time
unsigned char rdReq_issued = 0, wrReq_issued = 0;
unsigned char cpuWrites_issued = 0, cpuReads_issued = 0;

/*
 Functions
*/

int nondet_int();                               // Generate a non-det int
unsigned char nondet_uchar();                 // Generate a non-det uchar

void initGlobalHistory();                       // Initialise global history
void initPool(ReqPool *reqPool);                // Initialise a pool
void initChannel(Channel *ch);                  // Initialise a channel
void initWriteBuffer(WrBuffer *wrBuffer);       // Initialise write buffer


void addToWrReqPool(ReqPool *wrReqPool);
void addToRdReqPool(ReqPool *rdReqPool);
void addNop();


void flushChannel(Channel *upstreamChannels,     // Flush channel;
                  Channel *downstramChannels,
                  unsigned char ch_index,
                  unsigned char *sharedMemory);
int check_channels( Channel *channels,          // DEPRACATED: Check if a location is in the channels
                    unsigned char location,
                    unsigned char *channel_found,
                    unsigned char *value);
void stepUpstreamChannel( Channel *upstreamChannels,       // Steps the upstream channel
                          Channel *downstreamChannels,
                          unsigned char ch_index,
                          unsigned char *sharedMemory);
void stepDownstreamChannel( Channel *downstreamChannels,   // Steps the downstream channel
                            unsigned char ch_index,
                            unsigned char *sharedMemory);
void stepWrReqPool( ReqPool *wrReqPool,         // Steps the wrReqPool
                    Channel *upstreamChannels,
                    Channel *downstreamChannels,
                    unsigned char *sharedMemory);
void stepRdReqPool( ReqPool *rdReqPool,         // Steps the rdReqPool
                    Channel *upstreamChannels,
                    unsigned char *sharedMemory);

/*
 * TSO cores
 */
void tso_core_read(WrBuffer *wrBuffer,                // Generate a TSO core read
              unsigned char *sharedMemory,
              unsigned char thread);
void tso_core_write( WrBuffer *wrBuffer,              // Generate a TSO core write
                     unsigned char thread);
void tso_core_fence( WrBuffer *wrBuffer,              // Register a fence and flush the buffer
                     unsigned char thread);
void stepWriteBuffer(WrBuffer *wrBuffer,              // Step write buffer
                    unsigned char *sharedMemory);

/*
 * SC cores
 */

void sc_core_read(unsigned char *sharedMemory,        // Generate a SC core read
                  unsigned char thread);
void sc_core_write(unsigned char *sharedMemory,       // Generate a SC core write
                   unsigned char thread);


#endif /* ACTORS_H_ */
