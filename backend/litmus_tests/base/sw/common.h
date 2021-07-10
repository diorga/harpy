#include <atomic>


void setArray(uint64_t* array,
               int value,
               int n_entries)
{
    //assert(n_entries*sizeof(uint64_t) < getpagesize());

    for (int i = 0; i < n_entries; i += 1)
    {
      array[i] = value;
    }

    // Force all initialization to memory before the buffer is passed to the FPGA.
    std::atomic_thread_fence(std::memory_order_seq_cst);
}

void printArray(uint64_t* array,
                int instructions,
                int experiments)
{

    for (int i = 0; i < experiments; i++ )
    {
      for (int j = 0; j < instructions; j++ ) {
        cout << array[i*instructions+j] << " ";
      }
      cout << endl;
    }

    // Force all initialization to memory before the buffer is passed to the FPGA.
    std::atomic_thread_fence(std::memory_order_seq_cst);
}

unsigned int countArray(uint64_t* array,
               int value,
               int n_entries)
{
    unsigned int count = 0;
    //assert(n_entries*sizeof(uint64_t) < getpagesize());

    for (int i = 0; i < n_entries; i += 1)
    {
      if (array[i] == value) count++;
    }

    // Force all initialization to memory before the buffer is passed to the FPGA.
    std::atomic_thread_fence(std::memory_order_seq_cst);

    return count;
}
