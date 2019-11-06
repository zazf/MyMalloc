#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

#define max(a,b) (((a) > (b)) ? (a) : (b)) // max
#define min(a,b) (((a) < (b)) ? (a) : (b)) // min


/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

void insert_in_list (header * hdr, int index) {
  hdr->next = freelistSentinels[index].next;
  hdr->prev = &freelistSentinels[index];
  freelistSentinels[index].next->prev = hdr;
  freelistSentinels[index].next = hdr;
}

void sep_from_list (header * hdr) {
  hdr->prev->next = hdr->next;
  hdr->next->prev = hdr->prev;
}


header * divide_block (header * selected, size_t actual_size) {
  //selected->prev->next = selected->next;
  //selected->next->prev = selected->prev;
  size_t new_size = get_size(selected) - actual_size;
  header * result = get_header_from_offset(selected, new_size);
  set_size(selected, new_size);
  set_size(result, actual_size);
  result->left_size = new_size;
  set_state(result, ALLOCATED);

  header * right_header = get_right_header(result);
  right_header->left_size = actual_size;

  int new_index = min (((new_size - ALLOC_HEADER_SIZE) / MIN_ALLOCATION - 1), (N_LISTS-1));
  if (new_index < 58) {
  insert_in_list (selected, new_index);
  }

  return result;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  // TODO implement allocation
  (void) raw_size;

  if (raw_size == 0) {
    return NULL;
  }


  /*
  int index = max((raw_size / MIN_ALLOCATION), 2) - 1;

  if ((raw_size % MIN_ALLOCATION != 0) && index) {
    index++;
  }
  */

  int index = raw_size / MIN_ALLOCATION - 1;
  if (raw_size % MIN_ALLOCATION != 0) {
    index++;
  }
  index = max(index, 1);

  int actual_size = (index + 1) * MIN_ALLOCATION + ALLOC_HEADER_SIZE;
// for index from 1 to 57
  for (;index < N_LISTS - 1; index++) {
    if (freelistSentinels[index].next == &freelistSentinels[index]) {
      continue;
    }
    header * result = freelistSentinels[index].next;
    size_t remain_size = get_size(result) - actual_size;
    if (remain_size < 32) {
      sep_from_list (result);
      set_state(result, ALLOCATED);
      return (header*) result->data;
    } else {
      sep_from_list (result);
      result = divide_block(result, actual_size);
      return (header*) result->data;
    }
  }

  if (index > (N_LISTS-2)) {
    index = (N_LISTS-1);
  }
//for index in the last free list
  header * selected = freelistSentinels[index].next;

  while (selected != &freelistSentinels[index]) {

    size_t remain_size = get_size(selected) - actual_size;

    if (get_size(selected) < actual_size) {
    } else if (remain_size < 32) {
        header * result = freelistSentinels[index].next;
        sep_from_list (result);
        set_state(result, ALLOCATED);
        return (header*) result->data;
    } else {
      if (((remain_size-16)/8-1) < 58) {
      sep_from_list (selected);
      }
      header * result = divide_block(selected, actual_size);
      return (header*) result->data;
    }

    selected = selected->next;
  }
// mallocing new chunk
  int num_of_chunk = (actual_size + 2 * ALLOC_HEADER_SIZE) / ARENA_SIZE;

  if ((actual_size + 2 * ALLOC_HEADER_SIZE) % ARENA_SIZE != 0) {
    num_of_chunk++;
  }

  size_t nsize = num_of_chunk * ARENA_SIZE;
  header * new_block = allocate_chunk(nsize);

  size_t og_size = get_size(new_block);

  header * prev_fencepost = lastFencePost;

  int flag = 0;
//coalesing chunks
  if ((char*)new_block-(char*)lastFencePost == 32) {
    header * left_header = get_left_header(lastFencePost);
    lastFencePost = get_right_header(new_block);
    if (get_state(left_header) == ALLOCATED) {
      new_block = prev_fencepost;
      set_size(new_block, og_size + 2 * ALLOC_HEADER_SIZE);
      set_state(new_block, UNALLOCATED);
      lastFencePost->left_size = og_size + 2 * ALLOC_HEADER_SIZE;
    } else if (get_state(left_header) == UNALLOCATED) {
      new_block = left_header;
      if (((get_size(left_header)-16)/8-1) < 58) {
        sep_from_list (new_block);
      } else {
        flag = 1;
      }
      set_size(new_block, get_size(new_block) + og_size + 2 * ALLOC_HEADER_SIZE);
      lastFencePost->left_size = get_size(new_block);
    }
  } else {
    insert_os_chunk (get_left_header(new_block));
  }

  if (flag == 0) {
    insert_in_list (new_block, 58);
  }

  if (((get_size(new_block)-actual_size-16)/8-1) < 58) {
      sep_from_list (new_block);
  }

  header * result = divide_block(new_block, actual_size);

  return (header *) result->data;

  assert(false);

  exit(1);
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

int coalesce_block (header * left, header * right) {
  size_t new_size = get_size(left) + get_size(right);
  set_size(left, new_size);
  header * right_header = get_right_header(right);
  right_header->left_size = new_size;

  int new_index = min (((new_size - ALLOC_HEADER_SIZE) / MIN_ALLOCATION - 1), (N_LISTS-1));

  return new_index;
  
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation
  (void) p;

  if (p == NULL) {
    return;
  }

  header * hdr = ptr_to_header(p);

  if (hdr == NULL) {
    return;
  }

  if (hdr->size_state == 0 || hdr->left_size == 0) {
    return;
  }

  if (get_state(hdr) == UNALLOCATED) {
    fprintf(stderr, "Double Free Detected\n");
    assert(false);
    exit(1);
  }

  p == NULL;

  header * lhdr = get_left_header(hdr);
  header * rhdr = get_right_header(hdr);

  int flag = 0;

  int new_index = min (((get_size(hdr) - ALLOC_HEADER_SIZE) / MIN_ALLOCATION - 1), (N_LISTS-1));

  set_state(hdr, UNALLOCATED);

  if (get_state(rhdr) == UNALLOCATED) {
    sep_from_list (rhdr);
    new_index = coalesce_block (hdr, rhdr);
  }

  if (get_state(lhdr) == UNALLOCATED) {
    if (((get_size(lhdr)-16)/8-1) < 58) {
      sep_from_list (lhdr);
    } else {
      flag = 1;
    }
    new_index = coalesce_block (lhdr, hdr);
    hdr = lhdr;
  }

  //new_index = min (((get_size(hdr) - 16) / 8 - 1), 58);

  if (flag == 0) {
    insert_in_list (hdr, new_index);
  }

  return;

  assert(false);
  exit(1);
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
