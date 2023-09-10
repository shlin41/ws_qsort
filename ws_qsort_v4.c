/* A work-stealing scheduler is described in
 * Robert D. Blumofe, Christopher F. Joerg, Bradley C. Kuszmaul, Charles E.
 * Leiserson, Keith H. Randall, and Yuli Zhou. Cilk: An efficient multithreaded
 * runtime system. In Proceedings of the Fifth ACM SIGPLAN Symposium on
 * Principles and Practice of Parallel Programming (PPoPP), pages 207-216,
 * Santa Barbara, California, July 1995.
 * http://supertech.csail.mit.edu/papers/PPoPP95.pdf
 *
 * However, that refers to an outdated model of Cilk; an update appears in
 * the essential idea of work stealing mentioned in Leiserson and Platt,
 * Programming Parallel Applications in Cilk
 */

#include <assert.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <unistd.h>

#ifndef ELEM_T
#define ELEM_T uint32_t
#endif

int num_compare(const void *a, const void *b)
{
    return (*(ELEM_T *) a - *(ELEM_T *) b);
}


struct work_internal;

/* A 'task_t' represents a function pointer that accepts a pointer to a 'work_t'
 * struct as input and returns another 'work_t' struct as output. The input to
 * this function is always a pointer to the encompassing 'work_t' struct.
 *
 * It is worth considering whether to include information about the executing
 * thread's identifier when invoking the task. This information might be
 * beneficial for supporting thread-local accumulators in cases of commutative
 * reductions. Additionally, it could be useful to determine the destination
 * worker's queue for appending further tasks.
 *
 * The 'task_t' trampoline is responsible for delivering the subsequent unit of
 * work to be executed. It returns the next work item if it is prepared for
 * execution, or NULL if the task is not ready to proceed.
 */
typedef struct work_internal *(*task_t)(struct work_internal *);

typedef struct work_internal {
    task_t code;
    atomic_int join_count;
    atomic_int do_id;
    void *args[];
} work_t;

/* These are non-NULL pointers that will result in page faults under normal
 * circumstances, used to verify that nobody uses non-initialized entries.
 */
static work_t *EMPTY = (work_t *) 0x100, *ABORT = (work_t *) 0x200;

/* work_t-stealing deque */

typedef struct {
    atomic_size_t size;
    _Atomic work_t *buffer[];
} array_t;

typedef struct {
    /* Assume that they never overflow */
    atomic_size_t top, bottom;
    _Atomic(array_t *) array;
} deque_t;

void init(deque_t *q, int size_hint)
{
    atomic_init(&q->top, 0);
    atomic_init(&q->bottom, 0);
    array_t *a = malloc(sizeof(array_t) + sizeof(work_t *) * size_hint);
    atomic_init(&a->size, size_hint);
    atomic_init(&q->array, a);
}

void resize(deque_t *q)
{
    array_t *a = atomic_load_explicit(&q->array, memory_order_relaxed);
    size_t old_size = a->size;

    size_t new_size = old_size * 2;
    array_t *new = malloc(sizeof(array_t) + sizeof(work_t *) * new_size);

    atomic_init(&new->size, new_size);
    size_t t = atomic_load_explicit(&q->top, memory_order_relaxed);
    size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed);
    for (size_t i = t; i < b; i++)
        new->buffer[i % new_size] = a->buffer[i % old_size];

    atomic_store_explicit(&q->array, new, memory_order_relaxed);
    /* The question arises as to the appropriate timing for releasing memory
     * associated with the previous array denoted by *a. In the original Chase
     * and Lev paper, this task was undertaken by the garbage collector, which
     * presumably possessed knowledge about ongoing steal operations by other
     * threads that might attempt to access data within the array.
     *
     * In our context, the responsible deallocation of *a cannot occur at this
     * point, as another thread could potentially be in the process of reading
     * from it. Thus, we opt to abstain from freeing *a in this context,
     * resulting in memory leakage. It is worth noting that our expansion
     * strategy for these queues involves consistent doubling of their size;
     * this design choice ensures that any leaked memory remains bounded by the
     * memory actively employed by the functional queues.
     */
}

work_t *take(deque_t *q)
{
    size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed) - 1;
    array_t *a = atomic_load_explicit(&q->array, memory_order_relaxed);
    atomic_store_explicit(&q->bottom, b, memory_order_relaxed);
    atomic_thread_fence(memory_order_seq_cst);						// ---- seq_cst ----

    size_t t = atomic_load_explicit(&q->top, memory_order_relaxed);
    work_t *x;
    if (t <= b) {
        /* Non-empty queue */
        x = atomic_load_explicit(&a->buffer[b % a->size], memory_order_relaxed);
        if (t == b) {
            /* Single last element in queue */
            if (!atomic_compare_exchange_strong_explicit(&q->top, &t, t + 1,
                                                         memory_order_seq_cst,
                                                         memory_order_relaxed))		// ---- seq_cst ----
                /* Failed race */
                x = EMPTY;

            atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
        }
    } else {
	/* Empty queue */
        x = EMPTY;
        atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
    }
    return x;
}

void push(deque_t *q, work_t *w)
{
   
    //printf("[%s] enter: id=%d\n", __FUNCTION__, id);
    size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed);
    size_t t = atomic_load_explicit(&q->top, memory_order_acquire);			// ----- acquire ----
    array_t *a = atomic_load_explicit(&q->array, memory_order_relaxed);

    if (b - t > a->size - 1) { /* Full queue */
        resize(q);
        a = atomic_load_explicit(&q->array, memory_order_relaxed);
    }

    atomic_store_explicit(&a->buffer[b % a->size], w, memory_order_relaxed);
    atomic_thread_fence(memory_order_release);						// ---- release ----
    atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
}

work_t *steal(deque_t *q)
{
    size_t t = atomic_load_explicit(&q->top, memory_order_acquire);			// ---- acquire ----
    atomic_thread_fence(memory_order_seq_cst);						// ---- seq_cst ----

    size_t b = atomic_load_explicit(&q->bottom, memory_order_acquire);			// ---- acquire ----
											
    work_t *x = EMPTY;
    if (t < b) {
        /* Non-empty queue */
        array_t *a = atomic_load_explicit(&q->array, memory_order_consume);		// ---- consume ----
        x = atomic_load_explicit(&a->buffer[t % a->size], memory_order_relaxed);
        if (!atomic_compare_exchange_strong_explicit(
                &q->top, &t, t + 1, memory_order_seq_cst, memory_order_relaxed)) {	// ---- seq_cst ----
            /* Failed race */
	    //printf("abort\n");
            return ABORT;
	}
    }
    
    //if(x != EMPTY) printf("steal one\n");
    
    return x;
}

/******************************************************************************************************************************/

#define N_THREADS 	8
size_t nelem = 10000000;

deque_t 		*thread_queues;
atomic_bool 		done;

/* Returns the subsequent item available for processing, or NULL if no items
 * are remaining.
 */
static work_t *do_one_work(int id, work_t *work)
{
    printf("work item %d running item %p\n", id, work);
    atomic_store_explicit(&work->do_id, id, memory_order_relaxed);
    return (*(work->code)) (work);
}

void do_work(int id, work_t *work)
{
    while (work)
        work = do_one_work(id, work);
}

/* Returns the next item to be processed, or NULL if there are no remaining
 * items.
 */
work_t *join_work(work_t *work, int count_down)
{
    int old_join_count = atomic_fetch_sub(&work->join_count, count_down);
    //printf("old=%d, count_down=%d\n", old_join_count, count_down);
    if (old_join_count == count_down) {
        return work;
    }
    return NULL;
}

void *thread(void *payload)
{
    int id = *(int *) payload;
    deque_t *my_queue = &thread_queues[id];
    while (true) {
        work_t *work = take(my_queue);
        if (work != EMPTY) {
            do_work(id, work);
        } else {
            /* Currently, there is no work present in my own queue */
            work_t *stolen = EMPTY;
            for (int i = 0; i < N_THREADS; ++i) {
                if (i == id)
                    continue;
                stolen = steal(&thread_queues[i]);
                if (stolen == ABORT) {
                    i--;
                    continue; /* Try again at the same i */
                } else if (stolen == EMPTY)
                    continue;

                /* Found some work to do */
                break;
            }

            if (stolen == EMPTY) {
                /* Despite the previous observation of all queues being devoid
                 * of tasks during the last examination, there exists
                 * a possibility that additional work items have been introduced
                 * subsequently. To account for this scenario, a state of active
                 * waiting is adopted, wherein the program continues to loop
                 * until the global "done" flag becomes set, indicative of
                 * potential new work additions.
                 */
                if (atomic_load(&done))
                    break;
                continue;
            } else {
                do_work(id, stolen);
            }
        }
    }

    printf("work item %d finished\n", id);
    return NULL;
}

/***************************************************************************************************************/

static int qsort_algo(int do_id, void *a, size_t n);
typedef struct qsort_task_param {
    void 	*addr;
    size_t	n;
} param_t;

work_t *qsort_task(work_t *w)
{
    int do_id = w->do_id;
    param_t *param = (param_t *) w->args[0];
    void *addr = param->addr;
    size_t n = param->n;
    work_t *cont = (work_t *) w->args[1];

    //printf("Thread %d sorts from addr %p with n = %lu\n", do_id, addr, n);
    int count_down = qsort_algo(do_id, addr, n);	
    //printf("Thread %d get count_down = %d\n", do_id, count_down);
    //free(param);
    return join_work(cont, count_down);
}

work_t *done_task(work_t *w)
{
    free(w);
    atomic_store(&done, true);
    return NULL;
}

work_t *dummy_task(work_t *w)
{
    printf("Do dummy\n");
    return NULL;
}


/***********************************************************************************************************************/

ELEM_T *int_elem;
work_t *done_work;
//#define DEBUG

void usage(void)
{
    fprintf(
        stderr,
        "usage: ws_qsort [-tv] [-n elements]\n"
        "\t-t\tPrint timing results\n"
        "\t-v\tVerify the integer results\n"
        "Defaults are %lu elements, %d threads\n", nelem, N_THREADS);
    exit(1);
}


int main(int argc, char **argv)
{
    bool opt_time = false;
    bool opt_verify = false;
    int ch;
    char *ep;
    struct timeval start, end;
    struct rusage ru;

    gettimeofday(&start, NULL);
    while ((ch = getopt(argc, argv, "n:tv")) != -1) {
        switch (ch) {
        case 'n':
            int new_nelem = (size_t) strtol(optarg, &ep, 10);
            if (new_nelem == 0 || *ep != '\0') {
                warnx("illegal number, -n argument -- %s", optarg);
                usage();
            } else {
		nelem = new_nelem;
	    }
            break;
        case 't':
            opt_time = true;
            break;
        case 'v':
            opt_verify = true;
            break;
        case '?':
        default:
            usage();
        }
    }

    argc -= optind;
    argv += optind;

    printf("Threads = %d, elements = %ld\n", N_THREADS, nelem);

/*************************************************************************/
    
    /* Check that top and bottom are 64-bit so they never overflow */
    static_assert(sizeof(atomic_size_t) == 8,
                  "Assume atomic_size_t is 8 byte wide");

    int_elem = malloc(nelem * sizeof(ELEM_T));
    for (int i = 0; i < nelem; i++)
        int_elem[i] = rand() % nelem;

    printf("Generate\n");
#ifdef DEBUG
    for(int i = 0; i < nelem; i++)
        printf("%d ", int_elem[i]);
    printf("\n");
#endif

    /* do quick sort */
    pthread_t threads[N_THREADS];
    int tids[N_THREADS];
    thread_queues = malloc(N_THREADS * sizeof(deque_t));

    atomic_store(&done, false);
    done_work = malloc(sizeof(work_t));
    done_work->code = &done_task;
    done_work->join_count = nelem;
    done_work->do_id = N_THREADS;
    for (int i = 0; i < N_THREADS; ++i) {
        tids[i] = i;
        init(&thread_queues[i], 8);

	work_t *dummy_work = malloc(sizeof(work_t));
        dummy_work->code = &dummy_task;
        dummy_work->join_count = 0;
        dummy_work->do_id = N_THREADS;
        push(&thread_queues[i], dummy_work);

    }
        
    work_t *work = malloc(sizeof(work_t) + 2 * sizeof(void *));
    work->code = &qsort_task;
    work->join_count = 0;
    work->do_id = N_THREADS;
    param_t *param = malloc(sizeof(param_t));
    param->addr = int_elem;
    param->n = nelem;
    work->args[0] = param;
    work->args[1] = done_work;
    push(&thread_queues[0], work);

    for (int i = 0; i < N_THREADS; ++i) {
        if (pthread_create(&threads[i], NULL, thread, &tids[i]) != 0) {
            perror("Failed to start the thread");
            exit(EXIT_FAILURE);
        }
    }

    for (int i = 0; i < N_THREADS; ++i) {
        if (pthread_join(threads[i], NULL) != 0) {
            perror("Failed to join the thread");
            exit(EXIT_FAILURE);
        }
    }
    printf("Done \n");
    
    gettimeofday(&end, NULL);
    getrusage(RUSAGE_SELF, &ru);
    if (opt_verify) {
        for (int i = 1; i < nelem; i++)
            if (int_elem[i - 1] > int_elem[i]) {
                fprintf(stderr,
                        "sort error at position %d: "
                        " %d > %d\n",
                        i, int_elem[i - 1], int_elem[i]);
                exit(2);
            }

	printf("Verify: OK\n");
    }

    if (opt_time) {
        printf(
            "Time: %.3g %.3g %.3g\n",
            (end.tv_sec - start.tv_sec) + (end.tv_usec - start.tv_usec) / 1e6,
            ru.ru_utime.tv_sec + ru.ru_utime.tv_usec / 1e6,
            ru.ru_stime.tv_sec + ru.ru_stime.tv_usec / 1e6);
    }


#ifdef DEBUG
    for(int i = 0; i < nelem; i++)
        printf("%d ", int_elem[i]);
    printf("\n");
#endif
    return 0;
}


/************************************************************************************************/

#define verify(x)                                                      \
    do {                                                               \
        int e;                                                         \
        if ((e = x) != 0) {                                            \
            fprintf(stderr, "%s(%d) %s: %s\n", __FILE__, __LINE__, #x, \
                    strerror(e));                                      \
            exit(1);                                                   \
        }                                                              \
    } while (0)

typedef int cmp_t(const void *, const void *);
static inline char *med3(char *, char *, char *, cmp_t *, void *);
static inline void swapfunc(char *, char *, int, int);

#define min(a, b)           \
    ({                      \
        typeof(a) _a = (a); \
        typeof(b) _b = (b); \
        _a < _b ? _a : _b;  \
    })

/* Qsort routine from Bentley & McIlroy's "Engineering a Sort Function" */
#define swapcode(TYPE, parmi, parmj, n) \
    {                                   \
        long i = (n) / sizeof(TYPE);    \
        TYPE *pi = (TYPE *) (parmi);    \
        TYPE *pj = (TYPE *) (parmj);    \
        do {                            \
            TYPE t = *pi;               \
            *pi++ = *pj;                \
            *pj++ = t;                  \
        } while (--i > 0);              \
    }

static inline void swapfunc(char *a, char *b, int n, int swaptype)
{
    if (swaptype <= 1)
        swapcode(long, a, b, n) else swapcode(char, a, b, n)
}

#define swap(a, b)                         \
    do {                                   \
        if (swaptype == 0) {               \
            long t = *(long *) (a);        \
            *(long *) (a) = *(long *) (b); \
            *(long *) (b) = t;             \
        } else                             \
            swapfunc(a, b, es, swaptype);  \
    } while (0)

#define vecswap(a, b, n)                 \
    do {                                 \
        if ((n) > 0)                     \
            swapfunc(a, b, n, swaptype); \
    } while (0)

#define CMP(t, x, y) (cmp((x), (y)))

static inline char *med3(char *a, char *b, char *c, cmp_t *cmp, void *thunk)
{
    return CMP(thunk, a, b) < 0
               ? (CMP(thunk, b, c) < 0 ? b : (CMP(thunk, a, c) < 0 ? c : a))
               : (CMP(thunk, b, c) > 0 ? b : (CMP(thunk, a, c) < 0 ? a : c));
}

#define thunk NULL

void dump(void *a, size_t n) {
#ifdef DEBUG
	ELEM_T* array = (ELEM_T *)a;
	printf("dump: ");
	for(int i=0; i<n; i++) 
		printf("%u ", array[i]);
	printf("\n");
#endif
}

static int qsort_algo(int do_id, void *a, size_t n)
{
    //printf("[%s] %d enter: with addr %p, len=%lu\n", __FUNCTION__, do_id, a, n);
    /* data from qs */
    size_t es = sizeof(ELEM_T);
    cmp_t *cmp = num_compare;
    int swaptype = 2;

    char *pl, *pm, *pn;
    char *pa, *pb, *pc, *pd;
    int d, r, swap_cnt;

    int nl, nr;

    /* From here on qsort(3) business as usual. */
    swap_cnt = 0;

    /* 1. boundary condition */
    if (n < 7) { /* insertion sort */
        for (pm = (char *) a + es; pm < (char *) a + n * es; pm += es)
            for (pl = pm; pl > (char *) a && CMP(thunk, pl - es, pl) > 0; pl -= es)
                swap(pl, pl - es);

	//printf("[%s] %d exit1: with addr %p, len=%lu, return=%lu\n", __FUNCTION__, do_id, a, n, n);
	dump(a, n);
	return n;
    }

    /* 2. choose a good pivot and swap the value to a */
    pm = (char *) a + (n / 2) * es;
    if (n > 7) {
        pl = (char *) a;
        pn = (char *) a + (n - 1) * es;
        if (n > 40) {
            d = (n / 8) * es;
            pl = med3(pl, pl + d, pl + 2 * d, cmp, thunk);
            pm = med3(pm - d, pm, pm + d, cmp, thunk);
            pn = med3(pn - 2 * d, pn - d, pn, cmp, thunk);
        }
        pm = med3(pl, pm, pn, cmp, thunk);
    }
    swap(a, pm);

    /* 3. Quick Sort: divide part (one round) */
    pa = pb = (char *) a + es;
    pc = pd = (char *) a + (n - 1) * es;
    for (;;) {
        while (pb <= pc && (r = CMP(thunk, pb, a)) <= 0) {
	    if (r == 0) {
                swap_cnt = 1;
                swap(pa, pb);
                pa += es;
            }
            pb += es;
        }

        while (pc >= pb && (r = CMP(thunk, pc, a)) >= 0) {
    	    if (r == 0) {
                swap_cnt = 1;
                swap(pc, pd);
                pd -= es;
            }
            pc -= es;
        }

        if (pb > pc)
            break;

        swap(pb, pc);
        swap_cnt = 1;
        pb += es;
        pc -= es;
    }

    /* 4. Fasten quict sort: swap if(r == 0) part */
    
    pn = (char *) a + n * es;
    r = min(pa - (char *) a, pb - pa);
    vecswap(a, pb - r, r);
    r = min(pd - pc, pn - pd - es);
    vecswap(pb, pn - r, r);
    

    /* 5. Fasten quick sort: reason??? */
    
    if (swap_cnt == 0) { // Switch to insertion sort
        r = 1 + n / 4;   // n >= 7, so r >= 2
        for (pm = (char *) a + es; pm < (char *) a + n * es; pm += es)
            for (pl = pm; pl > (char *) a && CMP(thunk, pl - es, pl) > 0; pl -= es) {
                swap(pl, pl - es);
                if (++swap_cnt > r)
                    goto nevermind;
            }

        //printf("[%s] %d exit2: with addr %p, len=%lu, return=%lu\n", __FUNCTION__, do_id, a, n, n);
	dump(a, n);
        return n;
    }
    

nevermind:
    /* 6 Quick Sort: conquer part */
    nl = (pb - pa) / es;
    nr = (pd - pc) / es;

    //printf("[%s] %d step1: divide into %d %d\n", __FUNCTION__, do_id, nl, nr);
    dump(a, n);
    /* Now try to launch subthreads */
    /* Strategy:
     * 1. if both nl and nr are too small, we tend to sort them in this thread directly 
     * 2. if every thread is bust, we will sort them in this thread
     */
    if (nl > 0) {
        void *a1 = a;
        int n1 = nl;
        //printf("[%s] %d step2a: push left from %p n = %d\n", __FUNCTION__, do_id, a1, n1);
	
        work_t *work = malloc(sizeof(work_t) + 2 * sizeof(void *));
    	work->code = &qsort_task;
    	work->join_count = 0;
	work->do_id = N_THREADS;
    	param_t *param = malloc(sizeof(param_t));
    	param->addr = a1;
    	param->n = n1;
    	work->args[0] = param;
    	work->args[1] = done_work;
    	push(&thread_queues[do_id], work);
    }

    if (nr > 0) {
        void *a2 = pn - nr * es;
        int n2 = nr;
        //printf("[%s] %d step2b: push right from %p n = %d\n", __FUNCTION__, do_id, a2, n2);
        
	work_t *work = malloc(sizeof(work_t) + 2 * sizeof(void *));
    	work->code = &qsort_task;
    	work->join_count = 0;
	work->do_id = N_THREADS;
    	param_t *param = malloc(sizeof(param_t));
    	param->addr = a2;
    	param->n = n2;
    	work->args[0] = param;
    	work->args[1] = done_work;
    	push(&thread_queues[do_id], work);
    }

    //printf("[%s] %d exit3: with addr %p, len=%lu, n1=%d n2=%d ret=%lu top=%lu bottom=%lu\n", __FUNCTION__, do_id, a, n, nl, nr, n-nl-nr,
    //		    			atomic_load_explicit(&(&thread_queues[do_id])->top, memory_order_relaxed),	
    //					atomic_load_explicit(&(&thread_queues[do_id])->bottom, memory_order_relaxed));
    dump(a, n);
    return n - nl - nr;
}

