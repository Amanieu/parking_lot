// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#[cfg(feature = "nightly")]
use std::sync::atomic::{AtomicUsize, ATOMIC_USIZE_INIT, Ordering};
#[cfg(not(feature = "nightly"))]
use stable::{AtomicUsize, ATOMIC_USIZE_INIT, Ordering};
use std::time::Instant;
use std::cell::Cell;
use std::ptr;
use std::mem;
use smallvec::SmallVec8;
use thread_parker::ThreadParker;
use word_lock::WordLock;

static NUM_THREADS: AtomicUsize = ATOMIC_USIZE_INIT;
static HASHTABLE: AtomicUsize = ATOMIC_USIZE_INIT;
thread_local!(static THREAD_DATA: ThreadData = ThreadData::new());

// Even with 3x more buckets than threads, the memory overhead per thread is
// still only a few hundred bytes per thread.
const LOAD_FACTOR: usize = 3;

struct HashTable {
    // Hash buckets for the table
    entries: Box<[Bucket]>,

    // Number of bits used for the hash function
    hash_bits: u32,

    // Previous table. This is only kept to keep leak detectors happy.
    _prev: *const HashTable,
}

impl HashTable {
    fn new(num_threads: usize, prev: *const HashTable) -> Box<HashTable> {
        let new_size = (num_threads * LOAD_FACTOR).next_power_of_two();
        let hash_bits = 0usize.leading_zeros() - new_size.leading_zeros() - 1;
        let bucket = Bucket {
            mutex: WordLock::new(),
            queue_head: Cell::new(ptr::null()),
            queue_tail: Cell::new(ptr::null()),
            _padding: unsafe { mem::uninitialized() },
        };
        Box::new(HashTable {
            entries: vec![bucket; new_size].into_boxed_slice(),
            hash_bits: hash_bits,
            _prev: prev,
        })
    }
}

struct Bucket {
    // Lock protecting the queue
    mutex: WordLock,

    // Linked list of threads waiting on this bucket
    queue_head: Cell<*const ThreadData>,
    queue_tail: Cell<*const ThreadData>,

    // Padding to avoid false sharing between buckets. Ideally we would just
    // align the bucket structure to 64 bytes, but Rust doesn't support that yet.
    _padding: [u8; 64],
}

// Implementation of Clone for Bucket, needed to make vec![] work
impl Clone for Bucket {
    fn clone(&self) -> Bucket {
        Bucket {
            mutex: WordLock::new(),
            queue_head: Cell::new(ptr::null()),
            queue_tail: Cell::new(ptr::null()),
            _padding: unsafe { mem::uninitialized() },
        }
    }
}

struct ThreadData {
    parker: ThreadParker,
    key: AtomicUsize,
    next_in_queue: Cell<*const ThreadData>,
}

impl ThreadData {
    fn new() -> ThreadData {
        // Keep track of the total number of live ThreadData objects and resize
        // the hash table accordingly.
        let num_threads = NUM_THREADS.fetch_add(1, Ordering::Relaxed) + 1;
        unsafe {
            grow_hashtable(num_threads);
        }

        ThreadData {
            parker: ThreadParker::new(),
            key: AtomicUsize::new(0),
            next_in_queue: Cell::new(ptr::null()),
        }
    }
}

impl Default for ThreadData {
    fn default() -> ThreadData {
        ThreadData::new()
    }
}

impl Drop for ThreadData {
    fn drop(&mut self) {
        NUM_THREADS.fetch_sub(1, Ordering::Relaxed);
    }
}

// Get a pointer to the latest hash table, creating one if it doesn't exist yet.
unsafe fn get_hashtable() -> *const HashTable {
    let mut table = HASHTABLE.load(Ordering::Acquire);

    // If there is no table, create one
    if table == 0 {
        let new_table = Box::into_raw(HashTable::new(LOAD_FACTOR, ptr::null()));

        // If this fails then it means some other thread created the hash
        // table first.
        match HASHTABLE.compare_exchange(0,
                                         new_table as usize,
                                         Ordering::Release,
                                         Ordering::Relaxed) {
            Ok(_) => return new_table,
            Err(x) => table = x,
        }

        // Free the table we created
        Box::from_raw(new_table);
    }

    table as *const HashTable
}

// Grow the hash table so that it is big enough for the given number of threads.
// This isn't performance-critical since it is only done when a ThreadData is
// created, which only happens once per thread.
unsafe fn grow_hashtable(num_threads: usize) {
    // If there is no table, create one
    if HASHTABLE.load(Ordering::Relaxed) == 0 {
        let new_table = Box::into_raw(HashTable::new(num_threads, ptr::null()));

        // If this fails then it means some other thread created the hash
        // table first.
        if HASHTABLE.compare_exchange(0, new_table as usize, Ordering::Release, Ordering::Relaxed)
            .is_ok() {
            return;
        }

        // Free the table we created
        Box::from_raw(new_table);
    }

    let mut old_table;
    loop {
        old_table = HASHTABLE.load(Ordering::Acquire) as *mut HashTable;

        // Check if we need to resize the existing table
        if (*old_table).entries.len() >= LOAD_FACTOR * num_threads {
            return;
        }

        // Lock all buckets in the old table
        for b in &(*old_table).entries[..] {
            b.mutex.lock();
        }

        // Now check if our table is still the latest one. Another thread could
        // have grown the hash table between us reading HASHTABLE and locking
        // the buckets.
        if HASHTABLE.load(Ordering::Relaxed) == old_table as usize {
            break;
        }

        // Unlock buckets and try again
        for b in &(*old_table).entries[..] {
            b.mutex.unlock();
        }
    }

    // Create the new table
    let new_table = HashTable::new(num_threads, old_table);

    // Move the entries from the old table to the new one
    for b in &(*old_table).entries[..] {
        let mut current = b.queue_head.get();
        while !current.is_null() {
            let next = (*current).next_in_queue.get();
            let hash = hash((*current).key.load(Ordering::Relaxed), new_table.hash_bits);
            if new_table.entries[hash].queue_tail.get().is_null() {
                new_table.entries[hash].queue_head.set(current);
            } else {
                (*new_table.entries[hash].queue_tail.get()).next_in_queue.set(current);
            }
            new_table.entries[hash].queue_tail.set(current);
            (*current).next_in_queue.set(ptr::null());
            current = next;
        }
    }

    // Publish the new table. No races are possible at this point because
    // any other thread trying to grow the hash table is blocked on the bucket
    // locks in the old table.
    HASHTABLE.store(Box::into_raw(new_table) as usize, Ordering::Release);

    // Unlock all buckets in the old table
    for b in &(*old_table).entries[..] {
        b.mutex.unlock();
    }
}

// Hash function for addresses
#[cfg(target_pointer_width = "32")]
fn hash(key: usize, bits: u32) -> usize {
    key.wrapping_mul(0x9E3779B9) >> (32 - bits)
}
#[cfg(target_pointer_width = "64")]
fn hash(key: usize, bits: u32) -> usize {
    key.wrapping_mul(0x9E3779B97F4A7C15) >> (64 - bits)
}

// Lock the bucket for the given key
unsafe fn lock_bucket<'a>(key: usize) -> &'a Bucket {
    let mut bucket;
    loop {
        let hashtable = get_hashtable();

        let hash = hash(key, (*hashtable).hash_bits);
        bucket = &(*hashtable).entries[hash];

        // Lock the bucket
        bucket.mutex.lock();

        // If no other thread has rehashed the table before we grabbed the lock
        // then we are good to go! The lock we grabbed prevents any rehashes.
        if HASHTABLE.load(Ordering::Relaxed) == hashtable as usize {
            return bucket;
        }

        // Unlock the bucket and try again
        bucket.mutex.unlock();
    }
}

// Lock the bucket for the given key, but check that the key hasn't been changed
// in the meantime due to a requeue.
unsafe fn lock_bucket_checked<'a>(key: &AtomicUsize) -> (usize, &'a Bucket) {
    let mut bucket;
    loop {
        let hashtable = get_hashtable();
        let current_key = key.load(Ordering::Relaxed);

        let hash = hash(current_key, (*hashtable).hash_bits);
        bucket = &(*hashtable).entries[hash];

        // Lock the bucket
        bucket.mutex.lock();

        // Check that both the hash table and key are correct while the bucket
        // is locked. Note that the key can't change once we locked the proper
        // bucket for it, so we just keep trying until we have the correct key.
        if HASHTABLE.load(Ordering::Relaxed) == hashtable as usize &&
           key.load(Ordering::Relaxed) == current_key {
            return (current_key, bucket);
        }

        // Unlock the bucket and try again
        bucket.mutex.unlock();
    }
}

// Lock the two buckets for the given pair of keys
unsafe fn lock_bucket_pair<'a>(key1: usize, key2: usize) -> (&'a Bucket, &'a Bucket) {
    let mut bucket1;
    loop {
        let hashtable = get_hashtable();

        // Get the lowest bucket first
        let hash1 = hash(key1, (*hashtable).hash_bits);
        let hash2 = hash(key2, (*hashtable).hash_bits);
        if hash1 <= hash2 {
            bucket1 = &(*hashtable).entries[hash1];
        } else {
            bucket1 = &(*hashtable).entries[hash2];
        }

        // Lock the first bucket
        bucket1.mutex.lock();

        // If no other thread has rehashed the table before we grabbed the lock
        // then we are good to go! The lock we grabbed prevents any rehashes.
        if HASHTABLE.load(Ordering::Relaxed) == hashtable as usize {
            // Now lock the second bucket and return the two buckets
            if hash1 == hash2 {
                return (bucket1, bucket1);
            } else if hash1 < hash2 {
                let bucket2 = &(*hashtable).entries[hash2];
                bucket2.mutex.lock();
                return (bucket1, bucket2);
            } else {
                let bucket2 = &(*hashtable).entries[hash1];
                bucket2.mutex.lock();
                return (bucket2, bucket1);
            }
        }

        // Unlock the bucket and try again
        bucket1.mutex.unlock();
    }
}

// Unlock a pair of buckets
unsafe fn unlock_bucket_pair(bucket1: &Bucket, bucket2: &Bucket) {
    if bucket1 as *const _ == bucket2 as *const _ {
        bucket1.mutex.unlock();
    } else if bucket1 as *const _ < bucket2 as *const _ {
        bucket2.mutex.unlock();
        bucket1.mutex.unlock();
    } else {
        bucket1.mutex.unlock();
        bucket2.mutex.unlock();
    }
}

/// Result of an `unpark_one` operation.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum UnparkResult {
    /// No parked threads were found for the given key.
    NoParkedThreads,

    /// One thread was unparked and it was one in the queue.
    UnparkedLast,

    /// One thread was unparked but there are more in the queue.
    UnparkedNotLast,
}

/// Operation that `unpark_requeue` should perform.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum RequeueOp {
    /// Abort the operation without doing anything.
    Abort,

    /// Unpark one thread and requeue the rest onto the target queue.
    UnparkOneRequeueRest,

    /// Requeue all threads onto the target queue.
    RequeueAll,
}

/// Parks the current thread in the queue associated with the given key.
///
/// The `validate` function is called while the queue is locked and can abort
/// the operation by returning false. If `validate` returns true then the
/// current thread is appended to the queue and the queue is unlocked.
///
/// The `before_sleep` function is called after the queue is unlocked but before
/// the thread is put to sleep. The thread will then sleep until it is unparked
/// or the given timeout is reached.
///
/// The `timed_out` function is also called while the queue is locked, but only
/// if the timeout was reached. It is passed the key of the queue it was in when
/// it timed out, which may be different from the original key if
/// `unpark_requeue` was called. It is also passed an `UnparkResult` which
/// indicates whether it is the last thread in the queue.
///
/// This function returns `true` if the thread was unparked by a call to
/// `unpark_one` or `unpark_all`, and `false` if the validation function failed
/// or the timeout was reached.
///
/// # Safety
///
/// You should only call this function with an address that you control, since
/// you could otherwise interfere with the operation of other synchronization
/// primitives.
///
/// The `validate` and `timed_out` functions are called while the queue is
/// locked and must not panic or call into any function in `parking_lot`.
///
/// The `before_sleep` function is called outside the queue lock and is allowed
/// to call `unpark_one`, `unpark_all` or `unpark_requeue`, but it is not
/// allowed to call `park` or panic.
pub unsafe fn park(key: usize,
                   validate: &mut FnMut() -> bool,
                   before_sleep: &mut FnMut(),
                   timed_out: &mut FnMut(usize, UnparkResult),
                   timeout: Option<Instant>)
                   -> bool {
    // Grab our thread data, this also ensures that the hash table exists
    let thread_data = &*THREAD_DATA.with(|x| x as *const ThreadData);

    // Lock the bucket for the given key
    let bucket = lock_bucket(key);

    // If the validation function fails, just return
    if !validate() {
        bucket.mutex.unlock();
        return false;
    }

    // Append our thread data to the queue and unlock the bucket
    thread_data.next_in_queue.set(ptr::null());
    thread_data.key.store(key, Ordering::Relaxed);
    thread_data.parker.prepare_park();
    if !bucket.queue_head.get().is_null() {
        (*bucket.queue_tail.get()).next_in_queue.set(thread_data);
    } else {
        bucket.queue_head.set(thread_data);
    }
    bucket.queue_tail.set(thread_data);
    bucket.mutex.unlock();

    // Invoke the pre-sleep callback
    before_sleep();

    // Park our thread and determine whether we were woken up by an unpark or by
    // our timeout. Note that this isn't precise: we can still be unparked since
    // we are still in the queue.
    let unparked = match timeout {
        Some(timeout) => thread_data.parker.park_until(timeout),
        None => {
            thread_data.parker.park();
            true
        }
    };

    // If we were unparked, return now
    if unparked {
        return true;
    }

    // Lock our bucket again. Note that the hashtable may have been rehashed in
    // the meantime. Our key may also have changed if we were requeued.
    let (key, bucket) = lock_bucket_checked(&thread_data.key);

    // Now we need to check again if we were unparked or timed out. Unlike the
    // last check this is precise because we hold the bucket lock.
    if !thread_data.parker.timed_out() {
        bucket.mutex.unlock();
        return true;
    }

    // We timed out, so we now need to remove our thread from the queue
    let mut link = &bucket.queue_head;
    let mut current = bucket.queue_head.get();
    let mut previous = ptr::null();
    while !current.is_null() {
        if current == thread_data {
            let next = (*current).next_in_queue.get();
            link.set(next);
            let mut result = UnparkResult::UnparkedLast;
            if bucket.queue_tail.get() == current {
                bucket.queue_tail.set(previous);
            } else {
                // Scan the rest of the queue to see if there are any other
                // entries with the given key.
                let mut scan = next;
                while !scan.is_null() {
                    if (*scan).key.load(Ordering::Relaxed) == key {
                        result = UnparkResult::UnparkedNotLast;
                        break;
                    }
                    scan = (*scan).next_in_queue.get();
                }
            }

            // Callback to indicate that we timed out, and whether we were the
            // last thread on the queue.
            timed_out(key, result);
            break;
        } else {
            link = &(*current).next_in_queue;
            previous = current;
            current = link.get();
        }
    }

    // Unlock the bucket, we are done
    bucket.mutex.unlock();
    false
}

/// Unparks one thread from the queue associated with the given key.
///
/// The `callback` function is called while the queue is locked and before the
/// target thread is woken up. The `UnparkResult` argument to the function
/// indicates whether a thread was found in the queue and whether this was the
/// last thread in the queue. This value is also returned by `unpark_one`.
///
/// # Safety
///
/// You should only call this function with an address that you control, since
/// you could otherwise interfere with the operation of other synchronization
/// primitives.
///
/// The `callback` function is called while the queue is locked and must not
/// panic or call into any function in `parking_lot`.
pub unsafe fn unpark_one(key: usize, callback: &mut FnMut(UnparkResult)) -> UnparkResult {
    // Lock the bucket for the given key
    let bucket = lock_bucket(key);

    // Find a thread with a matching key and remove it from the queue
    let mut link = &bucket.queue_head;
    let mut current = bucket.queue_head.get();
    let mut previous = ptr::null();
    while !current.is_null() {
        if (*current).key.load(Ordering::Relaxed) == key {
            // Remove the thread from the queue
            let next = (*current).next_in_queue.get();
            link.set(next);
            let mut result = UnparkResult::UnparkedLast;
            if bucket.queue_tail.get() == current {
                bucket.queue_tail.set(previous);
            } else {
                // Scan the rest of the queue to see if there are any other
                // entries with the given key.
                let mut scan = next;
                while !scan.is_null() {
                    if (*scan).key.load(Ordering::Relaxed) == key {
                        result = UnparkResult::UnparkedNotLast;
                        break;
                    }
                    scan = (*scan).next_in_queue.get();
                }
            }

            // Invoke the callback before waking up the thread
            callback(result);

            // This is a bit tricky: we first lock the ThreadParker to prevent
            // the thread from exiting and freeing its ThreadData if its wait
            // times out. Then we unlock the queue since we don't want to keep
            // the queue locked while we perform a system call. Finally we wake
            // up the parked thread.
            let lock = (*current).parker.unpark_lock();
            bucket.mutex.unlock();
            (*current).parker.unpark(lock);

            return result;
        } else {
            link = &(*current).next_in_queue;
            previous = current;
            current = link.get();
        }
    }

    // No threads with a matching key were found in the bucket
    callback(UnparkResult::NoParkedThreads);
    bucket.mutex.unlock();
    UnparkResult::NoParkedThreads
}

/// Unparks all threads in the queue associated with the given key.
///
/// This function returns the number of threads that were unparked.
///
/// # Safety
///
/// You should only call this function with an address that you control, since
/// you could otherwise interfere with the operation of other synchronization
/// primitives.
pub unsafe fn unpark_all(key: usize) -> usize {
    // Lock the bucket for the given key
    let bucket = lock_bucket(key);

    // Remove all threads with the given key in the bucket
    let mut link = &bucket.queue_head;
    let mut current = bucket.queue_head.get();
    let mut previous = ptr::null();
    let mut threads = SmallVec8::new();
    while !current.is_null() {
        if (*current).key.load(Ordering::Relaxed) == key {
            // Remove the thread from the queue
            let next = (*current).next_in_queue.get();
            link.set(next);
            if bucket.queue_tail.get() == current {
                bucket.queue_tail.set(previous);
            }

            // Don't wake up threads while holding the queue lock. See comment
            // in unpark_one. For now just record which threads we need to wake
            // up.
            threads.push((current, (*current).parker.unpark_lock()));
            current = next;
        } else {
            link = &(*current).next_in_queue;
            previous = current;
            current = link.get();
        }
    }

    // Unlock the bucket
    bucket.mutex.unlock();

    // Now that we are outside the lock, wake up all the threads that we removed
    // from the queue.
    let num_threads = threads.len();
    for t in threads.into_iter() {
        (*t.0).parker.unpark(t.1);
    }

    num_threads
}

/// Removes all threads from the queue associated with `key_from`, optionally
/// unparks the first one and requeues the rest onto the queue associated with
/// `key_to`.
///
/// The `validate` function is called while both queues are locked and can abort
/// the operation by returning `RequeueOp::Abort`. It can also choose to
/// unpark the first thread in the source queue while moving the rest by
/// returning `RequeueOp::UnparkFirstRequeueRest`. Returning
/// `RequeueOp::RequeueAll` will move all threads to the destination queue.
///
/// The `callback` function is also called while both queues are locked. It is
/// passed the `RequeueOp` returned by `validate` and the number of threads that
/// were removed from the original queue.
///
/// This function returns the number of threads that were removed from the
/// original queue.
///
/// # Safety
///
/// You should only call this function with an address that you control, since
/// you could otherwise interfere with the operation of other synchronization
/// primitives.
///
/// The `validate` and `callback` functions are called while the queue is locked
/// and must not panic or call into any function in `parking_lot`.
pub unsafe fn unpark_requeue(key_from: usize,
                             key_to: usize,
                             validate: &mut FnMut() -> RequeueOp,
                             callback: &mut FnMut(RequeueOp, usize))
                             -> usize {
    // Lock the two buckets for the given key
    let (bucket_from, bucket_to) = lock_bucket_pair(key_from, key_to);

    // If the validation function fails, just return
    let op = validate();
    if op == RequeueOp::Abort {
        unlock_bucket_pair(bucket_from, bucket_to);
        return 0;
    }

    // Remove all threads with the given key in the source bucket
    let mut link = &bucket_from.queue_head;
    let mut current = bucket_from.queue_head.get();
    let mut previous = ptr::null();
    let mut requeue_threads = ptr::null();
    let mut requeue_threads_tail: *const ThreadData = ptr::null();
    let mut wakeup_thread = None;
    let mut num_threads = 0;
    while !current.is_null() {
        if (*current).key.load(Ordering::Relaxed) == key_from {
            // Remove the thread from the queue
            let next = (*current).next_in_queue.get();
            link.set(next);
            if bucket_from.queue_tail.get() == current {
                bucket_from.queue_tail.set(previous);
            }

            // Prepare the first thread for wakeup and requeue the rest.
            if op == RequeueOp::UnparkOneRequeueRest && wakeup_thread.is_none() {
                wakeup_thread = Some(current);
            } else {
                if !requeue_threads.is_null() {
                    (*requeue_threads_tail).next_in_queue.set(current);
                } else {
                    requeue_threads = current;
                }
                requeue_threads_tail = current;
                (*current).key.store(key_to, Ordering::Relaxed);
            }
            num_threads += 1;
            current = next;
        } else {
            link = &(*current).next_in_queue;
            previous = current;
            current = link.get();
        }
    }

    // Add the requeued threads to the destination bucket
    if !requeue_threads.is_null() {
        (*requeue_threads_tail).next_in_queue.set(ptr::null());
        if !bucket_to.queue_head.get().is_null() {
            (*bucket_to.queue_tail.get()).next_in_queue.set(requeue_threads);
        } else {
            bucket_to.queue_head.set(requeue_threads);
        }
        bucket_to.queue_tail.set(requeue_threads_tail);
    }

    // Invoke the callback before waking up the thread
    callback(op, num_threads);

    // See comment in unpark_one for why we mess with the locking
    if let Some(wakeup_thread) = wakeup_thread {
        let lock = (*wakeup_thread).parker.unpark_lock();
        unlock_bucket_pair(bucket_from, bucket_to);
        (*wakeup_thread).parker.unpark(lock);
    } else {
        unlock_bucket_pair(bucket_from, bucket_to);
    }

    num_threads
}
