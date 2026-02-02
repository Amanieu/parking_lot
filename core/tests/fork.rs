//! Test that parking_lot_core works correctly after fork().
//!
//! After fork(), the child inherits the parent's global hash table with stale
//! ThreadData pointers from dead threads. Without the fork-safety fix, park()
//! dereferences these and segfaults.

#![cfg(all(unix, feature = "fork"))]

use parking_lot_core::{park, unpark_one, DEFAULT_PARK_TOKEN, DEFAULT_UNPARK_TOKEN};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

/// Park a thread in the parent to populate the global hash table, then fork
/// and exercise park()/unpark_one() in the child. Repeated to catch races.
#[test]
fn park_after_fork() {
    for _ in 0..20 {
        // Park a background thread so the global hash table has entries.
        let flag = Arc::new(AtomicBool::new(false));
        let flag2 = flag.clone();
        let bg = thread::spawn(move || {
            let addr = &*flag2 as *const _ as usize;
            unsafe {
                park(
                    addr,
                    || !flag2.load(Ordering::Relaxed),
                    || {},
                    |_, _| {},
                    DEFAULT_PARK_TOKEN,
                    None,
                );
            }
        });
        thread::sleep(Duration::from_millis(20));

        // Fork. Child inherits stale hash table.
        let pid = unsafe { libc::fork() };
        assert!(pid >= 0, "fork() failed");

        if pid == 0 {
            // Child: exercise the actual park()/unpark() slow path on a
            // fresh key. This would segfault without the fix.
            let state = Arc::new(AtomicUsize::new(0));
            let s2 = state.clone();
            let t = thread::spawn(move || {
                let addr = &*s2 as *const _ as usize;
                unsafe {
                    park(
                        addr,
                        || s2.load(Ordering::Acquire) == 0,
                        || {},
                        |_, _| {},
                        DEFAULT_PARK_TOKEN,
                        None,
                    );
                }
            });
            thread::sleep(Duration::from_millis(10));
            state.store(1, Ordering::Release);
            unsafe { unpark_one(&*state as *const _ as usize, |_| DEFAULT_UNPARK_TOKEN) };
            t.join().unwrap();
            unsafe { libc::_exit(0) };
        }

        // Parent: wait for child, then clean up.
        let mut status: libc::c_int = 0;
        unsafe { libc::waitpid(pid, &mut status, 0) };
        assert!(
            libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 0,
            "child exited abnormally (status=0x{status:x})",
        );

        flag.store(true, Ordering::Relaxed);
        unsafe { unpark_one(&*flag as *const _ as usize, |_| DEFAULT_UNPARK_TOKEN) };
        bg.join().unwrap();
    }
}
