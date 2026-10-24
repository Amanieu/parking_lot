use parking_lot::RwLock;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};
use std::thread;
use std::time::Duration;

// A writer blocked on an upgradable read lock must not be barged by new
// readers: https://github.com/Amanieu/parking_lot/issues/543
#[test]
fn issue_543() {
    let lock = Arc::new(RwLock::new(()));
    let _upgradable = lock.upgradable_read();

    // Park a writer on the upgradable lock.
    let lock2 = lock.clone();
    let writer_acquired = Arc::new(AtomicUsize::new(0));
    let writer_acquired2 = writer_acquired.clone();
    let writer = thread::spawn(move || {
        let _guard = lock2.write();
        writer_acquired2.store(1, Ordering::SeqCst);
    });

    // Give the writer a chance to park. Parking takes microseconds; this
    // margin only affects test time, not correctness.
    thread::sleep(Duration::from_millis(200));
    assert_eq!(writer_acquired.load(Ordering::SeqCst), 0);

    // A new reader must block behind the waiting writer instead of barging
    // ahead of it.
    assert!(lock.try_read_for(Duration::from_millis(500)).is_none());

    // Releasing the upgradable lock hands it to the waiting writer.
    drop(_upgradable);
    writer.join().unwrap();
    assert_eq!(writer_acquired.load(Ordering::SeqCst), 1);

    // The lock is usable again afterwards.
    assert!(lock.try_read().is_some());
}

// Issue #101 (fixed by #112): a thread waiting for an *upgradable* lock must
// not block new readers. The #543 fix must not regress this.
#[test]
fn issue_543_upgradable_waiter_does_not_block_readers() {
    let lock = Arc::new(RwLock::new(()));
    let _upgradable = lock.upgradable_read();

    // Park an upgradable waiter (not a writer).
    let lock2 = lock.clone();
    let waiter = thread::spawn(move || {
        let _upgradable = lock2.upgradable_read();
    });

    thread::sleep(Duration::from_millis(200));

    // New readers are still granted while only an upgradable waiter is queued.
    assert!(lock.try_read_for(Duration::from_millis(500)).is_some());

    drop(_upgradable);
    waiter.join().unwrap();
}
