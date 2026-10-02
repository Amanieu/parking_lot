#![allow(dead_code)]

#[cfg(feature = "atomic_usize")]
use lock_api::{GetThreadId, MappedReentrantMutexGuard, ReentrantMutexGuard};
use lock_api::{
    GuardNoSend, GuardSend, MappedMutexGuard, MappedRwLockReadGuard, MappedRwLockWriteGuard,
    MutexGuard, RawMutex, RawRwLock, RawRwLockUpgrade, RwLockReadGuard, RwLockUpgradableReadGuard,
    RwLockWriteGuard,
};
use static_assertions::{assert_impl_all, assert_not_impl_any};
use std::cell::Cell;
use std::marker::PhantomData;
#[cfg(feature = "atomic_usize")]
use std::num::NonZeroUsize;
use std::rc::Rc;

#[cfg(all(feature = "arc_lock", feature = "atomic_usize"))]
use lock_api::ArcReentrantMutexGuard;
#[cfg(feature = "arc_lock")]
use lock_api::{
    ArcMutexGuard, ArcRwLockReadGuard, ArcRwLockUpgradableReadGuard, ArcRwLockWriteGuard,
};

struct SendSync;
struct SendNotSync(Cell<()>);
struct SyncNotSend(PhantomData<std::sync::MutexGuard<'static, ()>>);
struct Neither(PhantomData<Rc<()>>);

assert_impl_all!(SendSync: Send, Sync);
assert_impl_all!(SendNotSync: Send);
assert_not_impl_any!(SendNotSync: Sync);
assert_impl_all!(SyncNotSend: Sync);
assert_not_impl_any!(SyncNotSend: Send);
assert_not_impl_any!(Neither: Send, Sync);
assert_impl_all!(GuardSend: Send, Sync);
assert_impl_all!(GuardNoSend: Sync);
assert_not_impl_any!(GuardNoSend: Send);

// Used only for compile-time trait assertions.
struct TestRaw<T, M> {
    traits: PhantomData<T>,
    marker: PhantomData<fn() -> M>,
}

unsafe impl<T, M> RawMutex for TestRaw<T, M> {
    const INIT: Self = Self {
        traits: PhantomData,
        marker: PhantomData,
    };

    type GuardMarker = M;

    fn lock(&self) {
        unreachable!()
    }

    fn try_lock(&self) -> bool {
        unreachable!()
    }

    unsafe fn unlock(&self) {
        unreachable!()
    }

    fn is_locked(&self) -> bool {
        unreachable!()
    }
}

unsafe impl<T, M> RawRwLock for TestRaw<T, M> {
    const INIT: Self = Self {
        traits: PhantomData,
        marker: PhantomData,
    };

    type GuardMarker = M;

    fn lock_shared(&self) {
        unreachable!()
    }

    fn try_lock_shared(&self) -> bool {
        unreachable!()
    }

    unsafe fn unlock_shared(&self) {
        unreachable!()
    }

    fn lock_exclusive(&self) {
        unreachable!()
    }

    fn try_lock_exclusive(&self) -> bool {
        unreachable!()
    }

    unsafe fn unlock_exclusive(&self) {
        unreachable!()
    }

    fn is_locked(&self) -> bool {
        unreachable!()
    }

    fn is_locked_exclusive(&self) -> bool {
        unreachable!()
    }
}

unsafe impl<T, M> RawRwLockUpgrade for TestRaw<T, M> {
    fn lock_upgradable(&self) {
        unreachable!()
    }

    fn try_lock_upgradable(&self) -> bool {
        unreachable!()
    }

    unsafe fn unlock_upgradable(&self) {
        unreachable!()
    }

    unsafe fn upgrade(&self) {
        unreachable!()
    }

    unsafe fn try_upgrade(&self) -> bool {
        unreachable!()
    }
}

#[cfg(feature = "atomic_usize")]
struct TestThreadId<T>(PhantomData<T>);

#[cfg(feature = "atomic_usize")]
unsafe impl<T> GetThreadId for TestThreadId<T> {
    const INIT: Self = Self(PhantomData);

    fn nonzero_thread_id(&self) -> NonZeroUsize {
        unreachable!()
    }
}

type Raw<M = GuardSend> = TestRaw<SendSync, M>;
type RawSendOnly = TestRaw<SendNotSync, GuardSend>;
type RawSyncOnly = TestRaw<SyncNotSend, GuardSend>;
type RawNeither = TestRaw<Neither, GuardSend>;
type MarkerSendOnly = SendNotSync;

type LockMutex<R, T> = lock_api::Mutex<R, T>;
type LockRwLock<R, T> = lock_api::RwLock<R, T>;

assert_impl_all!(LockMutex<Raw, SendSync>: Send, Sync);
assert_impl_all!(LockMutex<RawSendOnly, SendSync>: Send);
assert_not_impl_any!(LockMutex<RawSendOnly, SendSync>: Sync);
assert_impl_all!(LockMutex<RawSyncOnly, SendSync>: Sync);
assert_not_impl_any!(LockMutex<RawSyncOnly, SendSync>: Send);
assert_not_impl_any!(LockMutex<RawNeither, SendSync>: Send, Sync);
assert_impl_all!(LockMutex<Raw, SendNotSync>: Send, Sync);
assert_not_impl_any!(LockMutex<Raw, SyncNotSend>: Send, Sync);

assert_impl_all!(LockRwLock<Raw, SendSync>: Send, Sync);
assert_impl_all!(LockRwLock<RawSendOnly, SendSync>: Send);
assert_not_impl_any!(LockRwLock<RawSendOnly, SendSync>: Sync);
assert_impl_all!(LockRwLock<RawSyncOnly, SendSync>: Sync);
assert_not_impl_any!(LockRwLock<RawSyncOnly, SendSync>: Send);
assert_not_impl_any!(LockRwLock<RawNeither, SendSync>: Send, Sync);
assert_impl_all!(LockRwLock<Raw, SendNotSync>: Send);
assert_not_impl_any!(LockRwLock<Raw, SendNotSync>: Sync);
assert_not_impl_any!(LockRwLock<Raw, SyncNotSend>: Send, Sync);

#[cfg(feature = "atomic_usize")]
mod reentrant_lock_traits {
    use super::*;

    type RawReentrant<R, G> = lock_api::RawReentrantMutex<R, G>;
    type LockReentrant<R, G, T> = lock_api::ReentrantMutex<R, G, T>;

    assert_impl_all!(RawReentrant<Raw, TestThreadId<SendSync>>: Send, Sync);
    assert_impl_all!(RawReentrant<RawSendOnly, TestThreadId<SendSync>>: Send);
    assert_not_impl_any!(RawReentrant<RawSendOnly, TestThreadId<SendSync>>: Sync);
    assert_impl_all!(RawReentrant<RawSyncOnly, TestThreadId<SendSync>>: Sync);
    assert_not_impl_any!(RawReentrant<RawSyncOnly, TestThreadId<SendSync>>: Send);
    assert_not_impl_any!(RawReentrant<RawNeither, TestThreadId<SendSync>>: Send, Sync);
    assert_impl_all!(RawReentrant<Raw, TestThreadId<SendNotSync>>: Send);
    assert_not_impl_any!(RawReentrant<Raw, TestThreadId<SendNotSync>>: Sync);
    assert_impl_all!(RawReentrant<Raw, TestThreadId<SyncNotSend>>: Sync);
    assert_not_impl_any!(RawReentrant<Raw, TestThreadId<SyncNotSend>>: Send);

    assert_impl_all!(LockReentrant<Raw, TestThreadId<SendSync>, SendSync>: Send, Sync);
    assert_impl_all!(LockReentrant<RawSendOnly, TestThreadId<SendSync>, SendSync>: Send);
    assert_not_impl_any!(LockReentrant<RawSendOnly, TestThreadId<SendSync>, SendSync>: Sync);
    assert_impl_all!(LockReentrant<RawSyncOnly, TestThreadId<SendSync>, SendSync>: Sync);
    assert_not_impl_any!(LockReentrant<RawSyncOnly, TestThreadId<SendSync>, SendSync>: Send);
    assert_not_impl_any!(LockReentrant<RawNeither, TestThreadId<SendSync>, SendSync>: Send, Sync);
    assert_impl_all!(LockReentrant<Raw, TestThreadId<SendNotSync>, SendSync>: Send);
    assert_not_impl_any!(LockReentrant<Raw, TestThreadId<SendNotSync>, SendSync>: Sync);
    assert_impl_all!(LockReentrant<Raw, TestThreadId<SyncNotSend>, SendSync>: Sync);
    assert_not_impl_any!(LockReentrant<Raw, TestThreadId<SyncNotSend>, SendSync>: Send);
    assert_impl_all!(LockReentrant<Raw, TestThreadId<SendSync>, SendNotSync>: Send, Sync);
    assert_not_impl_any!(LockReentrant<Raw, TestThreadId<SendSync>, SyncNotSend>: Send, Sync);
}

type Mutex<'a, R, T> = MutexGuard<'a, R, T>;
type MappedMutex<'a, R, T> = MappedMutexGuard<'a, R, T>;
type Read<'a, R, T> = RwLockReadGuard<'a, R, T>;
type Write<'a, R, T> = RwLockWriteGuard<'a, R, T>;
type Upgradable<'a, R, T> = RwLockUpgradableReadGuard<'a, R, T>;
type MappedRead<'a, R, T> = MappedRwLockReadGuard<'a, R, T>;
type MappedWrite<'a, R, T> = MappedRwLockWriteGuard<'a, R, T>;

macro_rules! assert_mapped_exclusive {
    ($guard:ident) => {
        assert_impl_all!($guard<'static, Raw, SendSync>: Send, Sync);

        assert_not_impl_any!($guard<'static, RawSendOnly, SendSync>: Send, Sync);
        assert_impl_all!($guard<'static, RawSyncOnly, SendSync>: Send, Sync);
        assert_not_impl_any!($guard<'static, RawNeither, SendSync>: Send, Sync);

        assert_impl_all!($guard<'static, Raw, SendNotSync>: Send);
        assert_not_impl_any!($guard<'static, Raw, SendNotSync>: Sync);
        assert_impl_all!($guard<'static, Raw, SyncNotSend>: Sync);
        assert_not_impl_any!($guard<'static, Raw, SyncNotSend>: Send);

        assert_impl_all!($guard<'static, Raw<MarkerSendOnly>, SendSync>: Send);
        assert_not_impl_any!($guard<'static, Raw<MarkerSendOnly>, SendSync>: Sync);
        assert_impl_all!($guard<'static, Raw<GuardNoSend>, SendSync>: Sync);
        assert_not_impl_any!($guard<'static, Raw<GuardNoSend>, SendSync>: Send);
    };
}

assert_mapped_exclusive!(MappedMutex);
assert_mapped_exclusive!(MappedWrite);

assert_impl_all!(Mutex<'static, Raw, SendSync>: Send, Sync);
assert_not_impl_any!(Mutex<'static, RawSendOnly, SendSync>: Send, Sync);
assert_impl_all!(Mutex<'static, RawSyncOnly, SendSync>: Send, Sync);
assert_not_impl_any!(Mutex<'static, RawNeither, SendSync>: Send, Sync);
assert_impl_all!(Mutex<'static, Raw, SendNotSync>: Send);
assert_not_impl_any!(Mutex<'static, Raw, SendNotSync>: Sync);
assert_not_impl_any!(Mutex<'static, Raw, SyncNotSend>: Send, Sync);
assert_impl_all!(Mutex<'static, Raw<MarkerSendOnly>, SendSync>: Send);
assert_not_impl_any!(Mutex<'static, Raw<MarkerSendOnly>, SendSync>: Sync);
assert_impl_all!(Mutex<'static, Raw<GuardNoSend>, SendSync>: Sync);
assert_not_impl_any!(Mutex<'static, Raw<GuardNoSend>, SendSync>: Send);

macro_rules! assert_borrowed_rwlock {
    ($guard:ident) => {
        assert_impl_all!($guard<'static, Raw, SendSync>: Send, Sync);

        assert_not_impl_any!($guard<'static, RawSendOnly, SendSync>: Send, Sync);
        assert_impl_all!($guard<'static, RawSyncOnly, SendSync>: Send, Sync);
        assert_not_impl_any!($guard<'static, RawNeither, SendSync>: Send, Sync);

        assert_not_impl_any!($guard<'static, Raw, SendNotSync>: Send, Sync);
        assert_not_impl_any!($guard<'static, Raw, SyncNotSend>: Send, Sync);

        assert_impl_all!($guard<'static, Raw<MarkerSendOnly>, SendSync>: Send);
        assert_not_impl_any!($guard<'static, Raw<MarkerSendOnly>, SendSync>: Sync);
        assert_impl_all!($guard<'static, Raw<GuardNoSend>, SendSync>: Sync);
        assert_not_impl_any!($guard<'static, Raw<GuardNoSend>, SendSync>: Send);
    };
}

assert_borrowed_rwlock!(Read);
assert_borrowed_rwlock!(Write);
assert_borrowed_rwlock!(Upgradable);

assert_impl_all!(MappedRead<'static, Raw, SendSync>: Send, Sync);
assert_impl_all!(MappedRead<'static, RawSyncOnly, SendSync>: Send, Sync);
assert_not_impl_any!(MappedRead<'static, RawSendOnly, SendSync>: Send, Sync);
assert_not_impl_any!(MappedRead<'static, RawNeither, SendSync>: Send, Sync);
assert_impl_all!(MappedRead<'static, Raw, SyncNotSend>: Send, Sync);
assert_not_impl_any!(MappedRead<'static, Raw, SendNotSync>: Send, Sync);
assert_impl_all!(MappedRead<'static, Raw<MarkerSendOnly>, SendSync>: Send);
assert_not_impl_any!(MappedRead<'static, Raw<MarkerSendOnly>, SendSync>: Sync);
assert_impl_all!(MappedRead<'static, Raw<GuardNoSend>, SendSync>: Sync);
assert_not_impl_any!(MappedRead<'static, Raw<GuardNoSend>, SendSync>: Send);

#[cfg(feature = "atomic_usize")]
mod reentrant_guard_traits {
    use super::*;

    type Reentrant<'a, R, G, T> = ReentrantMutexGuard<'a, R, G, T>;
    type MappedReentrant<'a, R, G, T> = MappedReentrantMutexGuard<'a, R, G, T>;

    assert_impl_all!(MappedReentrant<'static, Raw, TestThreadId<SendSync>, SendSync>: Sync);
    assert_not_impl_any!(MappedReentrant<'static, Raw, TestThreadId<SendSync>, SendSync>: Send);
    assert_impl_all!(MappedReentrant<'static, RawSyncOnly, TestThreadId<SyncNotSend>, SyncNotSend>: Sync);
    assert_not_impl_any!(MappedReentrant<'static, RawSendOnly, TestThreadId<SendSync>, SendSync>: Sync);
    assert_not_impl_any!(MappedReentrant<'static, RawNeither, TestThreadId<SendSync>, SendSync>: Send, Sync);
    assert_not_impl_any!(MappedReentrant<'static, Raw, TestThreadId<SendNotSync>, SendSync>: Sync);
    assert_not_impl_any!(MappedReentrant<'static, Raw, TestThreadId<SendSync>, SendNotSync>: Sync);

    assert_impl_all!(Reentrant<'static, Raw, TestThreadId<SendSync>, SendSync>: Sync);
    assert_not_impl_any!(Reentrant<'static, Raw, TestThreadId<SendSync>, SendSync>: Send);
    assert_impl_all!(Reentrant<'static, RawSyncOnly, TestThreadId<SyncNotSend>, SendSync>: Sync);
    assert_not_impl_any!(Reentrant<'static, RawSendOnly, TestThreadId<SendSync>, SendSync>: Sync);
    assert_not_impl_any!(Reentrant<'static, RawNeither, TestThreadId<SendSync>, SendSync>: Send, Sync);
    assert_not_impl_any!(Reentrant<'static, Raw, TestThreadId<SendNotSync>, SendSync>: Sync);
    assert_not_impl_any!(Reentrant<'static, Raw, TestThreadId<SendSync>, SendNotSync>: Sync);
    assert_not_impl_any!(Reentrant<'static, Raw, TestThreadId<SendSync>, SyncNotSend>: Sync);
}

#[cfg(feature = "arc_lock")]
mod arc {
    use super::*;

    type ArcMutex<R, T> = ArcMutexGuard<R, T>;
    type ArcRead<R, T> = ArcRwLockReadGuard<R, T>;
    type ArcWrite<R, T> = ArcRwLockWriteGuard<R, T>;
    type ArcUpgradable<R, T> = ArcRwLockUpgradableReadGuard<R, T>;

    assert_impl_all!(ArcMutex<Raw, SendSync>: Send, Sync);
    assert_not_impl_any!(ArcMutex<RawSendOnly, SendSync>: Send, Sync);
    assert_not_impl_any!(ArcMutex<RawSyncOnly, SendSync>: Send, Sync);
    assert_not_impl_any!(ArcMutex<RawNeither, SendSync>: Send, Sync);
    assert_impl_all!(ArcMutex<Raw, SendNotSync>: Send);
    assert_not_impl_any!(ArcMutex<Raw, SendNotSync>: Sync);
    assert_not_impl_any!(ArcMutex<Raw, SyncNotSend>: Send, Sync);
    assert_impl_all!(ArcMutex<Raw<MarkerSendOnly>, SendSync>: Send);
    assert_not_impl_any!(ArcMutex<Raw<MarkerSendOnly>, SendSync>: Sync);
    assert_impl_all!(ArcMutex<Raw<GuardNoSend>, SendSync>: Sync);
    assert_not_impl_any!(ArcMutex<Raw<GuardNoSend>, SendSync>: Send);

    macro_rules! assert_arc_rwlock {
        ($guard:ident) => {
            assert_impl_all!($guard<Raw, SendSync>: Send, Sync);

            assert_not_impl_any!($guard<RawSendOnly, SendSync>: Send, Sync);
            assert_not_impl_any!($guard<RawSyncOnly, SendSync>: Send, Sync);
            assert_not_impl_any!($guard<RawNeither, SendSync>: Send, Sync);

            assert_not_impl_any!($guard<Raw, SendNotSync>: Send, Sync);
            assert_not_impl_any!($guard<Raw, SyncNotSend>: Send, Sync);

            assert_impl_all!($guard<Raw<MarkerSendOnly>, SendSync>: Send);
            assert_not_impl_any!($guard<Raw<MarkerSendOnly>, SendSync>: Sync);
            assert_impl_all!($guard<Raw<GuardNoSend>, SendSync>: Sync);
            assert_not_impl_any!($guard<Raw<GuardNoSend>, SendSync>: Send);
        };
    }

    assert_arc_rwlock!(ArcRead);
    assert_arc_rwlock!(ArcWrite);
    assert_arc_rwlock!(ArcUpgradable);

    #[cfg(feature = "atomic_usize")]
    mod reentrant {
        use super::*;

        type ArcReentrant<R, G, T> = ArcReentrantMutexGuard<R, G, T>;

        assert_impl_all!(ArcReentrant<Raw, TestThreadId<SendSync>, SendSync>: Sync);
        assert_not_impl_any!(ArcReentrant<Raw, TestThreadId<SendSync>, SendSync>: Send);
        assert_not_impl_any!(ArcReentrant<RawSyncOnly, TestThreadId<SendSync>, SendSync>: Sync);
        assert_not_impl_any!(ArcReentrant<RawSendOnly, TestThreadId<SendSync>, SendSync>: Sync);
        assert_not_impl_any!(ArcReentrant<RawNeither, TestThreadId<SendSync>, SendSync>: Send, Sync);
        assert_not_impl_any!(ArcReentrant<Raw, TestThreadId<SyncNotSend>, SendSync>: Sync);
        assert_not_impl_any!(ArcReentrant<Raw, TestThreadId<SendNotSync>, SendSync>: Sync);
        assert_not_impl_any!(ArcReentrant<Raw, TestThreadId<SendSync>, SyncNotSend>: Sync);
        assert_not_impl_any!(ArcReentrant<Raw, TestThreadId<SendSync>, SendNotSync>: Sync);
    }
}

#[test]
fn trait_matrix_compiles() {}
