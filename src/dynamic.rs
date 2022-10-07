use std::collections::HashMap;
use std::any::TypeId;
use std::sync::{Arc, RwLock};
use std::sync::atomic::{AtomicUsize, Ordering, ATOMIC_USIZE_INIT};
use std::cell::RefCell;

use crate::VTable;

type RegistryKey = (TypeId, TypeId);

#[doc(hidden)]
#[derive(Default, Clone)]
pub struct Registry {
    entries: HashMap<RegistryKey, VTable>
}

impl Registry {
    #[doc(hidden)]
    pub unsafe fn register<Type: 'static + ?Sized, Trait: 'static + ?Sized>(&mut self, vtable: VTable) {
        self.entries.insert((TypeId::of::<Type>(), TypeId::of::<Trait>()), vtable);
    }
    fn find<Type: 'static + ?Sized>(&self, trait_id: TypeId) -> Option<VTable> {
        self.entries.get(&(TypeId::of::<Type>(), trait_id)).cloned()
    }
}

// The global registry can be dynamically updated, so must be protected
// by an RwLock.
#[derive(Default)]
struct GlobalRegistry {
    registry: Arc<Registry>
}

// But we need read access to be *super* fast, since it's accessed
// on every query, so we store a local reference that doesn't require
// any synchronisation to access.
struct LocalRegistry {
    registry: Arc<Registry>,
    version: usize
}

lazy_static! {
    static ref GLOBAL_REGISTRY: RwLock<GlobalRegistry> = RwLock::default();
}
static GLOBAL_REGISTRY_VERSION: AtomicUsize = ATOMIC_USIZE_INIT;

impl LocalRegistry {
    fn obtain() -> Self {
        // Obtain read access to global registry
        let lock_guard = GLOBAL_REGISTRY.read().unwrap();

        // Keep a local reference to the registry
        LocalRegistry {
            registry: lock_guard.registry.clone(),
            version: GLOBAL_REGISTRY_VERSION.load(Ordering::Acquire),
        }
    }
}

thread_local! {
    static LOCAL_REGISTRY: RefCell<LocalRegistry> = RefCell::new(LocalRegistry::obtain());
}

// *Fast* read-only access to the registry
fn with_registry<R, F: FnOnce(&Registry) -> R>(f: F) -> R {
    LOCAL_REGISTRY.with(|registry| {
        let mut registry = registry.borrow_mut();
        
        // Check for updates
        if GLOBAL_REGISTRY_VERSION.load(Ordering::Acquire) != registry.version {
            *registry = LocalRegistry::obtain();
        }

        // Access to registry
        f(&registry.registry)
    })
}

// Slower write access to the registry
#[doc(hidden)]
pub fn with_registry_mut<R, F: FnOnce(&mut Registry) -> R>(f: F) -> R {
    // Obtain write access to global registry
    let mut lock_guard = GLOBAL_REGISTRY.write().unwrap();

    // Allow caller to mutate registry
    let result = f(Arc::make_mut(&mut lock_guard.registry));

    // Notify readers that the registry has changed
    GLOBAL_REGISTRY_VERSION.fetch_add(1, Ordering::AcqRel);

    result
}

#[doc(hidden)]
pub fn find_in_registry<Type: 'static + ?Sized>(trait_id: TypeId) -> Option<VTable> {
    with_registry(|registry| registry.find::<Type>(trait_id))
}

#[macro_export]
macro_rules! dynamic_interfaces {
    ($($name:ty: $($iface:ty),+;)*) => (
        $crate::dynamic::with_registry_mut(|registry| { unsafe { $(
            registry.register::<$name, $name>($crate::VTable::none());
            registry.register::<$name, dyn $crate::Object>(vtable_for!($name as dyn $crate::Object));
            $(
            registry.register::<$name, $iface>(vtable_for!($name as $iface));
            )+
        )* } });
    )
}
