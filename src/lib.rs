//! query-interface - dynamically query a type-erased object for any trait implementation
//!
//! ```rust
//! #[macro_use]
//! extern crate query_interface;
//! use query_interface::{Object, ObjectClone};
//! use std::fmt::Debug;
//!
//! #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
//! struct Foo;
//!
//! interfaces!(Foo: ObjectClone, Debug, Bar);
//!
//! trait Bar {
//!     fn do_something(&self);
//! }
//! impl Bar for Foo {
//!     fn do_something(&self) {
//!         println!("I'm a Foo!");
//!     }
//! }
//!
//! fn main() {
//!     let obj = Box::new(Foo) as Box<Object>;
//!     let obj2 = obj.clone();
//!     println!("{:?}", obj2);
//!
//!     obj2.query_ref::<Bar>().unwrap().do_something();  // Prints: "I'm a Foo!"
//! }
//! ```

use std::any::{TypeId, Any};
use std::ptr;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher, SipHasher};

/// Represents a trait object's vtable pointer. You shouldn't need to use this as a
/// consumer of the crate but it is required for macro expansion.
#[doc(hidden)]
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct VTable(*const ());

impl VTable {
    pub fn none() -> VTable {
        VTable(ptr::null())
    }
}

/// Represents a trait object's layout. You shouldn't need to use this as a
/// consumer of the crate but it is required for macro expansion.
#[doc(hidden)]
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct TraitObject {
    pub data: *const (),
    pub vtable: VTable
}

/// Obtain the vtable for a type/trait pair. You shouldn't need to use this as a
/// consumer of the crate but it is required for macro expansion.
#[doc(hidden)]
#[macro_export]
macro_rules! vtable_for {
    ($x:ty as $y:ty) => ({
        let x = ::std::ptr::null::<$x>() as *const $y;
        unsafe { ::std::mem::transmute::<_, $crate::TraitObject>(x).vtable }
    })
}

/// Define a custom Object-like trait. The `query`, `query_ref` an `query_mut`
/// methods will be automatically implemented on this trait object.
/// 
/// You may add additional static bounds to your custom trait via the
/// `HasInterface<I>` trait. This example will statically ensure that all
/// types convertible to `MyObject` can be cloned. Your trait must extend
/// `Object`.
/// 
/// ```rust
/// # #[macro_use]
/// # extern crate query_interface;
/// # use query_interface::*;
/// trait MyObject: Object + ObjectClone + HasInterface<ObjectClone> { }
/// mopo!(MyObject);
/// # fn main() {}
/// ```
#[macro_export]
macro_rules! mopo {
    ($name:ty) => (
        impl $name {
            pub fn query_ref<U: ::std::any::Any + ?Sized>(&self) -> Option<&U> {
                if let Some(vtable) = self.query_vtable(::std::any::TypeId::of::<U>()) {
                    unsafe {
                        let data = self as *const Self;
                        let u = $crate::TraitObject { data: data as *const (), vtable: vtable };
                        Some(*::std::mem::transmute::<_, &&U>(&u))
                    }
                } else {
                    None
                }
            }
            pub fn query_mut<U: ::std::any::Any + ?Sized>(&mut self) -> Option<&mut U> {
                if let Some(vtable) = self.query_vtable(::std::any::TypeId::of::<U>()) {
                    unsafe {
                        let data = self as *mut Self;
                        let mut u = $crate::TraitObject { data: data as *const (), vtable: vtable };
                        Some(*::std::mem::transmute::<_, &mut &mut U>(&mut u))
                    }
                } else {
                    None
                }
            }
            pub fn query<U: ::std::any::Any + ?Sized>(self: Box<Self>) -> ::std::result::Result<Box<U>, Box<Self>> {
                if let Some(vtable) = self.query_vtable(::std::any::TypeId::of::<U>()) {
                    unsafe {
                        let data = Box::into_raw(self);
                        let mut u = $crate::TraitObject { data: data as *const (), vtable: vtable };
                        Ok(Box::from_raw(*::std::mem::transmute::<_, &mut *mut U>(&mut u)))
                    }
                } else {
                    Err(self)
                }
            }
            pub fn obj_partial_eq(&self, other: &Self) -> bool {
                if let Some(x) = self.query_ref::<$crate::ObjectPartialEq>() {
                    x.obj_eq(other.query_ref().unwrap())
                } else {
                    (self as *const Self) == (other as *const Self)
                }
            }
            pub fn obj_partial_cmp(&self, other: &Self) -> Option<::std::cmp::Ordering> {
                if let Some(x) = self.query_ref::<$crate::ObjectPartialOrd>() {
                    x.obj_partial_cmp(other.query_ref().unwrap())
                } else {
                    None
                }
            }
        }
        impl ::std::clone::Clone for Box<$name> {
            fn clone(&self) -> Self {
                (**self).to_owned()
            }
        }
        impl ::std::borrow::ToOwned for $name {
            type Owned = Box<$name>;
            fn to_owned(&self) -> Box<$name> {
                self.query_ref::<$crate::ObjectClone>().expect("Object not clonable!").obj_clone().query::<$name>().unwrap()
            }
        }
        impl ::std::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                if let Some(o) = self.query_ref::<::std::fmt::Debug>() {
                    o.fmt(f)
                } else {
                    writeln!(f, "Object {{ <no `Debug` implementation> }}")
                }
            }
        }
        impl ::std::cmp::PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                // Require `Eq` rather than `PartialEq` as this allows `Object`s to be used as
                // key in hash maps
                if let Some(x) = self.query_ref::<$crate::ObjectEq>() {
                    x.obj_eq(other.query_ref().unwrap())
                } else {
                    // This trivially meets the requirements of `Eq`
                    (self as *const Self) == (other as *const Self)
                }
            }
        }
        impl ::std::cmp::Eq for $name {}
        impl ::std::cmp::PartialOrd for $name {
            fn partial_cmp(&self, other: &Self) -> Option<::std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }
        impl ::std::cmp::Ord for $name {
            fn cmp(&self, other: &Self) -> ::std::cmp::Ordering {
                if let Some(x) = self.query_ref::<$crate::ObjectOrd>() {
                    if let Some(o) = x.obj_cmp(other.query_ref().unwrap()) {
                        return o
                    }
                }
                Ord::cmp(&(self as *const Self), &(other as *const Self))
            }
        }
        impl ::std::hash::Hash for $name {
            fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
                if let Some(x) = self.query_ref::<$crate::ObjectHash>() {
                    x.obj_hash(state)
                } else {
                    state.write_usize(self as *const Self as *const () as usize)
                }
            }
        }
    )
}

/// This trait is the primary function of the library. `Object` trait objects
/// can be freely queried for any other trait, allowing conversion between
/// trait objects.
pub unsafe trait Object: Any {
    /// This is implemented by the `interfaces!` macro, and should never be
    /// manually implemented.
    #[doc(hidden)]
    fn query_vtable(&self, id: TypeId) -> Option<VTable>;
}

/// You can use this trait to ensure that a type implements a trait as an
/// interface. This means the type declared the trait in its `interfaces!(...)`
/// list, and guarantees that querying an `Object` of that type for the trait
/// will always succeed.
/// 
/// When using `HasInterface<SomeTrait>` in a generic bound, you should also
/// specify `SomeTrait` as a bound. While `HasInterface<SomeTrait>` is a more
/// stringent requirement than, and in practice implies `SomeTrait`, the
/// compiler cannot deduce that because it is enforced through macros rather
/// than the type system.
pub unsafe trait HasInterface<I: ?Sized> {}

mopo!(Object);


/// This is an object-safe version of `Clone`, which is automatically
/// implemented for all `Clone + Object` types. This is a support trait used to
/// allow `Object` trait objects to be clonable.
pub trait ObjectClone {
    fn obj_clone(&self) -> Box<Object>;
}
impl<T: Clone + Object> ObjectClone for T {
    fn obj_clone(&self) -> Box<Object> {
        Box::new(self.clone())
    }
}

/// This is an object-safe version of `PartialEq`, which is automatically
/// implemented for all `PartialEq + Object` types. This is a support trait used to
/// allow `Object` trait objects to be comparable in this way.
pub trait ObjectPartialEq {
    fn obj_eq(&self, other: &Object) -> bool;
}
impl<T: PartialEq + Object> ObjectPartialEq for T {
    fn obj_eq(&self, other: &Object) -> bool {
        if let Some(o) = other.query_ref::<Self>() {
            self == o
        } else {
            false
        }
    }
}

/// This is an object-safe version of `Eq`, which is automatically
/// implemented for all `Eq + Object` types. This is a support trait used to
/// allow `Object` trait objects to be comparable in this way.
pub trait ObjectEq: ObjectPartialEq {}
impl<T: Eq + Object> ObjectEq for T {}

/// This is an object-safe version of `PartialOrd`, which is automatically
/// implemented for all `PartialOrd + Object` types. This is a support trait used to
/// allow `Object` trait objects to be comparable in this way.
pub trait ObjectPartialOrd {
    fn obj_partial_cmp(&self, other: &Object) -> Option<Ordering>;
}
impl<T: PartialOrd + Object> ObjectPartialOrd for T {
    fn obj_partial_cmp(&self, other: &Object) -> Option<Ordering> {
        if let Some(o) = other.query_ref::<Self>() {
            self.partial_cmp(o)
        } else {
            None
        }
    }
}

/// This is an object-safe version of `Ord`, which is automatically
/// implemented for all `Ord + Object` types. This is a support trait used to
/// allow `Object` trait objects to be comparable in this way.
pub trait ObjectOrd {
    fn obj_cmp(&self, other: &Object) -> Option<Ordering>;
}
impl<T: Ord + Object> ObjectOrd for T {
    fn obj_cmp(&self, other: &Object) -> Option<Ordering> {
        if let Some(o) = other.query_ref::<Self>() {
            Some(self.cmp(o))
        } else {
            None
        }
    }
}

/// This is an object-safe version of `Hash`, which is automatically
/// implemented for all `Hash + Object` types. This is a support trait used to
/// allow `Object` trait objects to be comparable in this way.
///
/// Note: `Object`s are not guaranteed to hash to the same value as their
/// underlying type.
pub trait ObjectHash {
    fn obj_hash(&self, state: &mut Hasher);
}
impl<T: Hash + Object> ObjectHash for T {
    fn obj_hash(&self, state: &mut Hasher) {
        let mut h = SipHasher::new();
        self.hash(&mut h);
        state.write_u64(h.finish());
    }
}

/// Allow a set of traits to be dynamically queried from a type when it is
/// stored as an `Object` trait object.
/// 
/// Example use:
/// 
/// ```rust
/// # #[macro_use]
/// # extern crate query_interface;
/// # use query_interface::*;
/// #[derive(Clone)]
/// struct Foo;
/// interfaces!(Foo: ObjectClone);
/// # fn main() {}
/// ```
#[macro_export]
macro_rules! interfaces {
    ($name:ty: $($iface:ty),+) => (
        unsafe impl $crate::HasInterface<$name> for $name {}
        unsafe impl $crate::HasInterface<$crate::Object> for $name {}
        $(unsafe impl $crate::HasInterface<$iface> for $name {})*
        unsafe impl $crate::Object for $name {
            fn query_vtable(&self, id: ::std::any::TypeId) -> Option<$crate::VTable> {
                if id == ::std::any::TypeId::of::<$name>() {
                    Some($crate::VTable::none())
                } else if id == ::std::any::TypeId::of::<$crate::Object>() {
                    Some(vtable_for!($name as $crate::Object))
                } else $(if id == ::std::any::TypeId::of::<$iface>() {
                    Some(vtable_for!($name as $iface))
                } else)* {
                    None
                }
            }
        }
    )
}

#[cfg(test)]
mod tests {
    use std::fmt::Debug;

    #[derive(Debug, Clone)]
    struct Bar;
    interfaces!(Bar: Foo, super::ObjectClone, Debug, Custom);

    trait Foo: Debug {
        fn test(&self) -> bool { false }
    }
    trait Foo2: Debug {}
    impl Foo for Bar {
        fn test(&self) -> bool { true }
    }
    impl Foo2 for Bar {}

    #[test]
    fn test_ref() {
        let x = Box::new(Bar) as Box<super::Object>;
        let foo: Option<&Foo> = x.query_ref();
        assert!(foo.is_some());
        assert!(foo.unwrap().test());
        let foo2: Option<&Foo2> = x.query_ref();
        assert!(foo2.is_none());
        let bar: Option<&Bar> = x.query_ref();
        assert!(bar.is_some());
    }

    #[test]
    fn test_mut() {
        let mut x = Box::new(Bar) as Box<super::Object>;
        {
            let foo = x.query_mut::<Foo>();
            assert!(foo.is_some());
            assert!(foo.unwrap().test());
        }
        {
            let foo2 = x.query_mut::<Foo2>();
            assert!(foo2.is_none());
        }
        {
            let bar = x.query_mut::<Bar>();
            assert!(bar.is_some());
        }
    }

    #[test]
    fn test_owned() {
        let x = Box::new(Bar) as Box<super::Object>;
        let foo: Result<Box<Foo>, _> = x.clone().query();
        assert!(foo.is_ok());
        assert!(foo.unwrap().test());
        let foo2: Result<Box<Foo2>, _> = x.clone().query();
        assert!(foo2.is_err());
        let bar: Result<Box<Bar>, _> = x.clone().query();
        assert!(bar.is_ok());
    }

    trait Custom : super::Object {}
    impl Custom for Bar {}
    mopo!(Custom);

    #[test]
    fn test_derived() {
        let x = Box::new(Bar) as Box<Custom>;
        let foo: Result<Box<Foo>, _> = x.clone().query();
        assert!(foo.is_ok());
        assert!(foo.unwrap().test());
        let foo2: Result<Box<Foo2>, _> = x.clone().query();
        assert!(foo2.is_err());
        let bar: Result<Box<Bar>, _> = x.clone().query();
        assert!(bar.is_ok());
    }
}
