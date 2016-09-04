//! query-interface - dynamically query a type-erased object for any trait implementation
//!
//! ```rust
//! #[macro_use]
//! extern crate query_interface;
//! use query_interface::{Object, ObjectExt, ObjectClone};
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
use std::mem;
use std::ptr;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher, SipHasher};
use std::fmt;

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct VTable(*const ());

impl VTable {
    pub fn none() -> VTable {
        VTable(ptr::null())
    }
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct TraitObject {
    pub data: *const (),
    pub vtable: VTable
}

#[macro_export]
macro_rules! vtable_for {
    ($x:ty as $y:ty) => ({
        let x = ::std::ptr::null::<$x>() as *const $y;
        unsafe { ::std::mem::transmute::<_, $crate::TraitObject>(x).vtable }
    })
}

pub unsafe trait Object: Any {
    fn query_vtable(&self, id: TypeId) -> Option<VTable>;
}

pub trait ObjectExt {
    fn query_ref<U: Any + ?Sized>(&self) -> Option<&U>;
    fn query_mut<U: Any + ?Sized>(&mut self) -> Option<&mut U>;
    fn query<U: Any + ?Sized>(self: Box<Self>) -> Result<Box<U>, Box<Self>>;
}

impl<T: Object + ?Sized> ObjectExt for T {
    fn query_ref<U: Any + ?Sized>(&self) -> Option<&U> {
        if let Some(vtable) = self.query_vtable(TypeId::of::<U>()) {
            unsafe {
                let data = self as *const T;
                let u = TraitObject { data: data as *const (), vtable: vtable };
                Some(*mem::transmute::<_, &&U>(&u))
            }
        } else {
            None
        }
    }
    fn query_mut<U: Any + ?Sized>(&mut self) -> Option<&mut U> {
        if let Some(vtable) = self.query_vtable(TypeId::of::<U>()) {
            unsafe {
                let data = self as *mut T;
                let mut u = TraitObject { data: data as *const (), vtable: vtable };
                Some(*mem::transmute::<_, &mut &mut U>(&mut u))
            }
        } else {
            None
        }
    }
    fn query<U: Any + ?Sized>(self: Box<Self>) -> Result<Box<U>, Box<Self>> {
        if let Some(vtable) = self.query_vtable(TypeId::of::<U>()) {
            unsafe {
                let data = Box::into_raw(self);
                let mut u = TraitObject { data: data as *const (), vtable: vtable };
                Ok(Box::from_raw(*mem::transmute::<_, &mut *mut U>(&mut u)))
            }
        } else {
            Err(self)
        }
    }
}

impl fmt::Debug for Object {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(o) = self.query_ref::<fmt::Debug>() {
            o.fmt(f)
        } else {
            writeln!(f, "Object {{ <no `Debug` implementation> }}")
        }
    }
}

pub trait ObjectClone {
    fn obj_clone(&self) -> Box<Object>;
}
impl<T: Clone + Object> ObjectClone for T {
    fn obj_clone(&self) -> Box<Object> {
        Box::new(self.clone())
    }
}
impl Clone for Box<Object> {
    fn clone(&self) -> Self {
        (**self).to_owned()
    }
}
impl ToOwned for Object {
    type Owned = Box<Object>;
    fn to_owned(&self) -> Box<Object> {
        self.query_ref::<ObjectClone>().expect("Object not clonable!").obj_clone()
    }
}

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
impl PartialEq for Object {
    fn eq(&self, other: &Object) -> bool {
        if let Some(x) = self.query_ref::<ObjectPartialEq>() {
            x.obj_eq(other)
        } else {
            (self as *const Object) == (other as *const Object)
        }
    }
}

pub trait ObjectEq: ObjectPartialEq {}
impl<T: Eq + Object> ObjectEq for T {}

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
impl PartialOrd for Object {
    fn partial_cmp(&self, other: &Object) -> Option<Ordering> {
        if let Some(x) = self.query_ref::<ObjectPartialOrd>() {
            x.obj_partial_cmp(other)
        } else if (self as *const Object) == (other as *const Object) {
            Some(Ordering::Equal)
        } else {
            None
        }
    }
}

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
impl Hash for Object {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if let Some(x) = self.query_ref::<ObjectHash>() {
            x.obj_hash(state)
        } else {
            state.write_usize(self as *const Object as *const () as usize)
        }
    }
}

#[macro_export]
macro_rules! interfaces {
    ($name:ty: $($iface:ty),+) => (
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
    use super::ObjectExt;

    #[derive(Debug, Clone)]
    struct Bar;
    interfaces!(Bar: Foo, super::ObjectClone, Debug);

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

}
