# query_interface
Dynamically query a type-erased object for any trait implementation

Example:
```rust
#[macro_use]
extern crate query_interface;

use query_interface::{Object, ObjectExt, ObjectClone};
use std::fmt::Debug;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct Foo;

interfaces!(Foo: ObjectClone, Debug, Bar);

trait Bar {
    fn do_something(&self);
}
impl Bar for Foo {
    fn do_something(&self) {
        println!("I'm a Foo!");
    }
}

fn main() {
    let obj = Box::new(Foo) as Box<Object>;
    let obj2 = obj.clone();
    println!("{:?}", obj2);
   
    obj2.query_ref::<Bar>().unwrap().do_something();  // Prints: "I'm a Foo!"
}
```

In short, this allows you to pass around `Object`s and still have access to any of the (object-safe) traits
implemented for the underlying type. The library also provides some useful object-safe equivalents to standard
traits, including `ObjectClone`, `ObjectPartialEq`, `ObjectPartialOrd`, `ObjectHash`.

To improve usability, the non-object-safe versions of the traits are implemented directly on the `Object` trait
object, allowing you to easily clone `Object`s and store them in collections.
