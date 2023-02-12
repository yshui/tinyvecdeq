#![forbid(unsafe_code)]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod arrayvecdeq;
pub mod array;

#[cfg(feature = "alloc")]
pub mod tinyvecdeq;
