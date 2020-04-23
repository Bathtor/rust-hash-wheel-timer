# Hash Wheel Timer

A low-level timer implementation using a hierarchical four-level hash wheel together with an overflow vector.

[![License](https://img.shields.io/badge/license-MIT-blue.svg)](https://github.com/Bathtor/rust-hash-wheel-timer)
<!-- [![Cargo](https://img.shields.io/crates/v/executors.svg)](https://crates.io/crates/executors) 
[![Documentation](https://docs.rs/executors/badge.svg)](https://docs.rs/executors) //-->
[![Build Status](https://travis-ci.org/Bathtor/rust-hash-wheel-timer.svg?branch=master)](https://travis-ci.org/Bathtor/rust-hash-wheel-timer)

## Provided APIs

This crate provides a low-level event timer implementation based on hierarchical hash wheels.

The APIs in the crate are offered at three different levels of abstraction, listed below from lowest to highest.

### 1 – Single Wheel
The fundamental abstraction of this crate a single hash wheel with 256 slots addressed with a single byte. Each slot stores a list of a generic event type.
The whole wheel can be "ticked" causing entries in the slots that are being moved over to expire. With every tick, all expired event entries are returned for handling.

### 2 – Hierachical Wheel
Combining four byte wheels we get a hierachical timer that can represent timeouts up to `std::u32::MAX` time units into the future.
In order to support timeouts of up to `std::u64::MAX` time units, our implementations also come with an overflow list, which stores all timers that didn't fit into any slot in the four wheels.

This crate provides two variant implementations of this four level wheel structure:

- The `wheels::quad_wheel::QuadWheelWithOverflow` corresponds directly to the implementation described above.
- The `wheels::cancellable::QuadWheelWithOverflow` additionally supports the cancellation of outstanding timers before they expire. In order to do so, however, it requires the generic timer entry type to provide a unique identifier field. It also uses `std::rc::Rc` internally to avoid double storing the actual entry, which makes it (potentialy) unsuitable for situations where the timer must be able to move between threads.

### 3 – High Level APIs
This crate also provides two high levels APIs that can either be used directly or can be seen as examples of how to use the lower level APIs in an application.

Bother higher level APIs also offer built-in support for periodically repeating timers, in addition to the normal timers which are schedulled once and discarded once expired.

#### Simulation Timer
The `simulation` module provides an implementation for an event timer used to drive a discrete event simulation.
Its particular feature is that it can skip quickly through periods where no events are schedulled as it doesn't track real time, but rather provides the rate at which the simulation proceeds.

#### Thread Timer
The `thread_timer` module provides a timer for real-time event schedulling with millisecond accuracy.
It runs on its own dedicated thread and uses a shareable handle called a `TimerRef` for communication with other threads.

## Documentation

For reference and examples check the [API Docs](https://docs.rs/hierarchical_hash_wheel_timer).

## Performance

On my 2019 16" MacBook Pro (2,3 GHz 8-Core Intel Core i9) the level 2 APIs provide between 8 and 11 million writes per second (depending on the distribution of timer delays) and can read (or expire) timer entries at a rate of 2.7 million entries per second (if they are distributed over multiple slots) or around 11 million entries per second (if they are clustered into single slot).

You can repeat these experiments on your own hardware by checking out the sources and calling `cargo bench`.

## License

Licensed under the terms of MIT license.

See [LICENSE](LICENSE) for details.
