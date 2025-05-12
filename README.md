# Roboto: Parse and use robots.txt files

[![crate][crate-image]][crate-link]
[![Docs][docs-image]][docs-link]
[![Build Status][build-image]][build-link]
![MIT licensed][license-image]

Roboto provides a type-safe way to parse and use robots.txt files. It is based on the [Robots Exclusion Protocol](https://en.wikipedia.org/wiki/Robots_exclusion_standard) and is used to approximately try control the behavior of web crawlers and other web robots.

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
roboto = "0.1"
```

## Usage

```rust
use roboto::Robots;

let robots = r#"
User-agent: *
Disallow: /private
Disallow: /tmp
"#.parse::<Robots>().unwrap();

let user_agent = "googlebot".parse().unwrap();

assert_eq!(robots.is_allowed(&user_agent, "/public"), true);
```

[crate-image]: https://img.shields.io/crates/v/roboto
[crate-link]: https://crates.io/crates/roboto
[docs-image]: https://docs.rs/roboto/badge.svg
[docs-link]: https://docs.rs/roboto/
[build-image]: https://github.com/alexrudy/roboto/actions/workflows/ci.yml/badge.svg
[build-link]: https://github.com/alexrudy/roboto/actions/workflows/ci.yml
[license-image]: https://img.shields.io/badge/license-MIT-blue.svg
