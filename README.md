# Roboto: Parse and use robots.txt files

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
