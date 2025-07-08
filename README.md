# Prefix Parser

A parser for numbers with a binary/SI prefix on the end.

# Usage:

call `prefix_parser::parse_prefixes` with the prefixed number to parse.

```rust
let parsed = prefix_parser::parse_prefixes("216MiB")?;

// 226492416 == 1024^2 * 216, so 226492416 is 216MiB
assert_eq!(parsed, 226492416);
```

## Things to note:

 - If no prefix is specified, the value is just converted to a number and returned.
 - Capitalization is ignored. To differentiate between SI and binary, use `MB` vs `MiB`, `KB` vs `KiB`, etc...
 - If just the first letter is specified, it is assumed to be in binary format (`1k` is 1024, not 1000).
 - All of `b`, `bb`, and `bib` are allowed and valid, although they just keep the number as is.
