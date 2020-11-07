# readmem

A rust library to read data of the format required by the Verilog system
tasks `$readmemb` and `$readmemh`.

Example:

```rust
let file_content = r#"
    @0 0
    @1 1 // one!
    2
"#;
use readmem::{readmem, ContentType};
assert_eq!(vec![0, 1, 2], readmem::<u8>(file_content, ContentType::Hex).unwrap());
```