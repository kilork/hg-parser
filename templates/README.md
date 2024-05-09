# hg-parser

Mercurial repository parser written in the [Rust programming language](https://www.rust-lang.org/en-US/).

## Basic usage

### Add dependency to Cargo.toml

```toml
[dependencies]
hg-parser = "0.8"
```

### Use case - Analyse revision log and export to ```git fast-import``` format

{{ codeblock "rust#ignore" ( read_to_str "examples/git-fast-import.rs" ) }}

## Implementation details

**hg-parser** is based on repository parse code from [mononoke](https://github.com/facebookexperimental/mononoke) project. Which basically based on original Mercurial source code. Version has some simplifications which may not work for you.