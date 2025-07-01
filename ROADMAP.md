### Roadmap (abandoned)

#### MVP
- [x] Immutable/Mutable References `&x`/`!x`
- [x] Auto (de)referencing
- [x] Struct methods
- [ ] Generics
- [ ] Enums
- [ ] Nullable Pointers as `Option<!T>` (similar to Rust's null pointer optimization but with C compatibility)
- [ ] Array support (temporary C semantics)

#### Easy nice-to-haves
- [x] Absolute paths
- [ ] Syntactic sugar: `if *** do stmt`
- [ ] Operator overloading
- [ ] Lazily `#include`s (e.g. import `stdbool.h` iff `bool` is used in the file)
- [ ] Basic ownership


#### Hard nice-to-haves
- [ ] Expression decomposition
    - [ ] Expression-scope blocks
    - [ ] `unsafe` block that does nothing but make Rust programmers confortable
    - [ ] Guaranteed function argument evaluation order
    - [ ] Do not rely on C's operator precedence
    - [ ] Array as values
    - [ ] Referencing of rvalue expressions
- [ ] Traits
- [ ] Resource visibility
- [ ] A standard library
- [ ] Better error messages
- [ ] `extern` struct declarations
- [ ] Basic, non-intrusive reference lifetime checking
- [ ] Macros as functions
    - [ ] Compile-time code execution

