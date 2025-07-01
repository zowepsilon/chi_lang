# The χ (chi) Programming Language

An imperative programming language that transpiles to C. It features overloadable functions, structs, methods, a module system, extern functions, basic type inference, immutable/mutable references, auto referencing and dereferencing.

### Getting Started

The `examples/` folder shows the basic syntax and semantics of the language.

Example program (from `examples/recursion.chi`): 
```groovy
extern "<stdio.h>" {
    def printf(fmt_str: !char, ...)
}

def fib(n: int) -> int {
    if n < 2 {
        return 1
    }
    return fib(n-1) + fib(n-2)
}

def main() {
    printf("fib(9) = %i\n", fib(9))
}
```

Try running it:
```console
cargo run -- examples/recursion.chi
```


To compile and run a program, simply pass it as the first argument to the compiler :
```console
cargo run -- <program.chi>
```
The generated C code and the compiled executable should be located in the `generated/` folder in the current directory.
Executable generation is only supported on Linux (and perhaps MacOS, untested), though Chi generates a single C file, so manual compilation shouldn't be an issue.

### Tests
`cargo test` compiles and runs every examples in the `examples/` folder and check if any of them failed to compile or run.
> All examples should compile and return `0`.

### Architecture

- `src/main.rs`: entry point
- `src/lib.rs`: library root, backbone of the compiler pipeline

- `src/lexer.rs`: lexer
- `src/parser.rs`: recursive descent parser
- `src/ast.rs`: untyped AST types

- `src/analysis/mod.rs`: multi-pass module declaration analysis, function/statement/expression typing, method resolution
- `src/analysis/resources.rs`: resource types, resource resolution routines, overload resolution
- `src/analysis/expression.rs`: typed AST types, lvalue checking, type coercion of arguments
- `src/analysis/builtins.rs`: builtin types and operator definitions

- `src/transpiler.rs`: transpiles a typed module into a C source file.
- `src/compilation.rs`: (Linux only) calls `clang` to compile the generated the generated C file.

### References

- https://craftinginterpreters.com/parsing-expressions.html
- https://github.com/gchatelet/gcc_cpp_mangling_documentation
