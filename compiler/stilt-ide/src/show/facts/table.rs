//! The facts of facts.inferred-facts: each fact that a limit names or that a function's own code
//! has, in the order of its table, with what it says of the function and the paragraphs that give
//! its sites. Generated from reference/15-facts.md by `just grammar-generate`, and checked
//! current by `just grammar`.

/// Each fact's word, what a function that has it does, and the paragraphs of its sites.
pub(crate) const FACTS: [(&str, &str, &str); 16] = [
    (
        "panic",
        "can panic, with a kind that counts against `without panic`",
        "effects.panicking-operations and facts.map-element-places",
    ),
    (
        "overflow",
        "can overflow an integer",
        "effects.overflow-effect",
    ),
    (
        "alloc",
        "can allocate",
        "facts.allocation and facts.native-allocation",
    ),
    ("div", "may not end", "facts.div"),
    (
        "copy",
        "can copy data that another value shares",
        "facts.copy",
    ),
    ("locks", "holds shared values", "shared.locks"),
    (
        "fs",
        "reaches files, the network, the clock, the environment, the console or randomness, starts tasks, or runs other programs",
        "facts.capabilities",
    ),
    (
        "net",
        "reaches files, the network, the clock, the environment, the console or randomness, starts tasks, or runs other programs",
        "facts.capabilities",
    ),
    (
        "clock",
        "reaches files, the network, the clock, the environment, the console or randomness, starts tasks, or runs other programs",
        "facts.capabilities",
    ),
    (
        "env",
        "reaches files, the network, the clock, the environment, the console or randomness, starts tasks, or runs other programs",
        "facts.capabilities",
    ),
    (
        "console",
        "reaches files, the network, the clock, the environment, the console or randomness, starts tasks, or runs other programs",
        "facts.capabilities",
    ),
    (
        "rand",
        "reaches files, the network, the clock, the environment, the console or randomness, starts tasks, or runs other programs",
        "facts.capabilities",
    ),
    (
        "spawn",
        "reaches files, the network, the clock, the environment, the console or randomness, starts tasks, or runs other programs",
        "facts.capabilities",
    ),
    (
        "exec",
        "reaches files, the network, the clock, the environment, the console or randomness, starts tasks, or runs other programs",
        "facts.capabilities",
    ),
    (
        "unsafe",
        "holds an `unsafe` block in its own code",
        "c.unsafe-and-foreign",
    ),
    (
        "foreign",
        "names foreign functions in its own code",
        "c.unsafe-and-foreign",
    ),
];
