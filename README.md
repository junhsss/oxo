# oxo

A from-scratch toolchain for software that comes with a proof.

1. A human writes what a program should do.
2. An untrusted generator writes the program and a proof.
3. A small, deterministic kernel checks the proof.
4. The checked program is compiled to native code.
5. Anyone can re-check the proof without trusting the author, generator, or compiler run.

If the proof is wrong, the kernel rejects it. If the generator is wrong, it does not matter.
The shipped binary contains only the checked program.

As code generation gets cheaper, trust moves from "who wrote this?" to "what
checked this?". The trusted part should be as small and auditable
as possible, and everything else should be replaceable.

## How It Works

```
spec ──①──► proof obligations ──②──► impl + proof ──③──► checked ──④──► binary + proof
            (deterministic)        (untrusted)         (KERNEL)      (verified compiler)
```

The kernel is the judge. Compiler passes, generators, and helper tools are
allowed to be wrong because their output must still pass the kernel.
