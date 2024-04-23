## Cutting Planes with Lean 4

[![](https://github.com/bernborgess/lean-cutting-planes/actions/workflows/mdbook.yml/badge.svg?branch=main)](https://github.com/bernborgess/lean-cutting-planes/actions/workflows/mdbook.yml)

This project follows the research in [Lean 4 Theorem Proving](https://lean-lang.org/) and Metaprogramming,
where we where we aim to develop a Lean 4 library for formalizing and manipulating cutting planes
in a verifiable manner, as they were described by [Jakob Nordström](https://jakobnordstrom.se/) in
[A Unified Proof System for Discrete Combinatorial Problems](https://jakobnordstrom.se/docs/presentations/TalkVeriPB_Dagstuhl23.pdf#page=45).

This work bridges the gap between the theoretical underpinnings of cutting planes—a mathematical optimization technique used in linear programming
to refine solution spaces—and the rigorous environment of theorem proving offered by Lean 4.
Our goal is to model the foundational concepts of cutting plane calculation, implement these calculations' rules,
and formally verify their correctness.

By [Bernardo Borges](https://github.com/bernborgess/) as a _capstone project_ for the
[Bachelor's degreen in Computer Science](https://dcc.ufmg.br/bacharelado-em-ciencia-da-computacao/)
at [Universidade Federal de Minas Gerais](https://ufmg.br/).

## Documentation

This manual is generated by _mdBook_.

You can read the [docs](https://bernborgess.github.io/lean-cutting-planes/) here.

Run `mdbook test` to test all `lean` code blocks.

## Example

We want to represent Pseudo-Boolean formulas to decide whether they are _satisfiable_. For instance,
$$-x_1 + 2x_2 - 3x_3 + 4x_4 - 5x_5 \ge 1 $$
will be represented as

```lean
open PseudoBoolean

variable {xs : Fin 5 → Fin 2}

def my_pb : PBIneq ![-1,2,-3,4,-5] xs 1 := sorry
```

This notation is under development and is subject to changes.

Now we can manipulate `PB`s, similarly to this `Toy Example`:

![toy_example](./docs/assets/toy_example.png "Toy Example")

```lean
variable {xs : Fin 4 → Fin 2}

--                     w x y z
example (c1 : PBIneq ![1,2,1,0] xs 2)
        (c2 : PBIneq ![1,2,4,2] xs 5)
        (c3 : PBIneq ![0,0,0,-1] xs (-1))
        : PBIneq ![1,2,2,0] xs 3
  := by
  let h2z : 2 > 0 := Nat.zero_lt_succ 1
  let h3z : 3 > 0 := Nat.zero_lt_succ 2
  let t1 : PBIneq ![2,4,2,0] xs 4      := by apply Multiplication c1 h2z
  let t2 : PBIneq ![3,6,6,2] xs 9      := by apply Addition t1 c2
  let t3 : PBIneq ![0,0,0,-2] xs (-2)  := by apply Multiplication c3 h2z
  let t4 : PBIneq ![3,6,6,0] xs 7      := by apply Addition t2 t3
  exact Division t4 h3z
  done
```
