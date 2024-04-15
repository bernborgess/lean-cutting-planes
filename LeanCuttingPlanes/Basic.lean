/-! # Representation of a Linear Inequality

  ## Basic Definition

  As stated in [Jakob Nordstrom's talk](https://jakobnordstrom.se/docs/presentations/TalkSimons2102_PseudoBooleanSolvingLiveTalk.pdf),
  Pseudo-Boolean constraints are 0-1 integer linear constraints
    `  ∑ᵢ aᵢlᵢ ⋈ A `

  With the following components

 * Coefficients aᵢ
 Are integers ℤ that represent some weight of each variable in our problem

 * Variables lᵢ
 Are integers either 0 or 1, that represent whether we set or not that variable

 * Constant A
 Is an integer ℤ that represents our constraint

 * Operator ⋈
 Is the relation that serves our inequality, such that ⋈ ∈ {≥,≤,=,>,<}.


  ## Normalized Form

  To perform the proofs about linear inequalities it is much simpler to set a normal form
  that can represent all other inequalities and prove theorems about it, without any loss
  of generality.

  In this library, we have settled in the following notation:
  pseudo-Boolean PBO format (only linear objective and constraints)

  * ⋈ is always ≥
  * aᵢ is a list of ℤ
  * A is a ℤ





-/
