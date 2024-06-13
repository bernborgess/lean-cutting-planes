Introduction
============

Cutting Planes and Lean 4
-----------------------------

*Cutting Planes* is a formal logic used in the context of discrete combinatorial problems, that can be applied in _Software testing_, _Formal verification_ and _Proof logging_.

Our proofs will consist of _Pseudo-Boolean Constraints_, that are 0-1 integer linear inequalities of the form:
\\[ \sum_i{a_i l_i} \ge A \\]
Where we have:
- constant \\( A \in \mathbb{Z} \\)
- coefficients \\( a_i \in \mathbb{Z} \\)
- literals \\( l_i: x_i\ \text{or}\ \overline{x_i}\ (\text{where } x_i + \overline{x_i} = 1) \\)
- variables \\( x_i \\) take values \\( 0 = false \\) or \\( 1 = true \\)

Without loss of generality, we will use the [normalized form](https://pure.mpg.de/rest/items/item_1832217_4/component/file_2574300/content#page=7), with all \\( a_i, A\\) non-negative.

In this regard, _Pseudo-Boolean Reasoning_ works on two axioms and four rules, each of which are formally verified in this project using _Lean 4_

[Lean 4](https://lean-lang.org/) is a theorem prover and programming language developed by [Leonardo de Moura](http://leodemoura.github.io/). In the last years it became proeminent in the mathematics community, after [The Xena Project](https://www.ma.imperial.ac.uk/~buzzard/xena/) of Imperial College London formalized Peter Scholze's proof in the area of condensed mathematics in 2021. In 2023 Terence Tao used Lean to formalize a proof of the _Polynomial Freiman-Ruzsa [(PFR)](https://teorth.github.io/pfr/) conjecture_, published in the same year.

Armed with a Lean 4 proof of the reasoning rules, complex proofs that involve these steps can be guaranteed to be correct.
