Pseudo Boolean Rules
============

Interaction
-----------------------------

As a starting point for the pseudo boolean reasoning we will get constraints from the user, which are subject to a normalization process. Then the rules can be applied to produce further inequalities
\\[
    xs := [0,1]
\\]

\\[
    as := [(1,0),(2,0)] \equiv x + 2y 
\\]

\\[
    bs := [(0,3),(2,0)] \equiv 3 \overline{x} + 2y
\\]

\\[
    {{c1 := \sum_i{as_i xs_i} \ge 2}\qquad {c2 := \sum_i{bs_i xs_i} \ge 5}}
\\]
```lean
def xs : Fin 2 → Fin 2 := ![0,1]
def c1 : PBIneq ![(1,0),(2,0)] xs 2
def c2 : PBIneq ![(0,3),(2,0)] xs 5
```


Addition Rule
-----------------------------
Two constraints can be added together, adding the coefficients and the constants. Another behaviour is that \\(x_i\\) and \\(\overline{x_i}\\) that may appear together cancel each other:
\\[ \frac
    {{\sum_i{a_i l_i} \ge A}\qquad {\sum_i{b_i l_i} \ge B}}
    {\sum_i{(a_i + b_i) l_i} \ge (A+B)}
\\]

```lean
def xs : Fin 2 → Fin 2 := ![0,1]
def c1 : PBIneq ![(1,0),(2,0)] xs 2
def c2 : PBIneq ![(0,3),(2,0)] xs 5
-----------------------------------
def c3 : PBIneq ![(0,2),(4,0)] xs 6 := by apply Addition c1 c2
```

Multiplication Rule
-----------------------------
A constraint can be multiplied by any \\( c \in \mathbb{N}^{+} \\):
\\[ \frac
    {\sum_i{a_i l_i} \ge A}
    {\sum_i{c a_i l_i} \ge c A}
\\]

```lean
def xs : Fin 2 → Fin 2
def c1 : PBIneq ![(1,0),(2,0)] xs 2
-----------------------------------
def c2 : PBIneq ![(2,0),(4,0)] xs 4 := by apply Multiplication c1 2
```

Division Rule
-----------------------------
A constraint can be divided by any \\( c \in \mathbb{N}^{+} \\), and the the ceiling of this division in applied:
\\[ \frac
    {\sum_i{a_i l_i} \ge A}
    {\sum_i{ \lceil \frac{a_i}{c} \rceil l_i} \ge \lceil \frac{A}{c} \rceil}
\\]

```lean
def xs : Fin 2 → Fin 2
def c1 : PBIneq ![(3,0),(6,0)] xs 7
-----------------------------------
def c2 : PBIneq ![(1,0),(2,0)] xs 3 := by apply Division c1 3
```

Saturation Rule
-----------------------------
A constraint can replace its coefficients by the minimum between them and the constant:
\\[ \frac
    {\sum_i{a_i l_i} \ge A}
    {\sum_i{ \min(a_i,A)\cdot l_i} \ge A}
\\]

```lean
def xs : Fin 2 → Fin 2
def c1 : PBIneq ![(3,0),(6,0)] xs 3
-----------------------------------
def c2 : PBIneq ![(3,0),(3,0)] xs 3 := by apply Saturation c1
```

All these rules can be seen in practice in the [Worked Example](./worked_example.md)