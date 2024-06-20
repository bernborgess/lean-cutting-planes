Pseudo Boolean Rules
============

Interaction
-----------------------------

As a starting point for the pseudo boolean reasoning we will get constraints from the user, which are subject to a normalization process. Then the rules can be applied to produce further inequalities

```lean
-- code goes here
def x := 3
```


Addition Rule
-----------------------------
Two constraints can be added together, adding the coefficients and the constants. Another behaviour is that \\(x_i\\) and \\(\overline{x_i}\\) that may appear together cancel each other:
\\[ \frac
    {{\sum_i{a_i l_i} \ge A}\qquad {\sum_i{b_i l_i} \ge B}}
    {\sum_i{(a_i + b_i) l_i} \ge (A+B)}
\\]

```lean
-- code goes here
```

Multiplication Rule
-----------------------------
A constraint can be multiplied by any \\( c \in \mathbb{N}^{+} \\):
\\[ \frac
    {\sum_i{a_i l_i} \ge A}
    {\sum_i{c a_i l_i} \ge c A}
\\]

```lean
-- code goes here
```

Division Rule
-----------------------------
A constraint can be divided by any \\( c \in \mathbb{N}^{+} \\), and the the ceiling of this division in applied:
\\[ \frac
    {\sum_i{a_i l_i} \ge A}
    {\sum_i{ \lceil \frac{a_i}{c} \rceil l_i} \ge \lceil \frac{A}{c} \rceil}
\\]

```lean
-- code goes here
```

Saturation Rule
-----------------------------
A constraint can replace its coefficients by the minimum between them and the constant:
\\[ \frac
    {\sum_i{a_i l_i} \ge A}
    {\sum_i{ \min(a_i,A)\cdot l_i} \ge A}
\\]

```lean
-- code goes here
```

All these rules can be seen in practice in the Worked Example