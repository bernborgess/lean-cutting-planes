Pseudo Boolean Rules
============

Input Axioms
-----------------------------

As a starting point for the pseudo boolean reasoning we will get constraints from the user, which are subject to a normalization process

Literal Axioms
-----------------------------

For any literal \\( l_i\\) we can create a constraint:
\\[ \frac{}
    {l_i \ge 0}
\\]

Addition Rule
-----------------------------
Two constraints can be added together, adding the coefficients and the constants. Another behaviour is that \\(x_i\\) and \\(\overline{x_i}\\) that may appear together cancel each other:
\\[ \frac
    {{\sum_i{a_i l_i} \ge A}\qquad {\sum_i{b_i l_i} \ge B}}
    {\sum_i{(a_i + b_i) l_i} \ge (A+B)}
\\]

Multiplication Rule
-----------------------------
A constraint can be multiplied by any \\( c \in \mathbb{N}^{+} \\):
\\[ \frac
    {\sum_i{a_i l_i} \ge A}
    {\sum_i{c a_i l_i} \ge c A}
\\]

Division Rule
-----------------------------
A constraint can be divided by any \\( c \in \mathbb{N}^{+} \\), and the the ceiling of this division in applied:
\\[ \frac
    {\sum_i{a_i l_i} \ge A}
    {\sum_i{ \lceil \frac{a_i}{c} \rceil l_i} \ge \lceil \frac{A}{c} \rceil}
\\]

Saturation Rule
-----------------------------
A constraint can be replace its coefficients by the minimum between them and the constant:
\\[ \frac
    {\sum_i{a_i l_i} \ge A}
    {\sum_i{ \min(a_i,A)\cdot l_i} \ge A}
\\]

All these rules can be seen in practice in the Worked Example