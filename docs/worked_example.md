Worked Example
============

Input
-----------------------------

For this example, in constraints over variables \\(w,x,y,z\\) we will have two input axioms:

1. \\( w + 2x + y \ge 2 \\)
1. \\( w + 2x + 4y + 2z \ge 5 \\)

Goal 
-----------------------------
The objective of this example is to prove:
\\[ w + 2x + 2y \ge 3 \\]

Execution
-----------------------------
We start by using muliplication of the first constraint by 2:
\\[ \frac
    {w + 2x + y \ge 2}
    {2w + 4x + 2y \ge 4}
    (\text{Multiply by 2})
\\]
Now we add this result to constraint 2:
\\[ \frac
    {{2w + 4x + 2y \ge 4}\qquad {w + 2x + 4y + 2z \ge 5}}
    {3w + 6x + 6y + 2z \ge 9}
    (\text{Add})
\\]
At this point we want to remove the variable \\(z\\), as it does not appear in our goal. Then we will introduce a \\(\overline{z} \ge 0\\) by the literal axiom and then multiply it by 2:
\\[ \frac
    {\overline{z} \ge 0}
    {2\overline{z} \ge 0}
    (\text{Multiply by 2})
\\]
Performing addition will cancel out the \\(z\\) variable:
\\[ \frac
    {{3w + 6x + 6y + 2z \ge 9}\qquad {2\overline{z} \ge 0}}
    {3w + 6x + 6y \ge 7}
    (\text{Add})
\\]
And lastly a division by 3 is performed to arrive at the goal:
\\[ \frac
    {3w + 6x + 6y \ge 7}
    {w + 2x + 2y \ge 3}
    (\text{Divide by 3})
\\]

Summarizing, this is the full proof:









![alt](./assets/toy_example.png)
