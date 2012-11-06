### Algebraic Normal Form (ANF) to Conjunctive Normal Form (CNF) Converter (SAGE version).
---

#### LICENSE
This program is free software; see [LICENSE][1] for more details.

#### FUNCTIONALITY
Converts a multivariate polynomial system over the finite field [GF(2)][2] in algebraic
normal form ([ANF][3]) into a logical formula in conjunctive normal form
([CNF][4]). 

#### FEATURES
* Variety of term substitution strategies, for more details please see the
  corresponding [paper][5]. On request a copy of the paper can be sent to the
  interested reader.
* Support for different clause types: 
  - DIMACS
  - XOR (for more details see the [cryptominisat homepage][6])

#### REQUIREMENTS
[SAGE][7] v5.3 or later.

#### USAGE & EXAMPLES
See doctests in [anf2cnf_sage.py][8].

#### CONTACT
For any questions you can contact Philipp Jovanovic via: <jovanovi@fim.uni-passau.de>

[1]: https://github.com/Daeinar/anf2cnf-sage/blob/master/LICENSE
[2]: https://en.wikipedia.org/wiki/GF(2)
[3]: https://en.wikipedia.org/wiki/Algebraic_normal_form
[4]: https://en.wikipedia.org/wiki/Conjunctive_normal_form
[5]: http://www.degruyter.com/view/j/gcc.2010.2.issue-2/gcc.2010.016/gcc.2010.016.xml
[6]: http://www.msoos.org/xor-clauses
[7]: http://www.sagemath.org
[8]: (https://github.com/Daeinar/anf2cnf-sage/blob/master/anf2cnf_sage.py)
