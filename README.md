### Algebraic Normal Form (ANF) to Conjunctive Normal Form (CNF) Converter (SAGE version).

#### LICENSE
This program is free software; see [LICENSE](https://github.com/Daeinar/anf2cnf-sage/blob/master/LICENSE) for more details.

#### FUNCTIONALITY
Converts a multivariate polynomial system over the finite field F2 in algebraic
normal form (ANF) into a logical formula in conjunctive normal form (CNF). 

#### FEATURES
* Support for different clause types: 
  - DIMACS
  - XOR (see the [cryptominisat homepage][1] for more details)
* Variety of term substitution strategies, for more details please [see][2].
  On request a copy of the above paper can be sent to the interested reader.

#### REQUIREMENTS
[SAGE][3] v5.3 or later.

#### USAGE & EXAMPLES
See doctests in [anf2cnf_sage.py](https://github.com/Daeinar/anf2cnf-sage/blob/master/anf2cnf_sage.py).

#### CONTACT
For any questions you can contact Philipp Jovanovic via:
<jovanovi at fim dot uni minus passau dot de>  

[1]: http://www.msoos.org/xor-clauses
[2]: http://www.degruyter.com/view/j/gcc.2010.2.issue-2/gcc.2010.016/gcc.2010.016.xml
[3]: http://www.sagemath.org
