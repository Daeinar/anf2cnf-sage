"""
ANF to CNF Converter supporting different conversion strategies.

AUTHORS: 

- Philipp Jovanovic (2012): Initial version. 
"""

##############################################################################
#  Copyright (C) 2012 Philipp Jovanovic
#  Distributed under the terms of the GNU General Public License (GPL)
#  The full text of the GPL is available at:
#                  http://www.gnu.org/licenses/
##############################################################################

from sage.sat.converters import ANF2CNFConverter

class SageCNFEncoder(ANF2CNFConverter):
  """
  ANF to CNF converter supporting different conversion strategies.
  """

  def __init__(self, solver, ring, use_xor_clauses=False, cutting_number=4):
    """
    INPUT:

    - ``solver`` - a SAT-solver instance.
    - ``ring`` - a :cls:`BooleanPolynomialRing`.
    - ``use_xor_clauses`` - boolean (default: ``False``) use XOR clauses. If
      ``True`` use only if ``solver`` supports it. 
    - ``cutting_number`` - integer (default: 4) maximum length of XOR chains after
      splitting if XOR clauses are not supported.  Supported values are 3,...,6.

    """
    assert(cutting_number in xrange(3,7))

    self.create_subpolys = {"SS": self.p_ss, "LPS": self.p_lps, \
        "DPS": self.p_dps, "QPS": self.p_qps, "CPS": self.p_cps}
    self.create_clauses = {"SS": self.c_ss, "LPS": self.c_lps, \
        "DPS": self.c_dps, "QPS": self.c_qps, "CPS": self.c_cps}

    self.solver = solver
    self.ring = ring
    self.one = self.ring.one()
    self.zero = self.ring.zero()
    if use_xor_clauses is not False:
      use_xor_clauses = hasattr(solver,"add_xor_clause")
    self.use_xor_clauses = use_xor_clauses
    self.cutting_number = cutting_number
    self._phi = [None]

    for x in sorted([x.lm() for x in self.ring.gens()], key=lambda x: x.index()):
      self.var(x)

  def __call__(self, F, qstrategy="SS", cstrategy="SS"):
    """
    Encode the boolean polynomials in ``F`` using the quadratic substitution
    strategy ``qstrategy``and the cubic substitution strategy ``cstrategy``.
    Monomials of degree > 3 are substituted using the standard strategy.

    INPUT:
    
    - ``F`` - list of :cls:`BooleanPolynomial`s.
    - ``qstrategy`` - string (default: "SS") sets the quadratic substitution
      strategy that should be used. 
    - ``cstrategy`` - string (default: "SS") sets the cubic substitution
      strategy that should be used. 

    """
    for f in F:
      self.clauses_strategy(f,qstrategy,cstrategy)
    return self.phi()
  
  def var(self, m=None, decision=None):
    """
    Return a *new* variable.

    This is a thin wrapper around the SAT-solvers function where
    we keep track of which SAT variable corresponds to which
    monomial.

    INPUT:

    - ``m`` - something the new variables maps to, usually a monomial or
      polynomial.
    - ``decision`` - is this variable a deicison variable?

    """
    self._phi.append(m)
    return self.solver.var(decision=decision)

  def phi(self):
    """
    Map SAT variables to polynomial variables.
    """
    return(self._phi)

  def clauses_strategy(self, f, qstrategy="SS", cstrategy="SS"):
    """
    Convert ``f`` using the quadratic substitution strategy ``qstrategy``and the
    cubic substitution strategy ``cstrategy``. Monomials of degree > 3 are
    substituted using the standard strategy.

    INPUT:

    - ``f`` - a :cls:`BooleanPolynomial`.
    - ``qstrategy`` - string (default: "SS") sets the quadratic substitution
      strategy that should be used. 
    - ``cstrategy`` - string (default: "SS") sets the cubic substitution
      strategy that should be used. 

    """
    assert(qstrategy in ["SS","LPS","DPS","QPS"]) 
    assert(cstrategy in ["SS","CPS"])

    hom_parts = self.homogeneous_parts(f)
    lin_poly = []
    for deg in hom_parts.keys()[::-1]:
      while len(hom_parts[deg]) != 0:
        m = hom_parts[deg].pop(0)
        if deg == 0:
          # Note: Index 0 corresponds to the constant coefficient 1!
          sub_var = self.phi().index(None)
        elif deg == 1:
          sub_var = self.phi().index(m) 
        elif deg == 2:
          sub_var = self.create_subpolys[qstrategy](m,hom_parts)
        elif deg == 3:
          sub_var = self.create_subpolys[cstrategy](m,hom_parts)
        else:
          sub_var = self.create_subpolys["SS"](m,hom_parts)
        lin_poly.append(sub_var)
   
    self.linearized(lin_poly)

  def homogeneous_parts(self,f):
    """
    Splits the polynomial ``f`` into its homogeneous parts and returns it as a
    dictionary.

    INPUT:

    - ``f`` - a :cls:`BooleanPolynomial`.

    OUTPUT: A dictionary h, where h[deg] returns a list containing all the
    monomials m of f where m.deg() == deg.

    """
    h = {}
    for m in f:
      if m.deg() not in h:
        h[m.deg()] = [m]
      else:
        h[m.deg()] += [m]
    return h

  def substitute(self,f,strategy):
    """
    Checks if the polynomial ``f`` was substituted before, if not, a new variable
    is introduced and the clauses for ``f`` are added to the solver.

    INPUT:

    - ``f`` - a :cls:`BooleanPolynomial`.
    - ``strategy`` - string that identifies the used substitution strategy.

    OUTPUT: An index for a SAT variable corresponding to ``f``.

    """
    if f not in self.phi():
      self.create_clauses[strategy](f,self.var(f))
    return self.phi().index(f)

  def p_ss(self,m,hom_parts):
    """
    Manages the Standard Substitution.

    INPUT:

    - ``m`` - a monomial.
    - ``hom_parts`` - dicitionary that contains all the (remaining) monomials of
      the currently processed polynomial.

    OUTPUT: An index for a SAT variable corresponding to ``f``. (see function substitute)

    """
    return self.substitute(m,"SS")
    
  def p_lps(self,m,hom_parts):
    """
    Manages the Linear Partner Substitution.

    INPUT:

    - ``m`` - a monomial.
    - ``hom_parts`` - dicitionary that contains all the (remaining) monomials of
      the currently processed polynomial.

    OUTPUT: An index for a SAT variable corresponding to ``f``. (see function substitute)

    """
    if 1 in hom_parts.keys():
      v = m.variables()
      if v[0] in hom_parts[1]:
        hom_parts[1].remove(v[0])
        return self.substitute(m+v[0],"LPS")
      elif v[1] in hom_parts[1]:
        hom_parts[1].remove(v[1])
        return self.substitute(m+v[1],"LPS")
    return self.substitute(m,"SS")

  def p_dps(self,m,hom_parts):
    """
    Manages the Double Partner Substitution.

    INPUT:

    - ``m`` - a monomial.
    - ``hom_parts`` - dicitionary that contains all the (remaining) monomials of
      the currently processed polynomial.

    OUTPUT: An index for a SAT variable corresponding to ``f``. (see function substitute)

    """
    if 0 in hom_parts.keys() and 1 in hom_parts.keys():
      v = m.variables()
      if v[0] in hom_parts[1] and v[1] in hom_parts[1] and self.one in hom_parts[0]:
        hom_parts[1].remove(v[0])
        hom_parts[1].remove(v[1])
        hom_parts[0].remove(self.one)
        return self.substitute(m+v[0]+v[1]+1,"DPS")
    else:
      return self.p_lps(m,hom_parts)

  def p_qps(self,m,hom_parts):
    """
    Manages the Quadratic Partner Substitution.

    INPUT:

    - ``m`` - a monomial.
    - ``hom_parts`` - dicitionary that contains all the (remaining) monomials of
      the currently processed polynomial.

    OUTPUT: An index for a SAT variable corresponding to ``f``. (see function substitute)

    """
    for t in hom_parts[2]:
      x = gcd(m,t)
      if x != 1:
        hom_parts[2].remove(t)
        return self.substitute(m+t,"QPS")
    return self.substitute(m,"SS")

  def p_cps(self,m,hom_parts):
    """
    Manages the Cubic Partner Substitution.

    INPUT:

    - ``m`` - a monomial.
    - ``hom_parts`` - dicitionary that contains all the (remaining) monomials of
      the currently processed polynomial.

    OUTPUT: An index for a SAT variable corresponding to ``f``. (see function substitute)

    """
    for t in hom_parts[3]:
      x = gcd(m,t)
      if x.deg() == 2:
        hom_parts[3].remove(t)
        return self.substitute(m+t,"CPS")
    return self.substitute(m,"SS")

  def c_ss(self,f,v):
    """
    Clauses for Standard Substitution:
    x[1]*...*x[n] + y <=> (x[1] | -y) & ... & (x[n] | -y) & (-x[1] | ... | -x[n] | y)

    INPUT:
    - ``f`` - a :cls:`BooleanPolynomial`.
    - ``v`` - boolean variable that was used for substituting ``f``.

    """
    l = []
    t = [self.phi().index(x) for x in f.variables()]
    for w in t:
      self.solver.add_clause((w,-v))
      l.append(-w)
    self.solver.add_clause(tuple(l+[v]))

  def c_lps(self,f,v):
    """
    Clauses for Linear Partner Substitution:
    x[1]*x[2] + x[1] + y <=> (x[1] | -y) & (-x[2] | -y) & (-x[1] | x[2] | y)

    INPUT:
    - ``f`` - a :cls:`BooleanPolynomial`
    - ``v`` - boolean variable that was used for substituting ``f``.

    """
    p = self.phi().index(f-f.lm())
    q = self.phi().index(f.lm()/(f-f.lm()))
    self.solver.add_clause((p,-v))
    self.solver.add_clause((-q,-v))
    self.solver.add_clause((-p,q,v))

  def c_dps(self,f,v):
    """
    Clauses for Double Partner Substitution:
    x[1]*x[2] + x[1] + x[2] + 1 + y <=> (-x[1] | -y) & (-x[2] | -y) & (x[1] | x[2] | y)

    INPUT:
    - ``f`` - a :cls:`BooleanPolynomial`.
    - ``v`` - boolean variable that was used for substituting ``f``.

    """
    w = f.variables()
    self.solver.add_clause((-self.phi().index(w[0]),-v))
    self.solver.add_clause((-self.phi().index(w[1]),-v))
    self.solver.add_clause((self.phi().index(w[0]),self.phi().index(w[1]),v))

  def c_qps(self,f,v):
    """
    Clauses for Quadratic Partner Substitution:
    x[1]*x[2] + x[1]*x[3] + y <=> 
    (x[1] | -y) & (x[2] | x[3] | -y) & (-x[2] | -x[3] | -y) &
    (-x[1] | -x[2] | x[3] | y) & (-x[1] | x[2] | -x[3] | y)

    INPUT:
    - ``f`` - a :cls:`BooleanPolynomial`.
    - ``v`` - boolean variable that was used for substituting ``f``.

    """
    t = list(f)
    p = self.phi().index(gcd(t[0],t[1]))
    w = [self.phi().index(x) for x in f.variables()]
    w.remove(p)
    self.solver.add_clause((p,-v))
    self.solver.add_clause(( w[0], w[1],-v))
    self.solver.add_clause((-w[0],-w[1],-v))
    self.solver.add_clause((-p,-w[0], w[1],v))
    self.solver.add_clause((-p, w[0],-w[1],v))

  def c_cps(self,f,v):
    """
    Clauses for Cubic Partner Substitution:
    x[1]*x[2]*x[3] + x[1]*x[2]*x[4] + y <=>
    (x[1] | -y) & (x[2] | -y) & (x[3] | x[4] | -y) & (-x[3] | -x[4] | -y) & 
    (-x[1] | -x[2] | -x[3] | x[4] | y) & (-x[1] | -x[2] | x[3] | -x[4] | y) 

    INPUT:

    - ``f`` - a :cls:`BooleanPolynomial`.
    - ``v`` - boolean variable that was used for substituting ``f``.

    """
    t = list(f)
    p = [self.phi().index(x) for x in gcd(t[0],t[1]).variables()]
    w = [self.phi().index(x) for x in f.variables()]
    w.remove(p[0])
    w.remove(p[1])
    self.solver.add_clause((p[0],-v))
    self.solver.add_clause((p[1],-v))
    self.solver.add_clause(( w[0], w[1],-v))
    self.solver.add_clause((-w[0],-w[1],-v))
    self.solver.add_clause((-p[0],-p[1],-w[0], w[1],v))
    self.solver.add_clause((-p[0],-p[1], w[0],-w[1],v))

  def linearized(self,f):
    """
    Converts the linearized polynomial ``f`` to its logical representation
    either with normal CNF or XOR clauses.

    INPUT:

    - ``f`` - list of index integers representing the linearized polynomial.

    """
    equal_zero = True
    if 0 in f:
      equal_zero = False
      f.remove(0)
    # XOR clauses
    if self.use_xor_clauses:
      if equal_zero:
        f[0] = -f[0]
      self.solver.add_xor_clause(tuple(f),False)
    # CNF clauses
    else:
      if len(f) > self.cutting_number:
        l = self.split(f)
      else:
        l = [f]
      clauses = []
      for i in xrange(len(l)):
        if i == len(l) - 1 and not equal_zero:
          clauses += self.c_lin_cnf(l[i],equal_zero)
        else:
          clauses += self.c_lin_cnf(l[i],True)
      for c in clauses:
        self.solver.add_clause(c)

  def split(self,f):
    """
    Splits the linearized polynomial ``f`` which is larger than the cutting
    number into smaller ones by introducing new variables.

    INPUT:

    - ``f`` - list of index integers representing the linearized polynomial.

    OUTPUT: list of lists where every of the inner lists represents a polynomial
    g (with len(support(g) <= cutting_number) that was broken off the polynomial
    ``f``. 

    """
    c = self.cutting_number
    l = []
    g = []
    while len(f) > 0:
      g.append(f.pop(0))
      if len(g) == c - 1 and len(f) != 0: 
        v = self.var()
        g.append(v)
        l.append(g)
        g = [v]
      if len(g) == 1 and len(f) < c:
        g.extend(f)
        l.append(g)
        break
    return l

  def c_lin_cnf(self,f,equal_zero):
    """
    CNF clauses for a linearized polynomial.

    INPUT: 

    - ``f`` - list of integers represeting a linearized polynomial.
    - ``equal_zero`` - boolean, true if f = 0 and false if f + 1 = 0.

    OUTPUT: A list of clauses modeling the polynomial ``f``.

    """
    c = []
    if equal_zero:
      if len(f) == 2:
        # x[1] + x[2]
        c.append((f[0],-f[1]))
        c.append((-f[0],f[1]))
      elif len(f) == 3:
        # x[1] + x[2] + x[3]
        c.append((-f[0], f[1], f[2]))
        c.append(( f[0],-f[1], f[2]))
        c.append((-f[0], f[1],-f[2]))
        c.append((-f[0],-f[1],-f[2]))
      elif len(f) == 4:
        # x[1] + x[2] + x[3] + x[4]
        c.append((-f[0], f[1], f[2], f[3]))
        c.append(( f[0],-f[1], f[2], f[3]))
        c.append(( f[0], f[1],-f[2], f[3]))
        c.append(( f[0], f[1], f[2],-f[3]))
        c.append((-f[0],-f[1],-f[2], f[3]))
        c.append((-f[0],-f[1], f[2],-f[3]))
        c.append((-f[0], f[1],-f[2],-f[3]))
        c.append(( f[0],-f[1],-f[2],-f[3]))
      elif len(f) == 5:
        # x[1] + x[2] + x[3] + x[4] + x[5]
        c.append((-f[0], f[1], f[2], f[3], f[4]))
        c.append(( f[0],-f[1], f[2], f[3], f[4]))
        c.append(( f[0], f[1],-f[2], f[3], f[4]))
        c.append(( f[0], f[1], f[2],-f[3], f[4]))
        c.append(( f[0], f[1], f[2], f[3],-f[4]))
        c.append((-f[0],-f[1],-f[2], f[3], f[4]))
        c.append((-f[0],-f[1], f[2],-f[3], f[4]))
        c.append((-f[0],-f[1], f[2], f[3],-f[4]))
        c.append((-f[0], f[1],-f[2], f[3],-f[4]))
        c.append((-f[0], f[1], f[2],-f[3],-f[4]))
        c.append((-f[0], f[1],-f[2],-f[3], f[4]))
        c.append(( f[0],-f[1], f[2],-f[3],-f[4]))
        c.append(( f[0], f[1],-f[2],-f[3],-f[4]))
        c.append(( f[0],-f[1],-f[2], f[3],-f[4]))
        c.append(( f[0],-f[1],-f[2],-f[3], f[4]))
        c.append((-f[0],-f[1],-f[2],-f[3],-f[4]))
      elif len(f) == 6:
        # x[1] + x[2] + x[3] + x[4] + x[5] + x[6]
        c.append((-f[0], f[1], f[2], f[3], f[4], f[5]))
        c.append(( f[0],-f[1], f[2], f[3], f[4], f[5]))
        c.append(( f[0], f[1],-f[2], f[3], f[4], f[5]))
        c.append(( f[0], f[1], f[2],-f[3], f[4], f[5]))
        c.append(( f[0], f[1], f[2], f[3],-f[4], f[5]))
        c.append(( f[0], f[1], f[2], f[3], f[4],-f[5]))
        c.append((-f[0],-f[1],-f[2], f[3], f[4], f[5]))
        c.append((-f[0],-f[1], f[2],-f[3], f[4], f[5]))
        c.append((-f[0],-f[1], f[2], f[3],-f[4], f[5]))
        c.append((-f[0],-f[1], f[2], f[3], f[4],-f[5]))
        c.append((-f[0], f[1],-f[2],-f[3], f[4], f[5]))
        c.append((-f[0], f[1],-f[2], f[3],-f[4], f[5]))
        c.append((-f[0], f[1],-f[2], f[3], f[4],-f[5]))
        c.append((-f[0], f[1], f[2],-f[3],-f[4], f[5]))
        c.append((-f[0], f[1], f[2],-f[3], f[4],-f[5]))
        c.append((-f[0], f[1], f[2], f[3],-f[4],-f[5]))
        c.append(( f[0],-f[1],-f[2],-f[3], f[4], f[5]))
        c.append(( f[0],-f[1],-f[2], f[3],-f[4], f[5]))
        c.append(( f[0],-f[1],-f[2], f[3], f[4],-f[5]))
        c.append(( f[0],-f[1], f[2],-f[3],-f[4], f[5]))
        c.append(( f[0],-f[1], f[2],-f[3], f[4],-f[5]))
        c.append(( f[0],-f[1], f[2], f[3],-f[4],-f[5]))
        c.append(( f[0], f[1],-f[2],-f[3],-f[4], f[5]))
        c.append(( f[0], f[1],-f[2],-f[3], f[4],-f[5]))
        c.append((-f[0], f[1],-f[2], f[3],-f[4],-f[5]))
        c.append((-f[0], f[1], f[2],-f[3],-f[4],-f[5]))
        c.append((-f[0],-f[1],-f[2],-f[3],-f[4], f[5]))
        c.append((-f[0],-f[1],-f[2],-f[3], f[4],-f[5]))
        c.append((-f[0],-f[1],-f[2], f[3],-f[4],-f[5]))
        c.append((-f[0],-f[1], f[2],-f[3],-f[4],-f[5]))
        c.append((-f[0], f[1],-f[2],-f[3],-f[4],-f[5]))
        c.append(( f[0],-f[1],-f[2],-f[3],-f[4],-f[5]))
    else:
      if len(f) == 2:
        # x[1] + x[2] + 1
        c.append((-f[0],-f[1]))
        c.append(( f[0], f[1]))
      elif len(f) == 3:
        # x[1] + x[2] + x[3] + 1
        c.append(( f[0], f[1], f[2]))
        c.append((-f[0],-f[1], f[2]))
        c.append((-f[0], f[1],-f[2]))
        c.append(( f[0],-f[1],-f[2]))
      elif len(f) == 4:
        # x[1] + x[2] + x[3] + x[4] + 1
        c.append(( f[0], f[1], f[2], f[3]))
        c.append((-f[0],-f[1], f[2], f[3]))
        c.append((-f[0], f[1],-f[2], f[3]))
        c.append((-f[0], f[1], f[2],-f[3]))
        c.append(( f[0],-f[1],-f[2], f[3]))
        c.append(( f[0],-f[1], f[2],-f[3]))
        c.append(( f[0], f[1],-f[2],-f[3]))
        c.append((-f[0],-f[1],-f[2],-f[3]))
      elif len(f) == 5:
        # x[1] + x[2] + x[3] + x[4] + x[5] + 1
        c.append(( f[0], f[1], f[2], f[3], f[4]))
        c.append((-f[0],-f[1], f[2], f[3], f[4]))
        c.append((-f[0], f[1],-f[2], f[3], f[4]))
        c.append((-f[0], f[1], f[2],-f[3], f[4]))
        c.append((-f[0], f[1], f[2], f[3],-f[4]))
        c.append(( f[0],-f[1],-f[2], f[3], f[4]))
        c.append(( f[0],-f[1], f[2],-f[3], f[4]))
        c.append(( f[0],-f[1], f[2], f[3],-f[4]))
        c.append(( f[0], f[1],-f[2],-f[3], f[4]))
        c.append(( f[0], f[1],-f[2], f[3],-f[4]))
        c.append(( f[0], f[1], f[2],-f[3],-f[4]))
        c.append((-f[0],-f[1],-f[2],-f[3], f[4]))
        c.append((-f[0],-f[1],-f[2], f[3],-f[4]))
        c.append((-f[0],-f[1], f[2],-f[3],-f[4]))
        c.append((-f[0], f[1],-f[2],-f[3],-f[4]))
        c.append(( f[0],-f[1],-f[2],-f[3],-f[4]))
      elif len(f) == 6:
        # x[1] + x[2] + x[3] + x[4] + x[5] + x[6] + 1
        c.append(( f[0], f[1], f[2], f[3], f[4], f[5]))
        c.append((-f[0],-f[1], f[2], f[3], f[4], f[5]))
        c.append((-f[0], f[1],-f[2], f[3], f[4], f[5]))
        c.append((-f[0], f[1], f[2],-f[3], f[4], f[5]))
        c.append((-f[0], f[1], f[2], f[3],-f[4], f[5]))
        c.append((-f[0], f[1], f[2], f[3], f[4],-f[5]))
        c.append(( f[0],-f[1],-f[2], f[3], f[4], f[5]))
        c.append(( f[0],-f[1], f[2],-f[3], f[4], f[5]))
        c.append(( f[0],-f[1], f[2], f[3],-f[4], f[5]))
        c.append(( f[0],-f[1], f[2], f[3], f[4],-f[5]))
        c.append(( f[0], f[1],-f[2],-f[3], f[4], f[5]))
        c.append(( f[0], f[1],-f[2], f[3],-f[4], f[5]))
        c.append(( f[0], f[1],-f[2], f[3], f[4],-f[5]))
        c.append(( f[0], f[1], f[2],-f[3],-f[4], f[5]))
        c.append(( f[0], f[1], f[2],-f[3], f[4],-f[5]))
        c.append(( f[0], f[1], f[2], f[3],-f[4],-f[5]))
        c.append((-f[0],-f[1],-f[2],-f[3], f[4], f[5]))
        c.append((-f[0],-f[1],-f[2], f[3],-f[4], f[5]))
        c.append((-f[0],-f[1], f[2],-f[3],-f[4], f[5]))
        c.append((-f[0], f[1],-f[2],-f[3],-f[4], f[5]))
        c.append(( f[0],-f[1],-f[2],-f[3],-f[4], f[5]))
        c.append((-f[0],-f[1],-f[2], f[3], f[4],-f[5]))
        c.append((-f[0],-f[1], f[2],-f[3], f[4],-f[5]))
        c.append((-f[0], f[1],-f[2],-f[3], f[4],-f[5]))
        c.append(( f[0],-f[1],-f[2],-f[3], f[4],-f[5]))
        c.append((-f[0],-f[1], f[2], f[3],-f[4],-f[5]))
        c.append((-f[0], f[1],-f[2], f[3],-f[4],-f[5]))
        c.append(( f[0],-f[1],-f[2], f[3],-f[4],-f[5]))
        c.append((-f[0], f[1], f[2],-f[3],-f[4],-f[5]))
        c.append(( f[0],-f[1], f[2],-f[3],-f[4],-f[5]))
        c.append(( f[0], f[1],-f[2],-f[3],-f[4],-f[5]))
        c.append((-f[0],-f[1],-f[2],-f[3],-f[4],-f[5]))
    return c
