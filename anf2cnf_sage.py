"""
Algebraic Normal Form (ANF) to Conjunctive Normal Form (CNF) converter with
support for different conversion strategies.

AUTHORS: 

- Philipp Jovanovic (2012): Initial version. 
"""

##############################################################################
#  Copyright (C) 2012 Philipp Jovanovic
#  Distributed under the terms of the GNU General Public License (GPL)
#  The full text of the GPL is available at:
#                  http://www.gnu.org/licenses/
##############################################################################

from itertools import combinations, ifilterfalse
from sage.sat.converters import ANF2CNFConverter

class SageCNFEncoder(ANF2CNFConverter):
    """
    ANF to CNF converter supporting different conversion strategies.
    """
  
    def __init__(self, solver, ring, use_xor_clauses=False, cutting_number=4):
        """
        Construct ANF to CNF converter over ``ring`` passing clauses to ``solver``.

        INPUT:
  
        - ``solver`` - a SAT-solver instance.
        - ``ring`` - a :cls:`BooleanPolynomialRing`.
        - ``use_xor_clauses`` - boolean (default: ``False``) use XOR clauses. If
          ``True`` use only if ``solver`` supports it. 
        - ``cutting_number`` - integer (default: 4) maximum length of XOR chains after
          splitting if XOR clauses are not supported.  Supported values are 3,...,6.
  
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b,c,d> = BooleanPolynomialRing()
            sage: enc = SageCNFEncoder(DIMACS(), R, cutting_number = 5)
            sage: enc.use_xor_clauses
            False
            sage: enc.cutting_number
            5
            sage: enc.phi
            [None, a, b, c, d]
    
            sage: from sage.sat.solvers.cryptominisat import CryptoMiniSat       # optional - cryptominisat
            sage: R.<a,b,c,d> = BooleanPolynomialRing()                          # optional - cryptominisat
            sage: enc = SageCNFEncoder(CryptoMiniSat(), R, use_xor_clauses=True) # optional - cryptominisat
            sage: enc.use_xor_clauses                                            # optional - cryptominisat
            True
            sage: enc.phi                                                        # optional - cryptominisat
            [None, a, b, c, d]
  
        """
        assert(cutting_number in xrange(3,8))
  
        self.create_subpolys = {"SS": self.p_ss, "LPS": self.p_lps, \
            "DPS": self.p_dps, "QPS": self.p_qps, "CPS": self.p_cps}
        self.create_clauses = {"SS": self.c_ss, "LPS": self.c_lps, \
            "DPS": self.c_dps, "QPS": self.c_qps, "CPS": self.c_cps}
  
        self.solver = solver
        self.ring = ring
        self._one = self.ring.one() 
        self.cutting_number = cutting_number
        self._phi = [None] 
        if use_xor_clauses is True:
          use_xor_clauses = hasattr(solver,"add_xor_clause")
        self.use_xor_clauses = use_xor_clauses
  
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
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b,c,d> = BooleanPolynomialRing()
            sage: L = [a*b*c + a*c*d + b*c + b + c + d + 1, b*c + c*d + b]
    
        Standard substitution::
    
            sage: enc = SageCNFEncoder(DIMACS(), R)
            sage: enc(L)
            [None, a, b, c, d, a*b*c, a*c*d, b*c, None, c*d]
          
        Linear partner substitution::
        
            sage: enc = SageCNFEncoder(DIMACS(), R)
            sage: enc(L, qstrategy="LPS")
            [None, a, b, c, d, a*b*c, a*c*d, b*c + b, None, c*d] 
    
        Double partner substitution::
    
            sage: enc = SageCNFEncoder(DIMACS(), R)
            sage: enc(L, qstrategy="DPS")
            [None, a, b, c, d, a*b*c, a*c*d, b*c + b + c + 1, b*c + b, c*d] 
    
        Quadratic partner substitution::
    
            sage: enc = SageCNFEncoder(DIMACS(), R)
            sage: enc(L, qstrategy="QPS")
            [None, a, b, c, d, a*b*c, a*c*d, b*c, None, b*c + c*d]
    
        Cubic partner substitution::
    
            sage: enc = SageCNFEncoder(DIMACS(), R)
            sage: enc(L, cstrategy="CPS")
            [None, a, b, c, d, a*b*c + a*c*d, b*c, None, c*d]
    
        Standard substitution (XOR)::
    
            sage: from sage.sat.solvers.cryptominisat import CryptoMiniSat          # optional - cryptominisat 
            sage: solver = CryptoMiniSat()                                          # optional - cryptominisat
            sage: enc = SageCNFEncoder(solver, R, use_xor_clauses=True)             # optional - cryptominisat
            sage: enc(L)                                                            # optional - cryptominisat
            [None, a, b, c, d, a*b*c, a*c*d, b*c, c*d] 
            sage: print(solver)                                                     # optional - cryptominisat
            CryptoMiniSat
            #vars:       8, #lits:      43, #clauses:       6, #learnt:       0, #assigns:       0 
    
        """
        for f in F:
          self.clauses_by_strategy(f,qstrategy,cstrategy)
        return self.phi
    
    def var(self, m=None, decision=None):
        """
        Return a *new* variable.
    
        This is a thin wrapper around the SAT-solvers function where
        we keep track of which SAT variable corresponds to which
        monomial / polynomial.
    
        INPUT:
    
        - ``m`` - something the new variables maps to, usually a monomial or
          polynomial.
        - ``decision`` - is this variable a deicison variable?
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b,c> = BooleanPolynomialRing()
            sage: enc = SageCNFEncoder(DIMACS(),R)
            sage: enc.var()
            4
    
        """
        self._phi.append(m)
        return self.solver.var(decision=decision)
  
    @property
    def phi(self):
        """
        Map SAT variables to polynomial variables.
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b,c> = BooleanPolynomialRing()
            sage: enc = SageCNFEncoder(DIMACS(),R)
            sage: enc.var()
            4
            sage: enc.phi
            [None, a, b, c, None]
    
        """
        return(self._phi)
  
    def clauses_by_strategy(self, f, qstrategy="SS", cstrategy="SS"):
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
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b,c> = BooleanPolynomialRing()
            sage: fn = tmp_filename()
            sage: solver = DIMACS(filename=fn)
            sage: enc = SageCNFEncoder(solver,R)
            sage: enc.clauses_by_strategy(a*b + c + 1,"SS","SS")
            sage: _ = solver.write()
            sage: print open(fn).read()
            p cnf 4 5
            1 -4 0
            2 -4 0
            -1 -2 4 0
            4 3 0
            -4 -3 0
    
        """
        hom_parts = self.homogeneous_parts(f)
        lin_poly = []
        for deg in hom_parts.keys()[::-1]:
          while len(hom_parts[deg]) != 0:
            m = hom_parts[deg].pop(0)
            try:
              if deg == 0:
                # Note: Index 0 corresponds to the constant coefficient +1!
                sub_var = self.phi.index(None)
              elif deg == 1:
                sub_var = self.phi.index(m) 
              elif deg == 2:
                sub_var = self.create_subpolys[qstrategy](m,hom_parts)
              elif deg == 3:
                sub_var = self.create_subpolys[cstrategy](m,hom_parts)
              else:
                sub_var = self.create_subpolys["SS"](m,hom_parts)
              lin_poly.append(sub_var)
            except KeyError as e:
              print "Unsupported conversion strategy:", e
              raise
       
        self.lin_to_clauses(lin_poly)
  
    def homogeneous_parts(self,f):
        """
        Splits the polynomial ``f`` into its homogeneous parts and returns it as a
        dictionary.
    
        INPUT:
    
        - ``f`` - a :cls:`BooleanPolynomial`.
    
        OUTPUT: A dictionary h, where h[deg] returns a list containing all the
        monomials m of f where m.deg() == deg.
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b,c> = BooleanPolynomialRing()
            sage: enc = SageCNFEncoder(DIMACS(),R)
            sage: enc.homogeneous_parts(a*b*c + a*b + a*c + b + c + 1)
            {0: [1], 1: [b, c], 2: [a*b, a*c], 3: [a*b*c]}
    
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
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b,c> = BooleanPolynomialRing()
            sage: fn = tmp_filename()
            sage: solver = DIMACS(filename=fn)
            sage: enc = SageCNFEncoder(solver,R)
            sage: enc.substitute(a*b,"SS")
            4
            sage: _ = solver.write()
            sage: print open(fn).read()
            p cnf 4 3
            1 -4 0
            2 -4 0
            -1 -2 4 0
            sage: enc.phi
            [None, a, b, c, a*b]
    
        """
        if f not in self.phi:
          self.create_clauses[strategy](f,self.var(f))
        return self.phi.index(f)
  
    def p_ss(self,m,hom_parts):
        """
        Manages the Standard Substitution.
    
        INPUT:
    
        - ``m`` - a monomial.
        - ``hom_parts`` - dicitionary that contains all the (remaining) monomials of
          the currently processed polynomial.
    
        OUTPUT: An index for a SAT variable corresponding to ``f``. (see function substitute)
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b,c> = BooleanPolynomialRing()
            sage: enc = SageCNFEncoder(DIMACS(),R)
            sage: h = enc.homogeneous_parts(a*b + a*c + a + b + 1)
            sage: print(h)
            {0: [1], 1: [a, b], 2: [a*b, a*c]}
            sage: enc.p_ss(a*b,h)
            4
            sage: enc.phi
            [None, a, b, c, a*b]
    
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
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b,c> = BooleanPolynomialRing()
            sage: enc = SageCNFEncoder(DIMACS(),R)
            sage: enc.p_lps(a*b,enc.homogeneous_parts(a*b + a*c + a + b + 1))
            4
            sage: enc.phi
            [None, a, b, c, a*b + a]
    
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
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b,c> = BooleanPolynomialRing()
            sage: enc = SageCNFEncoder(DIMACS(),R)
            sage: enc.p_dps(a*b,enc.homogeneous_parts(a*b + a*c + a + b + 1))
            4
            sage: enc.phi
            [None, a, b, c, a*b + a + b + 1]
    
        """
        if 0 in hom_parts.keys() and 1 in hom_parts.keys():
          v = m.variables()
          if v[0] in hom_parts[1] and v[1] in hom_parts[1] and self._one in hom_parts[0]:
            hom_parts[1].remove(v[0])
            hom_parts[1].remove(v[1])
            hom_parts[0].remove(self._one)
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
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b,c> = BooleanPolynomialRing()
            sage: enc = SageCNFEncoder(DIMACS(),R)
            sage: enc.p_qps(a*b,enc.homogeneous_parts(a*b + a*c + a + b + 1))
            4
            sage: enc.phi
            [None, a, b, c, a*b + a*c]
    
        """
        for t in hom_parts[2]:
          # TODO: Calculate the remainder below with the help of the division algorithm.
          if len(set(t.variables()).intersection(set(m.variables()))) == 1:  
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
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b,c,d> = BooleanPolynomialRing()
            sage: enc = SageCNFEncoder(DIMACS(),R)
            sage: enc.p_cps(a*b*c,enc.homogeneous_parts(a*b*c + a*b*d + a + b + 1))
            5
            sage: enc.phi
            [None, a, b, c, d, a*b*c + a*b*d]
    
        """
        for t in hom_parts[3]:
          # TODO: Calculate the remainder below with the help of the division algorithm.
          if len(set(t.variables()).intersection(set(m.variables()))) == 2:  
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
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b> = BooleanPolynomialRing()
            sage: fn = tmp_filename()
            sage: solver = DIMACS(filename=fn)
            sage: enc = SageCNFEncoder(solver,R)
            sage: enc.c_ss(a*b,enc.var())
            sage: _ = solver.write()
            sage: print open(fn).read()
            p cnf 3 3
            1 -3 0
            2 -3 0
            -1 -2 3 0
            sage: enc.phi
            [None, a, b, None]
    
        """
        l = []
        t = [self.phi.index(x) for x in f.variables()]
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
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b> = BooleanPolynomialRing()
            sage: fn = tmp_filename()
            sage: solver = DIMACS(filename=fn)
            sage: enc = SageCNFEncoder(solver,R)
            sage: enc.c_lps(a*b+a,enc.var())
            sage: _ = solver.write()
            sage: print open(fn).read()
            p cnf 3 3
            1 -3 0
            -2 -3 0
            -1 2 3 0
            sage: enc.phi
            [None, a, b, None]
    
        """
        p = self.phi.index(f-f.lm())
        q = self.phi.index(f.lm()/(f-f.lm()))
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
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b> = BooleanPolynomialRing()
            sage: fn = tmp_filename()
            sage: solver = DIMACS(filename=fn)
            sage: enc = SageCNFEncoder(solver,R)
            sage: enc.c_dps(a*b+a+b+1,enc.var())
            sage: _ = solver.write()
            sage: print open(fn).read()
            p cnf 3 3
            -1 -3 0
            -2 -3 0
            1 2 3 0
            sage: enc.phi
            [None, a, b, None]
    
        """
        w = f.variables()
        self.solver.add_clause((-self.phi.index(w[0]),-v))
        self.solver.add_clause((-self.phi.index(w[1]),-v))
        self.solver.add_clause((self.phi.index(w[0]),self.phi.index(w[1]),v))
  
    def c_qps(self,f,v):
        """
        Clauses for Quadratic Partner Substitution:
        x[1]*x[2] + x[1]*x[3] + y <=> 
        (x[1] | -y) & (x[2] | x[3] | -y) & (-x[2] | -x[3] | -y) &
        (-x[1] | -x[2] | x[3] | y) & (-x[1] | x[2] | -x[3] | y)
    
        INPUT:
    
        - ``f`` - a :cls:`BooleanPolynomial`.
        - ``v`` - boolean variable that was used for substituting ``f``.
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b,c> = BooleanPolynomialRing()
            sage: fn = tmp_filename()
            sage: solver = DIMACS(filename=fn)
            sage: enc = SageCNFEncoder(solver,R)
            sage: enc.c_qps(a*b+a*c,enc.var())
            sage: _ = solver.write()
            sage: print open(fn).read()
            p cnf 4 5
            1 -4 0
            2 3 -4 0
            -2 -3 -4 0
            -1 -2 3 4 0
            -1 2 -3 4 0
            sage: enc.phi
            [None, a, b, c, None]
    
        """
        t = list(f)
        p = self.phi.index(t[0].gcd(t[1]))
        w = [self.phi.index(x) for x in f.variables()]
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
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R.<a,b,c,d> = BooleanPolynomialRing()
            sage: fn = tmp_filename()
            sage: solver = DIMACS(filename=fn)
            sage: enc = SageCNFEncoder(solver,R)
            sage: enc.c_cps(a*b*c+a*b*d,enc.var())
            sage: _ = solver.write()
            sage: print open(fn).read()
            p cnf 5 6
            1 -5 0
            2 -5 0
            3 4 -5 0
            -3 -4 -5 0
            -1 -2 -3 4 5 0
            -1 -2 3 -4 5 0
            sage: enc.phi
            [None, a, b, c, d, None]
    
        """
        t = list(f)
        p = [self.phi.index(x) for x in (t[0].gcd(t[1])).variables()]
        w = [self.phi.index(x) for x in f.variables()]
        w.remove(p[0])
        w.remove(p[1])
        self.solver.add_clause((p[0],-v))
        self.solver.add_clause((p[1],-v))
        self.solver.add_clause(( w[0], w[1],-v))
        self.solver.add_clause((-w[0],-w[1],-v))
        self.solver.add_clause((-p[0],-p[1],-w[0], w[1],v))
        self.solver.add_clause((-p[0],-p[1], w[0],-w[1],v))
  
    def lin_to_clauses(self,f):
        """
        Converts the linearized polynomial ``f`` to its logical representation
        either with normal CNF or XOR clauses.
    
        INPUT:
    
        - ``f`` - list of index integers representing the linearized polynomial.
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R = BooleanPolynomialRing(4,'x')
    
        First lets convert the polynomial x[0] + x[1] + x[2] + x[3]:: 
    
            sage: fn = tmp_filename()
            sage: solver = DIMACS(filename=fn)
            sage: enc = SageCNFEncoder(solver,R,cutting_number=4,use_xor_clauses=False)
            sage: enc.lin_to_clauses([1,2,3,4])
            sage: _ = solver.write()
            sage: print open(fn).read()
            p cnf 4 8
            -1 2 3 4 0
            1 -2 3 4 0
            1 2 -3 4 0
            1 2 3 -4 0
            -1 -2 -3 4 0
            -1 -2 3 -4 0
            -1 2 -3 -4 0
            1 -2 -3 -4 0
    
        Now we convert the polynomial x[0] + x[1] + x[2] + x[3] + 1::
    
            sage: fn = tmp_filename()
            sage: solver = DIMACS(filename=fn)
            sage: enc = SageCNFEncoder(solver,R,cutting_number=4,use_xor_clauses=False)
            sage: enc.lin_to_clauses([0,1,2,3,4])
            sage: _ = solver.write()
            sage: print open(fn).read()
            p cnf 4 8
            1 2 3 4 0
            -1 -2 3 4 0
            -1 2 -3 4 0
            -1 2 3 -4 0
            1 -2 -3 4 0
            1 -2 3 -4 0
            1 2 -3 -4 0
            -1 -2 -3 -4 0
        
        # TODO: improve the tests below!
        And now the same with XOR clauses. First x[0] + x[1] + x[2] + x[3]::
    
            sage: from sage.sat.solvers.cryptominisat import CryptoMiniSat               # optional - cryptominisat
            sage: solver = CryptoMiniSat()                                               # optional - cryptominisat
            sage: enc = SageCNFEncoder(solver,R,use_xor_clauses=True)                    # optional - cryptominisat
            sage: enc.lin_to_clauses([1,2,3,4])                                          # optional - cryptominisat
            sage: solver()                                                               # optional - cryptominisat
            (None, False, False, True, False)
            sage: print(solver)                                                          # optional - cryptominisat
            CryptoMiniSat
            #vars:       4, #lits:       4, #clauses:       1, #learnt:       0, #assigns:       0
    
        Second x[0] + x[1] + x[2] + x[3] + 1::
    
            sage: from sage.sat.solvers.cryptominisat import CryptoMiniSat               # optional - cryptominisat
            sage: solver = CryptoMiniSat()                                               # optional - cryptominisat
            sage: enc = SageCNFEncoder(solver,R,use_xor_clauses=True)                    # optional - cryptominisat
            sage: enc.lin_to_clauses([0,1,2,3,4])                                        # optional - cryptominisat
            sage: solver()                                                               # optional - cryptominisat
            (None, False, True, False, False)
            sage: print(solver)                                                          # optional - cryptominisat
            CryptoMiniSat
            #vars:       4, #lits:       4, #clauses:       1, #learnt:       0, #assigns:       0
    
        """
        equal_zero = True
        # Note: The entry '0' here corresponds to the constant +1.
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
          for i in xrange(len(l)):
            if i == len(l) - 1 and not equal_zero:
              self.c_lin_cnf(l[i],1)
            else:
              self.c_lin_cnf(l[i],0)
  
    def split(self,f):
        """
        Splits the linearized polynomial ``f`` which is larger than the cutting
        number into smaller ones by introducing new variables.
    
        INPUT:
    
        - ``f`` - list of index integers representing the linearized polynomial.
    
        OUTPUT: list of lists where every of the inner lists represents a polynomial
        g (with len(support(g) <= cutting_number) that was broken off the polynomial
        ``f``.
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R = BooleanPolynomialRing(7, 'x')
            sage: solver = DIMACS()
            sage: enc = SageCNFEncoder(solver,R,cutting_number=4)
            sage: enc.split([1,2,3,4,5,6,7])
            [[1, 2, 3, 8], [8, 4, 5, 9], [9, 6, 7]]
    
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
  
    def c_lin_cnf(self,f,t):
        """
        CNF clauses for a linearized polynomial.
    
        INPUT: 
    
        - ``f`` - list of integers represeting a linearized polynomial.
        - ``t`` - integer with t == 0 iif f = 0 and t == 1 iif f + 1 = 0.
    
        EXAMPLES::
    
            sage: from sage.sat.solvers.dimacs import DIMACS
            sage: R = BooleanPolynomialRing(5, 'x')
            sage: fn = tmp_filename()
            sage: solver = DIMACS(filename=fn)
            sage: enc = SageCNFEncoder(solver,R,cutting_number=5)
            sage: enc.c_lin_cnf([1,2,3,4,5],0)
            sage: _ = solver.write()
            sage: print open(fn).read()
            p cnf 5 16
            -1 2 3 4 5 0
            1 -2 3 4 5 0
            1 2 -3 4 5 0
            1 2 3 -4 5 0
            1 2 3 4 -5 0
            -1 -2 -3 4 5 0
            -1 -2 3 -4 5 0
            -1 -2 3 4 -5 0
            -1 2 -3 -4 5 0
            -1 2 -3 4 -5 0
            -1 2 3 -4 -5 0
            1 -2 -3 -4 5 0
            1 -2 -3 4 -5 0
            1 -2 3 -4 -5 0
            1 2 -3 -4 -5 0
            -1 -2 -3 -4 -5 0
      
            sage: fn = tmp_filename()
            sage: solver = DIMACS(filename=fn)
            sage: enc = SageCNFEncoder(solver,R,cutting_number=5)
            sage: enc.c_lin_cnf([1,2,3,4,5],1)
            sage: _ = solver.write()
            sage: print open(fn).read()
            p cnf 5 16
            1 2 3 4 5 0
            -1 -2 3 4 5 0
            -1 2 -3 4 5 0
            -1 2 3 -4 5 0
            -1 2 3 4 -5 0
            1 -2 -3 4 5 0
            1 -2 3 -4 5 0
            1 -2 3 4 -5 0
            1 2 -3 -4 5 0
            1 2 -3 4 -5 0
            1 2 3 -4 -5 0
            -1 -2 -3 -4 5 0
            -1 -2 -3 4 -5 0
            -1 -2 3 -4 -5 0
            -1 2 -3 -4 -5 0
            1 -2 -3 -4 -5 0
    
        .. NOTE::
    
            To compute the clauses for a linear polynomial f of length n we enumerate
            all k-combinations for a set with n elements. The k-combinations then show
            us where to set the minus when constructing a clause. There are four
            cases to distinguish: 
            f = 0 and n%2 = 0: enumerate binomial(n,1), ..., binomial(n,2*i+1), ..., binomial(n,n-1)
            f = 0 and n%2 = 1: enumerate binomial(n,1), ..., binomial(n,2*i+1), ..., binomial(n,n)
            f = 1 and n%2 = 0: enumerate binomial(n,0), ..., binomial(n,2*i  ), ..., binomial(n,n)
            f = 1 and n%2 = 1: enumerate binomial(n,0), ..., binomial(n,2*i  ), ..., binomial(n,n-2)
    
        """
        for k in ifilterfalse(lambda x: x%2==t, xrange(len(f)+1)):
          for indices in combinations(xrange(len(f)),k):
            g = list(f)
            for i in indices:
              g[i] = -g[i]
            self.solver.add_clause(tuple(g)) 
  
