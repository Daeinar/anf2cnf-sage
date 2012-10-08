#from anf2cnf_sage import SageCNFEncoder
from sage.sat.solvers.dimacs import DIMACS
from sage.sat.solvers.cryptominisat import CryptoMiniSat

def run_tests():
  var_names = ['x00','x01','x02','x03']
  R = BooleanPolynomialRing(len(var_names),var_names, order = 'deglex')
  x = R.gens()
  L = [x[0]*x[1]*x[2] + x[0]*x[2]*x[3] + x[1]*x[2] + x[1] + x[2] + x[3] + 1,\
       x[1]*x[2] + x[2]*x[3] + x[1]]

  # standard
  #test_strategies(R,L,"SS","SS",False)

  # linear partner
  #test_strategies(R,L,"LPS","SS",False)

  # double partner
  #test_strategies(R,L,"DPS","SS",False)

  # quadratic partner
  test_strategies(R,L,"QPS","SS",False)

  # cubic partner
  #test_strategies(R,L,"SS","CPS",False)

  # standard (xor)
  #test_strategies(R,L,"SS","SS",True)

def test_strategies(R,L,cs,qs,use_xor):
  if not use_xor:
    fn = tmp_filename()
    solver = DIMACS(filename=fn)
    enc = SageCNFEncoder(solver, R, use_xor_clauses=use_xor, cutting_number=4)
    enc(L,cs,qs)
    _ = solver.write()
    print open(fn).read()
  else:
    solver = CryptoMiniSat()
    enc = SageCNFEncoder(solver, R, use_xor_clauses=use_xor)
    enc(L,cs,qs)
    print(solver)
