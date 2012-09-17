from anf2cnf_sage import SageCNFEncoder
from sage.sat.solvers.dimacs import DIMACS
#from sage.sat.solvers.cryptominisat import CryptoMiniSat

def run_tests():
  var_names = ['x00','x01','x02','x03']
  R = BooleanPolynomialRing(len(var_names),var_names, order = 'deglex')
  x = R.gens()
  L = [x[0]*x[1]*x[2] + x[0]*x[2]*x[3] + x[1]*x[2] + x[1] + x[2] + x[3] + 1,\
       x[1]*x[2] + x[2]*x[3] + x[1]]

  # standard
  test_ss_ss(R,L)

  # linear partner
  #test_lps_ss(R,L)

  # double partner
  #test_dps_ss(R,L)

  # quadratic partner
  #test_qps_ss(R,L)

  # cubic partner
  #test_ss_cps(R,L)

  # standard (xor)
  #test_xor_ss_ss(R,L)

def test_ss_ss(R,L):
  fn = tmp_filename()
  solver = DIMACS(filename=fn)
  enc = SageCNFEncoder(solver, R, use_xor_clauses=False, cutting_number=4)
  enc(L,"SS","SS")
  _ = solver.write()
  print open(fn).read()

def test_lps_ss(R,L):
  fn = tmp_filename()
  solver = DIMACS(filename=fn)
  enc = SageCNFEncoder(solver, R, use_xor_clauses=False, cutting_number=4)
  enc(L,"LPS","SS")
  _ = solver.write()
  print open(fn).read()

def test_dps_ss(R,L):
  fn = tmp_filename()
  solver = DIMACS(filename=fn)
  enc = SageCNFEncoder(solver, R, use_xor_clauses=False, cutting_number=4)
  enc(L,"DPS","SS")
  _ = solver.write()
  print open(fn).read()

def test_qps_ss(R,L):
  fn = tmp_filename()
  solver = DIMACS(filename=fn)
  enc = SageCNFEncoder(solver, R, use_xor_clauses=False, cutting_number=4)
  enc(L,"QPS","SS")
  _ = solver.write()
  print open(fn).read()

def test_ss_cps(R,L):
  fn = tmp_filename()
  solver = DIMACS(filename=fn)
  enc = SageCNFEncoder(solver, R, use_xor_clauses=False, cutting_number=4)
  enc(L,"SS","CPS")
  _ = solver.write()
  print open(fn).read()

"""
def test_xor_ss_ss(R,L):
  fn = tmp_filename()
  solver = CryptoMiniSat(filename=fn)
  enc = SageCNFEncoder(solver, R, use_xor_clauses=True)
  enc(L,"SS","SS")
  _ = solver.write()
  print open(fn).read()
"""
