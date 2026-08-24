import VerifiedReserving.ChainLadder
import VerifiedReserving.Recursion
import VerifiedReserving.Stochastic

/-! Axiom audit: every theorem in the development must depend only on
`propext`, `Classical.choice`, `Quot.sound`. Run with
`lake env lean VerifiedReserving/Test/Axioms.lean`. -/

open VerifiedReserving

#print axioms fhat_eq_weighted_average
#print axioms T_eq_sum_weighted_F
#print axioms weighted_sq_dev
#print axioms weighted_sq_dev_at_fhat
#print axioms Chat_succ
#print axioms Chat_diag
#print axioms reserve_zero_of_oldest
#print axioms msep_eq_sum_mackTerm
#print axioms se2rec_eq_closed
#print axioms se2rec_eq_msep
#print axioms RandomTriangle.stronglyMeasurable_Srv
#print axioms condExp_fhatRv
