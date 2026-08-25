import VerifiedReserving.ChainLadder
import VerifiedReserving.Recursion
import VerifiedReserving.BornhuetterFerguson
import VerifiedReserving.Stochastic
import VerifiedReserving.Ultimate
import VerifiedReserving.Variance

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
#print axioms ultimate_eq_mul_cdf
#print axioms bfReserve_smul
#print axioms bfReserve_add
#print axioms bfUltimate_of_ultimate
#print axioms bfReserve_of_ultimate
#print axioms one_le_cdf
#print axioms bfReserve_nonneg
#print axioms bfReserve_le
#print axioms RandomTriangle.stronglyMeasurable_Srv
#print axioms condExp_fhatRv
#print axioms RandomTriangle.stronglyMeasurable_fhatRv
#print axioms condExp_fhatRv_mul
#print axioms integral_fhatRv_mul
#print axioms integral_fhatRv
#print axioms RandomTriangle.ChatRv_succ
#print axioms RandomTriangle.stronglyMeasurable_ChatRv
#print axioms condExp_C_succ
#print axioms condExp_C_of_Mack1
#print axioms condExp_ChatRv
#print axioms condExp_ultimate_eq
#print axioms RandomTriangle.fhatRv_sub_eq
#print axioms RandomTriangle.sq_fhatRv_sub
#print axioms condExp_sq_fhatRv_sub
