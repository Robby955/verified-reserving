import VerifiedReserving

/-! Axiom audit: every theorem in the development must depend only on
`propext`, `Classical.choice`, `Quot.sound`. Run with
`lake env lean VerifiedReserving/Test/Axioms.lean`. -/

open VerifiedReserving

-- keep each audit line on one line so CI can grep it
set_option format.width 400

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
#print axioms RandomTriangle.trueCDR_apply
#print axioms condExp_trueCDR_eq_zero
#print axioms condExp_C_of_Mack1_at
#print axioms condExp_C_ultimate_of_Mack1
#print axioms trueCDR_eq
#print axioms obsCDR_eq_reserve_sub
#print axioms RandomTriangle.obsCDRRv_apply
#print axioms RandomTriangle.fhatRv_sub_eq
#print axioms RandomTriangle.sq_fhatRv_sub
#print axioms condExp_sq_fhatRv_sub
#print axioms weighted_sq_dev_eps
#print axioms RandomTriangle.sigma2Rv_eq
#print axioms condExp_wssRv
#print axioms condExp_sigma2Rv
#print axioms condExp_eps
#print axioms condExp_sq_C_succ
#print axioms condExp_sq_C_succ_tower
#print axioms procVar_eq_sum
#print axioms condVar_C_eq_procVar
#print axioms condExp_sq_sub_of_stronglyMeasurable
#print axioms condMsep_eq
#print axioms mackEstimation_eq_sum_relVar
#print axioms one_add_sum_le_prod_one_add
#print axioms remainder_nonneg
#print axioms remainder_two
#print axioms remainder_eq_zero_of_subsingleton_support
#print axioms prod_one_add_le_exp_sum
#print axioms mackEstimation_le_bbmwEstimation
#print axioms bbmwEstimation_sub_mackEstimation
#print axioms bbmwEstimation_eq_mackEstimation_of_one_factor
#print axioms bbmwEstimation_sub_mackEstimation_le
#print axioms mackEstimation_lt_bbmwEstimation_Cex
#print axioms exists_mackEstimation_lt_bbmwEstimation
#print axioms mackEstimation_eq_rowSum
#print axioms bbmwEstimation_eq_rowProd
#print axioms bbmwTotalEstimation_sub_mackTotalEstimation
#print axioms rowProd_sub_rowSum_nonneg
#print axioms mackTotalEstimation_le_bbmwTotalEstimation
#print axioms rohrMsep_eq_rohrProcess_add_rohrParameter
#print axioms rohrRelParam_eq_relVar
#print axioms rohrParameter_eq_mackEstimation
#print axioms Chat_eq_Chat_mul_prod
#print axioms rohrProcess_eq_mackProcess
#print axioms rohrMsep_eq_msep
#print axioms msep_div_ultimate_sq
#print axioms msep_eq_mackProcess_add_mackEstimation
#print axioms rohrMsep_eq_mackProcess_add_mackEstimation
#print axioms bbmwEstimation_sub_rohrParameter
#print axioms rohrParameter_le_bbmwEstimation
#print axioms rohrMsepTotal_eq_msepTotal
#print axioms NontrivialModel.exists_nontrivial_mack_model
#print axioms NontrivialModel.fhat0_unbiased
#print axioms NontrivialModel.ultimate_unbiased
#print axioms NontrivialModel.var_fhat0
#print axioms NontrivialModel.sigma2_unbiased

#print axioms setIntegral_inter_of_indep
#print axioms condExp_sup_of_indep
#print axioms RandomTriangle.stronglyMeasurable_rowSigmaAll
#print axioms RandomTriangle.stronglyMeasurable_rowSigma
#print axioms indep_rowSigmaAll_otherRowsAll
#print axioms indep_rowSigmaAll_otherRowsSigma
#print axioms RandomTriangle.D_eq_sup
#print axioms mack1_of_mack1Row
#print axioms mack3_of_mack3Row
#print axioms condExp_eps_rowSigma
#print axioms mack2'_of_rows
