import NLS.KdV.HillRootPeriodAffineFormula

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem hillAbelianRootUpdate_eq_add_single
    (m : ℕ) (hm : 1 ≤ m) (a : Coeff 2) (s : ℂ) :
    hillAbelianRootUpdate m (a,hillAbelianHilbertRootEnergy a m+(m : ℂ)*s) =
      a+lp.single 2 (m : ℤ) s := by
  ext j
  by_cases hj : j = (m : ℤ)
  · subst j
    rw [hillAbelianRootUpdate_apply_same,hillAbelianHilbertRootEnergy,lp.coeFn_add,
      Pi.add_apply,lp.single_apply,Pi.single_eq_same]
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    field_simp
    ring
  · rw [hillAbelianRootUpdate_apply_other m a _ j hj,lp.coeFn_add,Pi.add_apply,
      lp.single_apply_ne _ _ _ hj,add_zero]

theorem hillAbelianHilbertPsi_add_single
    (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n) (E : ℂ) (a : Coeff 2) (s : ℂ) :
    hillAbelianHilbertPsi n (E,a+lp.single 2 (m : ℤ) s) =
      hillAbelianHilbertPsi n (E,a)+(m : ℂ)*s*hillAbelianRootSlope n m E a := by
  have h0 : hillAbelianRootUpdate m (a,hillAbelianHilbertRootEnergy a m) = a := by
    simpa only [mul_zero,add_zero,lp.single_zero] using hillAbelianRootUpdate_eq_add_single m hm a 0
  rw [← hillAbelianRootUpdate_eq_add_single m hm a s,
    hillAbelianHilbertPsi_rootUpdate_eq_rootSlope n m hm hmn]
  conv_rhs => arg 1; rw [← h0,hillAbelianHilbertPsi_rootUpdate_eq_rootSlope n m hm hmn]
  ring

end NLS.KdV
