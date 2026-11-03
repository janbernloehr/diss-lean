import NLS.ComplexAnalysis.HilbertWeightedProduct
import NLS.SequenceSpaces.PositiveReciprocalLattice
import NLS.SequenceSpaces.DeletedCoordinate

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV



def hillAbelianHilbertWeight (n : ℕ) : Coeff 2 :=
  Coeff.deleteCoordinate (n : ℤ)
    (((Real.pi : ℂ)^2)⁻¹ • Coeff.positivePuncturedLattice 2 (by norm_num))

def hillAbelianHilbertInput : ℂ × Coeff 2 →L[ℂ] Coeff 2 :=
  ContinuousLinearMap.snd ℂ ℂ (Coeff 2) -
    (ContinuousLinearMap.fst ℂ ℂ (Coeff 2)).smulRight
      (Coeff.positivePuncturedLattice 2 (by norm_num))

theorem hillAbelianHilbertInput_apply (t : ℂ × Coeff 2) (m : ℤ) :
    hillAbelianHilbertInput t m = t.2 m-t.1*Coeff.positivePuncturedLattice 2 (by norm_num) m := rfl

def hillAbelianHilbertProduct (n : ℕ) (t : ℂ × Coeff 2) : ℂ :=
  hilbertWeightedProduct (hillAbelianHilbertWeight n) (hillAbelianHilbertInput t)

theorem analyticOnNhd_hillAbelianHilbertProduct (n : ℕ) :
    AnalyticOnNhd ℂ (hillAbelianHilbertProduct n) univ := by
  intro t _
  exact (analyticOnNhd_hilbertWeightedProduct (hillAbelianHilbertWeight n) _ (mem_univ _)).comp
    (hillAbelianHilbertInput.analyticAt t)

theorem hillAbelianHilbertWeight_nonpositive (n : ℕ) (m : ℤ) (hm : m ≤ 0) :
    hillAbelianHilbertWeight n m = 0 := by
  by_cases hmn : m = (n : ℤ)
  · subst m
    exact Coeff.deleteCoordinate_apply_same _ _
  · rw [hillAbelianHilbertWeight,Coeff.deleteCoordinate_apply_other _ _ hmn]
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      Coeff.positivePuncturedLattice_apply,if_neg (by omega : ¬0 < m),mul_zero]

theorem hillAbelianHilbertWeight_positive (n k : ℕ) :
    hillAbelianHilbertWeight n ((k+1 : ℕ) : ℤ) =
      if k+1 = n then 0 else ((Real.pi : ℂ)^2)⁻¹ * ((k+1 : ℕ) : ℂ)⁻¹ := by
  by_cases hkn : k+1 = n
  · have he : ((k+1 : ℕ) : ℤ) = (n : ℤ) := by exact_mod_cast hkn
    rw [if_pos hkn,he,hillAbelianHilbertWeight,Coeff.deleteCoordinate_apply_same]
  · have he : ((k+1 : ℕ) : ℤ) ≠ (n : ℤ) := by exact_mod_cast hkn
    rw [if_neg hkn,hillAbelianHilbertWeight,Coeff.deleteCoordinate_apply_other _ _ he]
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Coeff.positivePuncturedLattice_natSucc]

end NLS.KdV
