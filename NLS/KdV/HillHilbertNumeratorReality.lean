import NLS.KdV.HillAbelianPeriodConjugation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem hillAbelianHilbertPsi_im_eq_zero_of_real_roots
    (n : ℕ) (a : Coeff 2) (ha : star a = a) (x : ℝ) :
    (hillAbelianHilbertPsi n ((x:ℂ),a)).im = 0 := by
  have hc := hillAbelianHilbertPsi_conj n (x:ℂ) a
  rw [Complex.conj_ofReal,ha] at hc
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

end NLS.KdV
