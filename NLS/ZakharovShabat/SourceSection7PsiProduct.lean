import NLS.ZakharovShabat.SourcePsiCandidate

/-! The corrected literal psi product in the Section 7 overview. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual psi numerator has one denominator per retained mode and the outer 1/pi_n. -/
theorem sourceSection7_psi_product (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : Coeff p) (z : ℂ) :
    Tendsto (fun N : ℕ =>
      (-2 / singleSpectralDenominator n) *
        ∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
          (displacedRoots a m-z)/singleSpectralDenominator m)
      atTop (𝓝 (sourcePsiCandidate n (z,a))) := by
  convert tendsto_sourcePsiCandidate_partialProduct hp hp1 n (z,a) using 1
  funext N
  simp only [jointDeletedSingleSpectralPartialProduct,singleSpectralFactor]
  ring

end NLS.ZakharovShabat
