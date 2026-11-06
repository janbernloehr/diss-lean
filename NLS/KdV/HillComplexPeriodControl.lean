import NLS.KdV.HillComplexPeriodErrorBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillAbelianComplexPeriod_error_neighborhood :
    ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ ∀ p : Coeff 2, ‖p‖ ≤ ε →
      (∀ k : ℕ, 1 ≤ k → ∀ E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
        (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k),
        (E,p) ∈ hillAbelianComplexRootDomain 0 hq hr) ∧
      ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → n ≠ k → ∀ a : Coeff 2,
        ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
          (hillAbelianComplexPeriod 0 hq hr n k (a,p)-hillAbelianHilbertPeriod 0 hq hr n k a)‖ ≤
          D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(k : ℝ) := by
  obtain ⟨ε,C,hε,hC,hbound⟩ := exists_hillFreeGapContour_inverse_root_bound hq hr
  refine ⟨ε,2*Real.pi^2*C,hε,by positivity,?_⟩
  intro p hp
  refine ⟨fun k hk E hE => (hbound p hp k hk E hE).1,?_⟩
  intro n k hn hk hnk a
  exact norm_scaled_hillAbelianComplexPeriod_error_le hq hr n k hn hk hnk a p C hC.le
    (fun E hE => (hbound p hp k hk E hE).1)
    (fun E hE => (hbound p hp k hk E hE).2)

def HillComplexPeriodControl (ε D : ℝ) : Prop :=
  ∀ p : Coeff 2, ‖p‖ ≤ ε →
    (∀ k : ℕ, 1 ≤ k → ∀ E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k),
      (E,p) ∈ hillAbelianComplexRootDomain 0 hq hr) ∧
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → n ≠ k → ∀ a : Coeff 2,
      ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianComplexPeriod 0 hq hr n k (a,p)-hillAbelianHilbertPeriod 0 hq hr n k a)‖ ≤
        D*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(k : ℝ)

theorem exists_hillComplexPeriodControl :
    ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ HillComplexPeriodControl hq hr ε D :=
  exists_hillAbelianComplexPeriod_error_neighborhood hq hr

end NLS.KdV
