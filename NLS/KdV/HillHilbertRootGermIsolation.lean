import NLS.KdV.HillHilbertRootIsolation
import NLS.SequenceSpaces.PositiveDeletedSpace

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem eventually_hillAbelianHilbert_roots_isolated
    (n : ℕ) (a : Coeff 2 → PositiveDeletedCoeff 2 (n:ℤ))
    (ha : ContinuousAt a 0) (ha0 : a 0 = 0) :
    ∀ᶠ p in 𝓝 (0 : Coeff 2), ∀ k : ℕ, 1 ≤ k →
      hillAbelianHilbertRootEnergy (a p : Coeff 2) k ∈
        ball (hillRealGapCenter 0 hq hr k : ℂ)
          (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k) ∧
      ∀ m : ℕ, 1 ≤ m → m ≠ k →
        hillAbelianHilbertRootEnergy (a p : Coeff 2) m ∉
          closedBall (hillRealGapCenter 0 hq hr k : ℂ)
            (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k) := by
  have hc : ContinuousAt (fun p : Coeff 2 => ‖(a p : Coeff 2)‖) 0 :=
    (continuous_subtype_val.continuousAt.comp ha).norm
  have hlim : Tendsto (fun p : Coeff 2 => ‖(a p : Coeff 2)‖)
      (𝓝 (0 : Coeff 2)) (𝓝 (0:ℝ)) := by
    simpa only [ha0,ZeroMemClass.coe_zero,norm_zero] using hc.tendsto
  have hsmall : ∀ᶠ p in 𝓝 (0 : Coeff 2), ‖(a p : Coeff 2)‖ < Real.pi^2/4 :=
    hlim.eventually (Iio_mem_nhds (by positivity : (0:ℝ) < Real.pi^2/4))
  filter_upwards [hsmall] with p hp k hk
  exact ⟨hillAbelianHilbertRootEnergy_mem_free_contour_ball hq hr _ hp k hk,
    fun m hm hmk => hillAbelianHilbertRootEnergy_not_mem_other_free_closedBall hq hr
      _ hp m k hm hk hmk⟩

end NLS.KdV
