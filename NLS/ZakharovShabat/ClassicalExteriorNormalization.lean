import NLS.ZakharovShabat.EntireFreeDiscBounds
import NLS.ZakharovShabat.ClassicalQuotientsVerticalLimit

/-!
# Exact normalization from bounds at exterior infinity

The missing bound need only hold at large parameters outside fixed free
discs. Compactness and maximum modulus supply global boundedness; the proved
vertical limit then fixes the entire factor to one.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
namespace NLS.ZakharovShabat

theorem canonicalParity_eq_classical_of_exterior_quotient_bound
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (k : ℤ) (hk : k = 0 ∨ k = 1) {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (R B : ℝ)
    (hb : ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
      ‖classicalParityProductQuotient φ Φ k z‖ ≤ B) (z : ℂ) :
    canonicalParityProduct (by simp) φ k z = classicalDiscriminant Φ z-2*wave k 1 := by
  apply canonicalParity_eq_classical_of_bounded_quotient φ hφ Φ hΦ k hk
  apply isBounded_entire_of_bound_off_freeDiscs _ hr hrπ R B hb
  intro w
  exact (analyticOnNhd_classicalParityProductQuotient φ hφ Φ hΦ k hk w (mem_univ _)).differentiableAt

theorem canonicalPeriodic_eq_classical_of_exterior_quotient_bound
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) (R B : ℝ)
    (hb : ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
      ‖classicalPeriodicProductQuotient φ Φ z‖ ≤ B) (z : ℂ) :
    canonicalPeriodicProduct (by simp) φ z = (classicalDiscriminant Φ z)^2-4 := by
  apply canonicalPeriodic_eq_classical_of_bounded_quotient φ hφ Φ hΦ
  apply isBounded_entire_of_bound_off_freeDiscs _ hr hrπ R B hb
  intro w
  exact (analyticOnNhd_classicalPeriodicProductQuotient φ hφ Φ hΦ w (mem_univ _)).differentiableAt

end NLS.ZakharovShabat
