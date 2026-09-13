import NLS.ZakharovShabat.CanonicalProductsExteriorLimit
import NLS.ZakharovShabat.UniformThresholds

/-!
# Uniform lower bounds for canonical/free ratios at exterior infinity

The fixed-potential exterior limit yields one threshold for all spectral
parameters outside the chosen free discs, including those with bounded
imaginary part.
-/

noncomputable section
open Set Complex Filter Topology NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At large exterior parameters either parity ratio has norm at least one half. -/
theorem exists_threshold_canonicalParity_div_free_lower (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (k : ℤ) (hk : k = 0 ∨ k = 1)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
      (1 : ℝ)/2 ≤ ‖canonicalParityProduct hp φ k z/(freeDiscriminant z-2*wave k 1)‖ := by
  let S := {z : ℂ // ∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖}
  obtain ⟨R, hR⟩ := exists_threshold_half_le_norm (fun z : S => ‖z.val‖)
    (fun z : S => canonicalParityProduct hp φ k z.val/(freeDiscriminant z.val-2*wave k 1))
    (tendsto_canonicalParity_div_free_of_separated hp hp1 φ hφ k hk
      (fun z : S => z.val) tendsto_comap hr hrπ (fun z => z.property))
  exact ⟨R, fun z hz hsep => hR ⟨z, hsep⟩ hz⟩

/-- The full canonical/free ratio has the same uniform exterior lower bound. -/
theorem exists_threshold_canonicalPeriodic_div_free_lower (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
      (1 : ℝ)/2 ≤ ‖canonicalPeriodicProduct hp φ z/((freeDiscriminant z)^2-4)‖ := by
  let S := {z : ℂ // ∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖}
  obtain ⟨R, hR⟩ := exists_threshold_half_le_norm (fun z : S => ‖z.val‖)
    (fun z : S => canonicalPeriodicProduct hp φ z.val/((freeDiscriminant z.val)^2-4))
    (tendsto_canonicalPeriodic_div_free_of_separated hp hp1 φ hφ
      (fun z : S => z.val) tendsto_comap hr hrπ (fun z => z.property))
  exact ⟨R, fun z hz hsep => hR ⟨z, hsep⟩ hz⟩

end NLS.ZakharovShabat
