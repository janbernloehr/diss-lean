import NLS.ZakharovShabat.CentralDeformation
import NLS.ZakharovShabat.UniformThresholds

/-! # Uniform exterior assertions on the half-integer circles -/

noncomputable section
open Set Filter Topology Metric
namespace NLS.ZakharovShabat

theorem tendsto_centralCircleRadius_atTop :
    Tendsto centralCircleRadius atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro R
  obtain ⟨K, hK⟩ := exists_nat_gt (R/Real.pi)
  filter_upwards [eventually_ge_atTop K] with k hk
  have hK : R < (K : ℝ)*Real.pi := by
    apply (div_lt_iff₀ Real.pi_pos).mp
    exact_mod_cast hK
  have hkreal : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  unfold centralCircleRadius
  nlinarith [Real.pi_pos]

/-- A separated exterior assertion holds on every sufficiently large
half-integer circle, uniformly over its spectral parameter. -/
theorem eventually_centralCircle_of_separated_threshold {P : ℂ → Prop}
    (hP : ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ m : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*m‖) → P z) :
    ∀ᶠ k : ℕ in atTop, ∀ z ∈ sphere (0 : ℂ) (centralCircleRadius k), P z := by
  obtain ⟨R, hR⟩ := hP
  filter_upwards [tendsto_centralCircleRadius_atTop.eventually_ge_atTop R] with k hk z hz
  have hnorm : ‖z‖ = centralCircleRadius k := by
    simpa only [mem_sphere, dist_zero_right] using hz
  apply hR z (by rw [hnorm]; exact hk)
  intro m
  have hsep := centralCircle_lattice_gap k hz m
  nlinarith [Real.pi_pos]

end NLS.ZakharovShabat
