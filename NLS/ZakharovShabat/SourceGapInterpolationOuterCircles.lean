import NLS.ZakharovShabat.SourceGapInterpolationProduct
import NLS.ZakharovShabat.SingleSpectralProductsExterior
import NLS.ZakharovShabat.CentralDeformation
import NLS.ZakharovShabat.UniformThresholds

/-!
# Exterior circles for the gap interpolation product

The entire product of any `ℓᵖ` spectral sequence approaches its free
normalization uniformly outside fixed free-lattice discs. In particular,
the half-integer-radius circles in Lemma 12.7 are eventually zero-free
and carry a uniform product-to-sine estimate.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A single threshold controls the entire/free-sine ratio at every
large spectral parameter separated from the free lattice. -/
theorem exists_threshold_entireSingleSpectralProduct_div_free_close
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun m => ρ m - (Real.pi : ℂ) * m) p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ m : ℤ, r ≤ ‖z - (Real.pi : ℂ) * m‖) →
      ‖entireSingleSpectralProduct ρ z / (-2 * sin z) - 1‖ ≤ ε := by
  let S := {z : ℂ // ∀ m : ℤ, r ≤ ‖z - (Real.pi : ℂ) * m‖}
  have ht := tendsto_entireSingleSpectralProduct_div_free_of_separated
    hp ρ hρlp (fun z : S => z.val) tendsto_comap hr hrπ
      (fun z => z.property)
  have hn := (ht.sub_const 1).norm
  simp only [sub_self, norm_zero] at hn
  obtain ⟨R,hR⟩ := exists_threshold_of_eventually_comap_atTop
    (fun z : S => ‖z.val‖) (hn.eventually (gt_mem_nhds hε))
  exact ⟨R,fun z hz hsep => (hR ⟨z,hsep⟩ hz).le⟩

/-- The entire/free-sine ratio tends uniformly to one on the
half-integer-radius circles of Lemma 12.7. -/
theorem eventually_centralCircle_entireSingleSpectralProduct_div_free_close
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun m => ρ m - (Real.pi : ℂ) * m) p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0 : ℂ) (centralCircleRadius k),
      ‖entireSingleSpectralProduct ρ z / (-2 * sin z) - 1‖ ≤ ε := by
  obtain ⟨R,hR⟩ := exists_threshold_entireSingleSpectralProduct_div_free_close
    hp ρ hρlp (by positivity : 0 < Real.pi / 4) le_rfl hε
  obtain ⟨K,hK⟩ := exists_nat_gt (R / Real.pi)
  refine ⟨K,?_⟩
  intro k hk z hz
  have hK : R < (K : ℝ) * Real.pi := by
    apply (div_lt_iff₀ Real.pi_pos).mp
    exact_mod_cast hK
  have hkreal : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hRk : R ≤ centralCircleRadius k := by
    unfold centralCircleRadius
    nlinarith [Real.pi_pos]
  have hnorm : ‖z‖ = centralCircleRadius k := by
    simpa only [mem_sphere, dist_zero_right] using hz
  apply hR z (by rw [hnorm]; exact hRk)
  intro m
  have hsep := centralCircle_lattice_gap k hz m
  nlinarith [Real.pi_pos]

/-- All sufficiently large half-integer-radius circles avoid the
zeros of the entire interpolation product. -/
theorem eventually_centralCircle_entireSingleSpectralProduct_ne_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (ρ : ℤ → ℂ)
    (hρlp : Memℓp (fun m => ρ m - (Real.pi : ℂ) * m) p) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ z ∈ sphere (0 : ℂ) (centralCircleRadius k),
      entireSingleSpectralProduct ρ z ≠ 0 := by
  obtain ⟨K,hK⟩ :=
    eventually_centralCircle_entireSingleSpectralProduct_div_free_close
      hp ρ hρlp (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨K,?_⟩
  intro k hk z hz hzero
  have hbound := hK k hk z hz
  rw [hzero, zero_div, zero_sub, norm_neg, norm_one] at hbound
  norm_num at hbound

end NLS.ZakharovShabat
