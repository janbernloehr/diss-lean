import NLS.ZakharovShabat.DiscriminantExteriorDerivative
import NLS.ZakharovShabat.FreeSineExteriorBounds

/-!
# The exterior spectral-derivative ratio

The normalized reciprocal sine is bounded everywhere outside fixed free discs.
It converts the additive derivative error into the ratio to the free derivative.
The potential is fixed; local uniformity in the potential is a separate result.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A bound on normalized reciprocal sine converts additive errors to relative errors. -/
theorem norm_div_neg_two_sin_sub_one_le {z d : ℂ} (hz : sin z ≠ 0)
    {C : ℝ} (hC : 0 ≤ C) (hb : ‖(Real.exp |z.im| : ℂ)/sin z‖ ≤ C) :
    ‖d/(-2*sin z)-1‖ ≤ C*‖(d+2*sin z)/(Real.exp |z.im| : ℂ)‖ := by
  have he : d/(-2*sin z)-1 =
      -((d+2*sin z)/(Real.exp |z.im| : ℂ))*((Real.exp |z.im| : ℂ)/sin z)/2 := by
    have hex : (Real.exp |z.im| : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_ne_zero _)
    field_simp
    ring
  rw [he, norm_div, norm_mul, norm_neg, norm_ofNat]
  have hm := mul_le_mul_of_nonneg_left hb
    (norm_nonneg ((d+2*sin z)/(Real.exp |z.im| : ℂ)))
  have hn := norm_nonneg ((d+2*sin z)/(Real.exp |z.im| : ℂ))
  nlinarith

/-- For a fixed potential, the ratio to the free derivative tends to one throughout the exterior. -/
theorem tendsto_discriminant_derivative_div_free_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun i => deriv (canonicalDiscriminant hp φ) (z i)/(-2*sin (z i))) l (𝓝 1) := by
  obtain ⟨C, hC, hb⟩ := exists_bound_exp_im_div_sin_of_separated hr
  have ht := tendsto_discriminant_derivative_error_div_exp_of_separated hp hp1 φ hφ
    z hescape hr hrπ hsep
  have hn : Tendsto (fun i => C*‖(deriv (canonicalDiscriminant hp φ) (z i)+2*sin (z i))/
      (Real.exp |(z i).im| : ℂ)‖) l (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using ht.norm.const_mul C
  have he : Tendsto (fun i => deriv (canonicalDiscriminant hp φ) (z i)/(-2*sin (z i))-1)
      l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hn
    exact Eventually.of_forall (fun i => norm_div_neg_two_sin_sub_one_le
      (sin_ne_zero_of_notMem_freeLattice (notMem_freeLattice_of_separated hr (hsep i)))
      hC.le (hb (z i) (hsep i)))
  simpa only [sub_add_cancel, zero_add] using he.add_const 1

/-- Each tolerance has one threshold valid at every separated spectral parameter. -/
theorem exists_threshold_discriminant_derivative_div_free (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
      ‖deriv (canonicalDiscriminant hp φ) z/(-2*sin z)-1‖ ≤ ε := by
  let S := {z : ℂ // ∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖}
  have ht := tendsto_discriminant_derivative_div_free_of_separated hp hp1 φ hφ
    (fun z : S => z.val) tendsto_comap hr hrπ (fun z => z.property)
  have hn := (ht.sub_const 1).norm
  simp only [sub_self, norm_zero] at hn
  obtain ⟨R, hR⟩ := exists_threshold_of_eventually_comap_atTop (fun z : S => ‖z.val‖)
    (hn.eventually (gt_mem_nhds hε))
  exact ⟨R, fun z hz hsep => (hR ⟨z, hsep⟩ hz).le⟩

end NLS.ZakharovShabat
