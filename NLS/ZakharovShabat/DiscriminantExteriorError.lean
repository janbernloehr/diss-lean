import NLS.ZakharovShabat.FiniteDiscriminant
import NLS.ZakharovShabat.CanonicalProductsExteriorLimit
import NLS.ZakharovShabat.ClassicalHorizontalStripBounds
import NLS.ZakharovShabat.FreeCosineZeroAudit

/-!
# Additive discriminant asymptotics on the full free-disc exterior

The even product's valid free normalization controls the trace error after
division by exp(abs(Im z)). This normalization includes free cosine zeros.
The potential is fixed; local uniformity over potential neighborhoods remains
separate from these uniform spectral thresholds.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The free even factor has a global exponential bound, including on the real axis. -/
theorem norm_freeDiscriminant_sub_two_div_exp_im_le (z : ℂ) :
    ‖(freeDiscriminant z-2)/(Real.exp |z.im| : ℂ)‖ ≤ 4 := by
  have ht : ‖freeDiscriminant z‖ ≤ 2*Real.exp |z.im| := by
    simpa only [classicalDiscriminant_free, norm_zero, add_zero] using
      norm_classicalDiscriminant_le_exp_im 0 z
  have he : 1 ≤ Real.exp |z.im| := Real.one_le_exp_iff.mpr (abs_nonneg _)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have h := norm_sub_le (freeDiscriminant z) (2 : ℂ)
  norm_num at h
  linarith

/-- The normalized additive trace error is bounded by four times the even relative-product error. -/
theorem norm_discriminant_error_div_exp_le (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) :
    ‖(canonicalDiscriminant hp φ z-freeDiscriminant z)/(Real.exp |z.im| : ℂ)‖ ≤
      4*‖canonicalParityProduct hp φ 0 z/(freeDiscriminant z-2)-1‖ := by
  have hd : freeDiscriminant z-2 ≠ 0 :=
    freeDiscriminant_sub_ne_zero_of_sq_eq_four 2 (by norm_num) z hz
  have he : (canonicalDiscriminant hp φ z-freeDiscriminant z)/(Real.exp |z.im| : ℂ) =
      (canonicalParityProduct hp φ 0 z/(freeDiscriminant z-2)-1)*
        ((freeDiscriminant z-2)/(Real.exp |z.im| : ℂ)) := by
    unfold canonicalDiscriminant
    field_simp
    ring
  rw [he, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_freeDiscriminant_sub_two_div_exp_im_le z) (norm_nonneg _)

/-- The additive trace error is little-o of exp(abs(Im z)) outside every fixed free-disc family. -/
theorem tendsto_discriminant_error_div_exp_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun i => (canonicalDiscriminant hp φ (z i)-freeDiscriminant (z i))/
      (Real.exp |(z i).im| : ℂ)) l (𝓝 0) := by
  have ht := tendsto_canonicalEven_div_free_of_separated hp hp1 φ hφ z hescape hr hrπ hsep
  have he : Tendsto (fun i => 4*‖canonicalParityProduct hp φ 0 (z i)/(freeDiscriminant (z i)-2)-1‖)
      l (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using (ht.sub_const 1).norm.const_mul 4
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ he
  exact Eventually.of_forall (fun i => norm_discriminant_error_div_exp_le hp φ (z i)
    (notMem_freeLattice_of_separated hr (hsep i)))

/-- One threshold works for all separated parameters for each fixed potential and tolerance. -/
theorem exists_threshold_discriminant_error_exp (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
      ‖canonicalDiscriminant hp φ z-freeDiscriminant z‖ ≤ ε*Real.exp |z.im| := by
  let S := {z : ℂ // ∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖}
  have ht := tendsto_discriminant_error_div_exp_of_separated hp hp1 φ hφ
    (fun z : S => z.val) tendsto_comap hr hrπ (fun z => z.property)
  have hn := ht.norm
  simp only [norm_zero] at hn
  obtain ⟨R, hR⟩ := exists_threshold_of_eventually_comap_atTop (fun z : S => ‖z.val‖)
    (hn.eventually (gt_mem_nhds hε))
  refine ⟨R, ?_⟩
  intro z hz hsep
  have h := (hR ⟨z, hsep⟩ hz).le
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
  exact (div_le_iff₀ (Real.exp_pos _)).mp h

/-- In particular the discriminant tends to zero along the real free cosine zeros. -/
theorem tendsto_discriminant_freeCosineZero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) :
    Tendsto (fun n => canonicalDiscriminant hp φ (freeCosineZero n)) atTop (𝓝 0) := by
  simpa only [freeDiscriminant_freeCosineZero, sub_zero, freeCosineZero_im, abs_zero,
    Real.exp_zero, Complex.ofReal_one, div_one] using
    tendsto_discriminant_error_div_exp_of_separated hp hp1 φ hφ freeCosineZero
      tendsto_norm_freeCosineZero (by positivity : 0 < Real.pi/4) le_rfl freeCosineZero_separated

end NLS.ZakharovShabat
