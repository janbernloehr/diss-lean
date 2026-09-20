import NLS.ZakharovShabat.DiscriminantExteriorError
import NLS.ZakharovShabat.ExteriorCauchyBounds

/-!
# Additive spectral-derivative asymptotics outside the free discs

Cauchy's estimate transfers the fixed-potential additive trace asymptotic to
its derivative. The normalized error is relative to exp(abs(Im z)), so it is
meaningful throughout the exterior, including free cosine zeros.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exact derivative of the free discriminant. -/
theorem hasDerivAt_freeDiscriminant (z : ℂ) :
    HasDerivAt freeDiscriminant (-2*sin z) z := by
  convert! (Complex.hasDerivAt_cos z).const_mul 2 using 1
  ring

/-- The derivative of the additive trace error has the expected free sine term. -/
theorem deriv_discriminant_error (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    deriv (fun w => canonicalDiscriminant hp φ w-freeDiscriminant w) z =
      deriv (canonicalDiscriminant hp φ) z+2*sin z := by
  have h := ((analyticOnNhd_canonicalDiscriminant hp hp1 φ hφ z (mem_univ _)).differentiableAt.hasDerivAt).sub
    (hasDerivAt_freeDiscriminant z)
  change HasDerivAt (fun w => canonicalDiscriminant hp φ w-freeDiscriminant w)
    (deriv (canonicalDiscriminant hp φ) z-(-2*sin z)) z at h
  simpa only [neg_mul, sub_neg_eq_add] using h.deriv

/-- One spectral threshold bounds the derivative error for every separated parameter. -/
theorem exists_threshold_discriminant_derivative_error_exp (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
      ‖deriv (canonicalDiscriminant hp φ) z+2*sin z‖ ≤ ε*Real.exp |z.im| := by
  let η := ε*(r/2)/Real.exp (r/2)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨R, hR⟩ := exists_threshold_discriminant_error_exp hp hp1 φ hφ
    (half_pos hr) (by linarith) hη
  refine ⟨R+r/2, ?_⟩
  intro z hz hsep
  have hf : Differentiable ℂ (fun w => canonicalDiscriminant hp φ w-freeDiscriminant w) := by
    intro w
    exact (analyticOnNhd_canonicalDiscriminant hp hp1 φ hφ w (mem_univ _)).differentiableAt.sub
      (hasDerivAt_freeDiscriminant w).differentiableAt
  have hb := norm_deriv_le_of_exterior_exp_bound hf hr R η hη.le hR z hz hsep
  rw [deriv_discriminant_error hp hp1 φ hφ] at hb
  have he : (η*Real.exp (|z.im|+r/2))/(r/2) = ε*Real.exp |z.im| := by
    rw [Real.exp_add]
    dsimp [η]
    field_simp
  exact hb.trans_eq he

/-- The derivative error divided by exp(abs(Im z)) tends to zero on every escaping separated path. -/
theorem tendsto_discriminant_derivative_error_div_exp_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun i => (deriv (canonicalDiscriminant hp φ) (z i)+2*sin (z i))/
      (Real.exp |(z i).im| : ℂ)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R, hR⟩ := exists_threshold_discriminant_derivative_error_exp hp hp1 φ hφ hr hrπ (half_pos hε)
  filter_upwards [hescape.eventually_ge_atTop R] with i hi
  rw [dist_zero_right, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact ((div_le_iff₀ (Real.exp_pos _)).mpr (hR (z i) hi (hsep i))).trans_lt (half_lt_self hε)

end NLS.ZakharovShabat
