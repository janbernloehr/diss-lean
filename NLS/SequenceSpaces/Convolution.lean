import NLS.SequenceSpaces.Translation
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The `lp × l1 → lp` convolution estimate

Convolution is constructed as an absolutely summable series in the Banach space
`Coeff p`. This simultaneously establishes membership and the norm bound, with
no need to infer norm convergence from coordinatewise convergence.
-/

open scoped ENNReal
noncomputable section

namespace NLS.Coeff

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Absolute summability of the series of translated coefficients. -/
theorem summable_norm_convolution_terms (a : Coeff p) (b : Coeff 1) :
    Summable (fun k : ℤ => ‖b k • shift k a‖) := by
  simpa only [norm_smul, norm_shift] using
    ((lp.memℓp b).norm.summable_of_one.mul_right ‖a‖)

theorem summable_convolution_terms (a : Coeff p) (b : Coeff 1) :
    Summable (fun k : ℤ => b k • shift k a) :=
  (summable_norm_convolution_terms a b).of_norm

/-- Discrete convolution with an absolutely summable sequence. -/
def convolution (a : Coeff p) (b : Coeff 1) : Coeff p :=
  ∑' k : ℤ, b k • shift k a

/-- The Banach-space definition agrees with the usual coefficient formula. -/
theorem convolution_apply (a : Coeff p) (b : Coeff 1) (n : ℤ) :
    convolution a b n = ∑' k : ℤ, a (n - k) * b k := by
  change (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n) (∑' k : ℤ, b k • shift k a) = _
  rw [ContinuousLinearMap.map_tsum _ (summable_convolution_terms a b)]
  congr 1
  funext k
  change b k * a (n - k) = a (n - k) * b k
  exact mul_comm _ _

/-- Young's inequality with an `l1` factor, including the `p = ∞` endpoint. -/
theorem norm_convolution_le (a : Coeff p) (b : Coeff 1) :
    ‖convolution a b‖ ≤ ‖a‖ * ‖b‖ := by
  calc
    ‖convolution a b‖ ≤ ∑' k : ℤ, ‖b k • shift k a‖ :=
      norm_tsum_le_tsum_norm (summable_norm_convolution_terms a b)
    _ = (∑' k : ℤ, ‖b k‖) * ‖a‖ := by
      simp only [norm_smul, norm_shift, tsum_mul_right]
    _ = ‖a‖ * ‖b‖ := by
      have hb : ∑' k : ℤ, ‖b k‖ = ‖b‖ := by
        simpa using (lp.hasSum_norm (p := 1) (by simp) b).tsum_eq
      rw [hb, mul_comm]

theorem convolution_add_left (a a' : Coeff p) (b : Coeff 1) :
    convolution (a + a') b = convolution a b + convolution a' b := by
  simp only [convolution, map_add, smul_add]
  exact (summable_convolution_terms a b).tsum_add (summable_convolution_terms a' b)

theorem convolution_add_right (a : Coeff p) (b b' : Coeff 1) :
    convolution a (b + b') = convolution a b + convolution a b' := by
  simp only [convolution, lp.coeFn_add, Pi.add_apply, add_smul]
  exact (summable_convolution_terms a b).tsum_add (summable_convolution_terms a b')

theorem convolution_smul_left (c : ℂ) (a : Coeff p) (b : Coeff 1) :
    convolution (c • a) b = c • convolution a b := by
  simp only [convolution, map_smul, smul_comm (b _) c]
  exact (summable_convolution_terms a b).tsum_const_smul c

theorem convolution_smul_right (c : ℂ) (a : Coeff p) (b : Coeff 1) :
    convolution a (c • b) = c • convolution a b := by
  change (∑' k : ℤ, (c * b k) • shift k a) = c • ∑' k : ℤ, b k • shift k a
  simpa only [smul_smul] using (summable_convolution_terms a b).tsum_const_smul c

/-- The underlying bilinear convolution map. -/
def convolutionLinear : Coeff p →ₗ[ℂ] Coeff 1 →ₗ[ℂ] Coeff p :=
  LinearMap.mk₂ ℂ (convolution (p := p)) convolution_add_left convolution_smul_left
    convolution_add_right convolution_smul_right

/-- Convolution as a continuous bilinear map. -/
def convolutionCLM : Coeff p →L[ℂ] Coeff 1 →L[ℂ] Coeff p :=
  (convolutionLinear (p := p)).mkContinuous₂ 1
    (fun a b => by
      simpa only [one_mul, convolutionLinear, LinearMap.mk₂_apply] using norm_convolution_le a b)

@[simp]
theorem convolutionCLM_apply (a : Coeff p) (b : Coeff 1) :
    convolutionCLM a b = convolution a b := rfl

/-- A single Fourier mode in the right factor produces the corresponding shift. -/
theorem convolution_single_right (a : Coeff p) (k : ℤ) (c : ℂ) :
    convolution a (lp.single 1 k c) = c • shift k a := by
  simp [convolution, lp.single_apply, Pi.single_apply]

end NLS.Coeff
