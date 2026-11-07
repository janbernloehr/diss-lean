import NLS.SequenceSpaces.WeightedReciprocalDecay
import NLS.SequenceSpaces.WeightedPhaseFlow

/-! Real frequency errors of order 1/n give EXACTLY linear-in-time
one-derivative phase smoothing, with no exponential time factor. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS

theorem norm_real_phase_sub_one_le (x : ℝ) : ‖Complex.exp ((x:ℂ)*I)-1‖≤|x| := by
  rw [mul_comm,Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,abs_mul]
  rw [abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h : |Real.sin (x/2)|≤|x/2| := Real.abs_sin_le_abs
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at h
  nlinarith

theorem norm_real_phase_sub_phase_le (t a b : ℝ) :
    ‖Complex.exp (((t*a:ℝ):ℂ)*I)-Complex.exp (((t*b:ℝ):ℂ)*I)‖≤|t| * |a-b| := by
  have he : Complex.exp (((t*a:ℝ):ℂ)*I)-Complex.exp (((t*b:ℝ):ℂ)*I)=
      Complex.exp (((t*b:ℝ):ℂ)*I)*(Complex.exp (((t*(a-b):ℝ):ℂ)*I)-1) := by
    rw [mul_sub,mul_one,←Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  simpa only [abs_mul] using norm_real_phase_sub_one_le (t*(a-b))

namespace WeightedCoeff

theorem exists_sobolev_real_phase_gain_multiplier {p : ℝ≥0∞} [Fact (1≤p)]
    (r t : ℝ) (ω ω₀ : ℤ → ℝ) (K : ℝ) (hK : 0≤K)
    (hω : ∀ j : ℤ, (1+|(j:ℝ)|) * |ω j-ω₀ j|≤K) :
    ∃ T : WeightedCoeff (Weight.sobolev r) p →L[ℂ] WeightedCoeff (Weight.sobolev (r+1)) p,
      (∀ a j, (T a).val j=(Complex.exp (((t*ω j:ℝ):ℂ)*I)-
        Complex.exp (((t*ω₀ j:ℝ):ℂ)*I))*a.val j) ∧ ‖T‖≤|t| * K := by
  apply exists_sobolev_gain_multiplier r _ (|t| * K) (mul_nonneg (abs_nonneg _) hK)
  intro j
  calc
    _ ≤ (1+|(j:ℝ)|)*(|t| * |ω j-ω₀ j|) := mul_le_mul_of_nonneg_left
      (norm_real_phase_sub_phase_le t (ω j) (ω₀ j)) (by positivity)
    _ = |t| * ((1+|(j:ℝ)|) * |ω j-ω₀ j|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hω j) (abs_nonneg _)

end WeightedCoeff

theorem odd_frequency_bracket_bound_of_positive
    (ω ω₀ : ℤ → ℝ) (hω : ∀ j, ω (-j)= -ω j) (hω₀ : ∀ j, ω₀ (-j)= -ω₀ j)
    (K : ℝ) (hK : 0≤K) (hb : ∀ n : ℕ+, (n:ℝ) * |ω (n:ℤ)-ω₀ (n:ℤ)|≤K) :
    ∀ j : ℤ, (1+|(j:ℝ)|) * |ω j-ω₀ j|≤2*K := by
  have hpos (j : ℤ) (hj : 0<j) : (1+|(j:ℝ)|) * |ω j-ω₀ j|≤2*K := by
    let n : ℕ+ := ⟨j.toNat,by omega⟩
    have he : (n:ℤ)=j := Int.toNat_of_nonneg hj.le
    have h := hb n
    change ((n:ℤ):ℝ) * |ω (n:ℤ)-ω₀ (n:ℤ)|≤K at h
    rw [he] at h
    have hj1 : (1:ℝ)≤j := by exact_mod_cast (show (1:ℤ)≤j by omega)
    rw [abs_of_nonneg (by exact_mod_cast hj.le : (0:ℝ)≤j)]
    have hm := mul_le_mul_of_nonneg_right hj1 (abs_nonneg (ω j-ω₀ j))
    nlinarith
  intro j
  rcases lt_trichotomy 0 j with hj|hj|hj
  · exact hpos j hj
  · subst j
    have hz := hω 0
    have hz₀ := hω₀ 0
    simp only [neg_zero] at hz hz₀
    have he : ω 0=0 := by linarith
    have he₀ : ω₀ 0=0 := by linarith
    simp only [he,he₀,sub_self,abs_zero,mul_zero]
    positivity
  · have h := hpos (-j) (by omega)
    simpa only [Int.cast_neg,abs_neg,hω j,hω₀ j,neg_sub_neg,abs_sub_comm] using h

end NLS
