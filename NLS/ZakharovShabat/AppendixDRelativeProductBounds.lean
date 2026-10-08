import NLS.ZakharovShabat.AppendixDRelativeProductSup

/-! # Lemma D.6: constants uniform on norm balls

The usual p-power bound and the printed linear-norm bound both follow
from a constant chosen before the reference displacement and perturbation.
-/
noncomputable section
open scoped ENNReal
open NLS.Fourier
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A positive constant for the product error on a perturbation norm ball. -/
def appendixDRelativeProductConstant (hp1 : 1 < p) (hp : p ≠ ⊤) (c B A : ℝ) : ℝ :=
  1+Real.pi⁻¹*(hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)+
    c*B*‖hilbertSquareCoeffs‖+
    Real.exp ((c/2)*absoluteSampledRowConstant hp*A)*
      ((c/2)*absoluteSampledRowConstant hp)^2*A

/-- The raw bound is at most a fixed constant times the actual input norm. -/
theorem appendixDRelativeProductBound_le (hp1 : 1 < p) (hp : p ≠ ⊤)
    {c B A x : ℝ} (hc : 0 < c) (_hB : 0 ≤ B) (hx : 0 ≤ x) (hxA : x ≤ A) :
    appendixDRelativeProductBound hp1 hp c B x ≤
      appendixDRelativeProductConstant hp1 hp c B A*x := by
  let D := (c/2)*absoluteSampledRowConstant hp
  have hD : 0 ≤ D := mul_nonneg (by positivity) (absoluteSampledRowConstant_nonneg hp)
  have he : Real.exp (D*x) ≤ Real.exp (D*A) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxA hD)
  have hx2 : x^2 ≤ A*x := by nlinarith
  have hrem : Real.exp (D*x)*(D*x)^2 ≤ Real.exp (D*A)*D^2*A*x := by
    calc
      _ = Real.exp (D*x)*D^2*x^2 := by ring
      _ ≤ Real.exp (D*A)*D^2*(A*x) :=
        mul_le_mul (mul_le_mul_of_nonneg_right he (sq_nonneg D)) hx2
          (sq_nonneg x) (by positivity)
      _ = _ := by ring
  unfold appendixDRelativeProductBound appendixDRelativeProductConstant
  change _ ≤ (1+_+_+Real.exp (D*A)*D^2*A)*x
  change (_+_)*x+Real.exp (D*x)*(D*x)^2 ≤ _
  nlinarith

/-- The constant is strictly positive, including at the zero perturbation. -/
theorem appendixDRelativeProductConstant_pos (hp1 : 1 < p) (hp : p ≠ ⊤)
    {c B A : ℝ} (hc : 0 < c) (hB : 0 ≤ B) (hA : 0 ≤ A) :
    0 < appendixDRelativeProductConstant hp1 hp c B A := by
  have hH := hilbertTransformBound_nonneg hp1 hp
  unfold appendixDRelativeProductConstant
  positivity

/-- Uniform bounds for the least disc majorant, with a constant fixed on both norm balls. -/
theorem exists_appendixDRelativeProductSup_normBall (hp1 : 1 < p) (hp : p ≠ ⊤)
    {c B A : ℝ} (hc : 0 < c) (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : Coeff ⊤) (a : Coeff p) (N : ℕ),
      ‖r‖ ≤ B → ‖a‖ ≤ A → AppendixDReferenceSeparated r c N →
      ∃ b : Coeff p,
        (∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ refinedResonantDisk n,
          ‖appendixDRelativeProductError r a n z‖ ≤ ‖b n‖) ∧
        (∀ n : ℤ, N ≤ n.natAbs → ∀ t : ℝ, 0 ≤ t →
          (∀ z ∈ refinedResonantDisk n, ‖appendixDRelativeProductError r a n z‖ ≤ t) →
          ‖b n‖ ≤ t) ∧
        (∀ n : ℤ, ¬N ≤ n.natAbs → b n = 0) ∧ ‖b‖ ≤ C*‖a‖ := by
  refine ⟨_,appendixDRelativeProductConstant_pos hp1 hp hc hB hA,?_⟩
  intro r a N hr ha hsep
  obtain ⟨b,hmajor,hmin,hzero,hb⟩ := exists_appendixDRelativeProductSup hp1 hp r a hc hB hr hsep
  exact ⟨b,hmajor,hmin,hzero,hb.trans
    (appendixDRelativeProductBound_le hp1 hp hc hB (norm_nonneg a) ha)⟩

/-- On a norm ball, the p-power estimate implies the source's literal linear-norm estimate. -/
private theorem rpow_le_ball_linear {x A q : ℝ} (hx : 0 ≤ x) (hxA : x ≤ A)
    (hq : 1 ≤ q) : x^q ≤ (1+A^q)*x := by
  by_cases hx1 : x ≤ 1
  · have h := Real.rpow_le_rpow_of_exponent_ge' hx hx1 (by norm_num : (0:ℝ) ≤ 1) hq
    rw [Real.rpow_one] at h
    exact h.trans (by nlinarith [Real.rpow_nonneg (hx.trans hxA) q])
  · have hx1' : 1 ≤ x := le_of_lt (lt_of_not_ge hx1)
    have h := Real.rpow_le_rpow hx hxA (by linarith : 0 ≤ q)
    exact h.trans (by nlinarith [Real.rpow_nonneg (hx.trans hxA) q])

/-- Both versions of the powered-supremum bound hold uniformly on norm balls.
The second right side is linear in the input norm, exactly as printed in D.6. -/
theorem appendixDRelativeProductPowerSup_normBall (hp1 : 1 < p) (hp : p ≠ ⊤)
    {c B A : ℝ} (hc : 0 < c) (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧
      ∀ (r : Coeff ⊤) (a : Coeff p) (N : ℕ),
      ‖r‖ ≤ B → ‖a‖ ≤ A → AppendixDReferenceSeparated r c N →
      Summable (appendixDRelativeProductPowerSup r a N) ∧
      (∑' n : ℤ, appendixDRelativeProductPowerSup r a N n) ≤ C*‖a‖^p.toReal ∧
      (∑' n : ℤ, appendixDRelativeProductPowerSup r a N n) ≤ L*‖a‖ := by
  let K := appendixDRelativeProductConstant hp1 hp c B A
  have hK : 0 < K := appendixDRelativeProductConstant_pos hp1 hp hc hB hA
  have hpR : 1 ≤ p.toReal := by
    exact_mod_cast (ENNReal.toReal_mono hp (Fact.out : (1:ℝ≥0∞) ≤ p))
  refine ⟨K^p.toReal, K^p.toReal*(1+A^p.toReal), by positivity, by positivity, ?_⟩
  intro r a N hr ha hsep
  obtain ⟨hs,hbound⟩ := appendixDRelativeProductPowerSup_bound hp1 hp r a hc hB hr hsep
  have hraw : 0 ≤ appendixDRelativeProductBound hp1 hp c B ‖a‖ := by
    have hH := hilbertTransformBound_nonneg hp1 hp
    unfold appendixDRelativeProductBound
    positivity
  have hpow : (∑' n : ℤ, appendixDRelativeProductPowerSup r a N n) ≤ K^p.toReal*‖a‖^p.toReal := by
    apply hbound.trans
    rw [← Real.mul_rpow hK.le (norm_nonneg a)]
    exact Real.rpow_le_rpow hraw
      (appendixDRelativeProductBound_le hp1 hp hc hB (norm_nonneg a) ha) (by linarith)
  refine ⟨hs,hpow,hpow.trans ?_⟩
  calc
    K^p.toReal*‖a‖^p.toReal ≤ K^p.toReal*((1+A^p.toReal)*‖a‖) :=
      mul_le_mul_of_nonneg_left (rpow_le_ball_linear (norm_nonneg a) ha hpR) (by positivity)
    _ = _ := by ring

end NLS.ZakharovShabat
