import NLS.SequenceSpaces.InterpolationFamily
import Mathlib.Analysis.Complex.Hadamard

/-!
# Interpolation of finite kernel pairings

Finite analytic input and test families turn endpoint bounds for a complex
kernel into an intermediate bound. The scalar three-lines theorem is applied
to an explicitly bounded entire function; the constants are uniform in the
finite supports of the inputs.
-/

noncomputable section
open scoped ENNReal
open Complex
namespace NLS.Coeff

/-- A finite bilinear pairing with an arbitrary complex matrix kernel. -/
def kernelPair (K : ℤ → ℤ → ℂ) (a b : ℤ →₀ ℂ) : ℂ :=
  a.sum (fun k x => b.sum (fun n y => x * K n k * y))

/-- Power families can be summed over the original supports, including zero branches. -/
theorem kernelPair_powerFamily (K : ℤ → ℤ → ℂ) (a b : ℤ →₀ ℂ) (u v : ℂ) :
    kernelPair K (powerFamily a u) (powerFamily b v) =
      ∑ k ∈ a.support, ∑ n ∈ b.support, powerCurve (a k) u * K n k * powerCurve (b n) v := by
  unfold kernelPair
  rw [Finsupp.sum_of_support_subset _ (support_powerFamily_subset a u) _ (by simp)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finsupp.sum_of_support_subset _ (support_powerFamily_subset b v) _ (by simp)]
  rfl

/-- The scalar kernel pairing of affine power families is entire. -/
theorem differentiable_kernelPair_powerFamily (K : ℤ → ℤ → ℂ) (a b : ℤ →₀ ℂ)
    (r s p₀ p₁ q₀ q₁ : ℝ) :
    Differentiable ℂ (fun z => kernelPair K
      (powerFamily a (interpolationWeight r p₀ p₁ z))
      (powerFamily b (interpolationWeight s q₀ q₁ z))) := by
  simp only [kernelPair_powerFamily]
  apply Differentiable.fun_sum
  intro k hk
  apply Differentiable.fun_sum
  intro n hn
  have hA := (differentiable_powerCurve (a k)).comp (differentiable_interpolationWeight r p₀ p₁)
  have hB := (differentiable_powerCurve (b n)).comp (differentiable_interpolationWeight s q₀ q₁)
  exact (hA.mul_const (K n k)).mul hB

/-- A support-dependent strip bound is enough for the scalar three-lines theorem. -/
theorem norm_kernelPair_powerFamily_le {r s : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ s)]
    (K : ℤ → ℤ → ℂ) (a b : ℤ →₀ ℂ)
    (ha : ‖ofFinsupp (p := r) a‖ ≤ 1) (hb : ‖ofFinsupp (p := s) b‖ ≤ 1)
    {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    ‖kernelPair K (powerFamily a u) (powerFamily b v)‖ ≤
      ∑ k ∈ a.support, ∑ n ∈ b.support, ‖K n k‖ := by
  rw [kernelPair_powerFamily]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul, norm_mul]
  calc
    _ ≤ 1 * ‖K n k‖ * 1 := by
      gcongr
      · exact norm_powerFamily_apply_le_one a ha hu k
      · exact norm_powerFamily_apply_le_one b hb hv n
    _ = _ := by ring

/-- Endpoint estimates interpolate on normalized finite inputs and tests.

The maximum of the endpoint bounds suffices; no optimal interpolation constant
is asserted here. All six exponents are finite and positive. -/
theorem norm_kernelPair_interpolate_unit
    {p₀ p₁ q₀ q₁ r s : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ s)]
    (hp₀ : 0 < p₀.toReal) (hp₁ : 0 < p₁.toReal)
    (hq₀ : 0 < q₀.toReal) (hq₁ : 0 < q₁.toReal)
    (hr : 0 < r.toReal) (hs : 0 < s.toReal)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hrt : r.toReal * ((1-t)/p₀.toReal + t/p₁.toReal) = 1)
    (hst : s.toReal * ((1-t)/q₀.toReal + t/q₁.toReal) = 1)
    (K : ℤ → ℤ → ℂ) {B₀ B₁ : ℝ} (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (h₀ : ∀ a b : ℤ →₀ ℂ, ‖kernelPair K a b‖ ≤
      B₀ * ‖ofFinsupp (p := p₀) a‖ * ‖ofFinsupp (p := q₀) b‖)
    (h₁ : ∀ a b : ℤ →₀ ℂ, ‖kernelPair K a b‖ ≤
      B₁ * ‖ofFinsupp (p := p₁) a‖ * ‖ofFinsupp (p := q₁) b‖)
    (a b : ℤ →₀ ℂ) (ha : ‖ofFinsupp (p := r) a‖ ≤ 1)
    (hb : ‖ofFinsupp (p := s) b‖ ≤ 1) : ‖kernelPair K a b‖ ≤ max B₀ B₁ := by
  let A := fun z => powerFamily a (interpolationWeight r.toReal p₀.toReal p₁.toReal z)
  let B := fun z => powerFamily b (interpolationWeight s.toReal q₀.toReal q₁.toReal z)
  let F := fun z => kernelPair K (A z) (B z)
  have hd : Differentiable ℂ F := differentiable_kernelPair_powerFamily K a b _ _ _ _ _ _
  have hbound : BddAbove ((norm ∘ F) '' HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨∑ k ∈ a.support, ∑ n ∈ b.support, ‖K n k‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact norm_kernelPair_powerFamily_le K a b ha hb
      (interpolationWeight_re_pos hr hp₀ hp₁ hz.1 hz.2)
      (interpolationWeight_re_pos hs hq₀ hq₁ hz.1 hz.2)
  have he₀ (z : ℂ) (hz : z.re = 0) : ‖F z‖ ≤ max B₀ B₁ := by
    have hA : ‖ofFinsupp (p := p₀) (A z)‖ ≤ 1 :=
      norm_powerFamily_le_one hp₀ hr a ha (by rw [interpolationWeight_re, hz]; ring)
    have hB : ‖ofFinsupp (p := q₀) (B z)‖ ≤ 1 :=
      norm_powerFamily_le_one hq₀ hs b hb (by rw [interpolationWeight_re, hz]; ring)
    exact (h₀ (A z) (B z)).trans (by
      calc
        _ ≤ B₀ * 1 * 1 := by gcongr; exact lp.norm_nonneg' _
        _ ≤ max B₀ B₁ := by simpa only [mul_one] using le_max_left B₀ B₁)
  have he₁ (z : ℂ) (hz : z.re = 1) : ‖F z‖ ≤ max B₀ B₁ := by
    have hA : ‖ofFinsupp (p := p₁) (A z)‖ ≤ 1 :=
      norm_powerFamily_le_one hp₁ hr a ha (by rw [interpolationWeight_re, hz]; ring)
    have hB : ‖ofFinsupp (p := q₁) (B z)‖ ≤ 1 :=
      norm_powerFamily_le_one hq₁ hs b hb (by rw [interpolationWeight_re, hz]; ring)
    exact (h₁ (A z) (B z)).trans (by
      calc
        _ ≤ B₁ * 1 * 1 := by gcongr; exact lp.norm_nonneg' _
        _ ≤ max B₀ B₁ := by simpa only [mul_one] using le_max_right B₀ B₁)
  have hthree := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' F
    (z := (t : ℂ)) ⟨ht₀, ht₁⟩ hd.diffContOnCl hbound
    (fun z hz => he₀ z hz) (fun z hz => he₁ z hz)
  have ht : F (t : ℂ) = kernelPair K a b := by
    dsimp [F, A, B]
    rw [interpolationWeight_at hrt, interpolationWeight_at hst, powerFamily_one, powerFamily_one]
  rw [ht, ofReal_re] at hthree
  have hM : 0 ≤ max B₀ B₁ := hB₀.trans (le_max_left _ _)
  have he : (max B₀ B₁) ^ (1-t) * (max B₀ B₁)^t = max B₀ B₁ := by
    rw [← Real.rpow_add' hM (by linarith : (1-t)+t ≠ 0)]
    simp
  rwa [he] at hthree

end NLS.Coeff
