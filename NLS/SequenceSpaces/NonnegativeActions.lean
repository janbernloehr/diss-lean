import NLS.SequenceSpaces.QuadraticActionLifting
import NLS.SequenceSpaces.RealFormIdentity

/-! # The nonnegative real action locus

Real Birkhoff pairs have nonnegative real actions. Conversely every
nonnegative half-exponent sequence has a real Birkhoff lift. These facts
allow holomorphic uniqueness on action space to be reduced to uniqueness
on the real form of the original coordinate space.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff

/-- Complex sequences whose coordinates are nonnegative real numbers. -/
def nonnegativeLocus (q : ℝ≥0∞) : Set (Coeff q) :=
  {b | ∀ n, (b n).im = 0 ∧ 0 ≤ (b n).re}

@[simp] theorem zero_mem_nonnegativeLocus (q : ℝ≥0∞) : (0 : Coeff q) ∈ nonnegativeLocus q := by
  intro n
  simp

/-- Nonnegative real action sequences form a convex cone. -/
theorem convex_nonnegativeLocus (q : ℝ≥0∞) : Convex ℝ (nonnegativeLocus q) := by
  intro a ha b hb u v hu hv huv n
  change ((u • a n + v • b n).im = 0) ∧ 0 ≤ (u • a n + v • b n).re
  constructor
  · simp [(ha n).1, (hb n).1]
  · simpa using add_nonneg (mul_nonneg hu (ha n).2) (mul_nonneg hv (hb n).2)

/-- A complex square can be nonnegative real only when its root is real. -/
theorem im_eq_zero_of_sq_nonnegative (z : ℂ) (hi : (z^2).im = 0) (hr : 0 ≤ (z^2).re) : z.im = 0 := by
  simp only [pow_two,Complex.mul_im,Complex.mul_re] at hi hr
  by_cases hz : z.re = 0
  · rw [hz] at hr
    nlinarith [sq_nonneg z.im]
  · have he : z.re*z.im = 0 := by nlinarith
    exact (mul_eq_zero.mp he).resolve_left hz

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- The real restriction of the quadratic action map has nonnegative coordinates. -/
theorem quadraticActions_mem_nonnegativeLocus (z : Coeff p × Coeff p) (hz : z ∈ realPairLocus p) :
    quadraticActionsExponent (q := q) z ∈ nonnegativeLocus q := by
  intro n
  constructor
  · simp [quadraticActionsExponent_apply,pow_two,hz.1 n,hz.2 n]
  · simp [quadraticActionsExponent_apply,pow_two,hz.1 n,hz.2 n]
    nlinarith [sq_nonneg (z.1 n).re,sq_nonneg (z.2 n).re]

/-- Every nonnegative action sequence has a real lift, including arbitrary
infinite zero sets. The second coordinate can be chosen identically zero. -/
theorem exists_real_quadraticActions_lift (hp : p ≠ ⊤) (b : Coeff q) (hb : b ∈ nonnegativeLocus q) :
    ∃ z : Coeff p × Coeff p, z ∈ realPairLocus p ∧ quadraticActionsExponent z = b ∧ z.2 = 0 := by
  obtain ⟨w,hw⟩ := square_surjective (p := p) (q := q) hp ((2 : ℂ) • b)
  have hs (n : ℤ) : w n^2 = 2*b n := by
    have he := congrArg (fun a : Coeff q => a n) hw
    simpa only [square_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul] using he
  have hr : ∀ n, (w n).im = 0 := by
    intro n
    apply im_eq_zero_of_sq_nonnegative
    · rw [hs]
      simp [(hb n).1]
    · rw [hs]
      simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hb n).2
  refine ⟨(w,0),⟨hr,?_⟩,?_,rfl⟩
  · intro n
    simp
  · ext n
    rw [quadraticActionsExponent_apply]
    change (w n^2+0^2)/2 = b n
    rw [hs]
    ring

/-- The nonnegative action locus is exactly the image of the real form. -/
theorem quadraticActions_image_realPairLocus (hp : p ≠ ⊤) :
    quadraticActionsExponent (p := p) (q := q) '' realPairLocus p = nonnegativeLocus q := by
  apply Subset.antisymm
  · rintro _ ⟨z,hz,rfl⟩
    exact quadraticActions_mem_nonnegativeLocus z hz
  · intro b hb
    obtain ⟨z,hz,he,_⟩ := exists_real_quadraticActions_lift hp b hb
    exact ⟨z,hz,he⟩

end NLS.Coeff
