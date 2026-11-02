import NLS.Fourier.PeriodicFourierLebesgueSpace
import NLS.SequenceSpaces.ConjugateReflection
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Physical conjugation on the original periodic distribution spaces

Conjugation acts on every original smooth periodic test. Its Fourier action
reverses the index, and it preserves the exact norm for every symmetric
weight. In particular every real Sobolev order and both Banach endpoints
are retained, at every positive physical period.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier
namespace SmoothPeriodicTest
variable {L : ℝ}

/-- Pointwise conjugation of an actual smooth periodic test. -/
def conjugate (f : SmoothPeriodicTest L) : SmoothPeriodicTest L :=
  ⟨fun x => star (f x), Complex.conjCLE.contDiff.comp f.smooth,
    fun x => congrArg star (f.periodic x)⟩

@[simp] theorem conjugate_apply (f : SmoothPeriodicTest L) (x : ℝ) :
    conjugate f x = star (f x) := rfl

@[simp] theorem conjugate_conjugate (f : SmoothPeriodicTest L) :
    conjugate (conjugate f) = f := by ext x; simp

@[simp] theorem conjugate_add (f g : SmoothPeriodicTest L) :
    conjugate (f+g) = conjugate f + conjugate g := by ext x; simp

@[simp] theorem conjugate_smul (c : ℂ) (f : SmoothPeriodicTest L) :
    conjugate (c • f) = star c • conjugate f := by ext x; simp

theorem iteratedDeriv_conjugate (f : SmoothPeriodicTest L) (k : ℕ) :
    iteratedDeriv k (conjugate f : ℝ → ℂ) = fun x => star (iteratedDeriv k (f : ℝ → ℂ) x) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iteratedDeriv_succ, ih, deriv.star', iteratedDeriv_succ]

/-- Physical conjugation preserves every seminorm in the original test topology. -/
theorem cNorm_conjugate (hL : L ≠ 0) (N : ℕ) (f : SmoothPeriodicTest L) :
    cNorm hL N (conjugate f) = cNorm hL N f := by
  simp only [cNorm_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [BoundedContinuousFunction.norm_eq_iSup_norm, derivative_apply,
    iteratedDeriv_conjugate, norm_star]

variable [Fact (0 < L)]

@[simp] theorem conjugate_mode (n : ℤ) :
    conjugate (mode n : SmoothPeriodicTest L) = mode (-n) := by
  ext x
  exact (wave_neg n _).symm

namespace Distribution

/-- Conjugation of a distribution on all original smooth periodic tests. -/
def conjugate (u : Distribution L) : Distribution L :=
  let v : SmoothPeriodicTest L →ₗ[ℂ] ℂ :=
    { toFun f := star (u (SmoothPeriodicTest.conjugate f))
      map_add' f g := by simp
      map_smul' c f := by simp }
  { v with
    cont := by
      apply (continuous_iff_finite_order v).mpr
      obtain ⟨N,C,hC,hbound⟩ := (continuous_iff_finite_order u.toLinearMap).mp u.continuous
      refine ⟨N,C,hC,fun f => ?_⟩
      change ‖star (u (SmoothPeriodicTest.conjugate f))‖ ≤ _
      have hb := hbound (SmoothPeriodicTest.conjugate f)
      change ‖u (SmoothPeriodicTest.conjugate f)‖ ≤
        C * cNorm (Fact.out : 0 < L).ne' N (SmoothPeriodicTest.conjugate f) at hb
      simpa only [norm_star, cNorm_conjugate] using hb }

@[simp] theorem conjugate_apply (u : Distribution L) (f : SmoothPeriodicTest L) :
    u.conjugate f = star (u (SmoothPeriodicTest.conjugate f)) := rfl

@[simp] theorem conjugate_conjugate (u : Distribution L) :
    u.conjugate.conjugate = u := by ext f; simp

/-- The normalized Fourier coefficients have the physical index reversal. -/
theorem conjugate_coefficient (u : Distribution L) (n : ℤ) :
    u.conjugate (mode (-n)) = star (u (mode n)) := by simp

/-- Equality with the physical conjugate is characterized by the original coefficients. -/
theorem eq_conjugate_iff_coefficients (u v : Distribution L) :
    v = u.conjugate ↔ ∀ n : ℤ, v (mode (-n)) = star (u (mode n)) := by
  constructor
  · rintro rfl n
    exact conjugate_coefficient u n
  · intro h
    apply ext_coefficients
    intro n
    rw [conjugate_coefficient, h]

end Distribution
end SmoothPeriodicTest

namespace PeriodicFourierLebesgue
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Physical conjugation stays in the original distribution space with a symmetric weight. -/
def conjugate (w : Weight) (hw : ∀ n, w (-n) = w n)
    (u : PeriodicFourierLebesgue L w p) : PeriodicFourierLebesgue L w p :=
  ⟨u.val.conjugate, by
    change Memℓp (fun n => (w n : ℂ) * u.val.conjugate (mode (-n))) p
    have h := (WeightedCoeff.conjugateReflection w hw (coefficientsLM w p u)).property
    change Memℓp (fun n => (w n : ℂ) *
      (WeightedCoeff.conjugateReflection w hw (coefficientsLM w p u)).val n) p at h
    simp only [WeightedCoeff.conjugateReflection_apply] at h
    change Memℓp (fun n => (w n : ℂ) * star (u.val (mode (-(-n))))) p at h
    simpa only [Distribution.conjugate_coefficient, neg_neg] using h⟩

/-- The original test-space operation agrees exactly with coefficient conjugate reflection. -/
theorem coefficientsLM_conjugate (w : Weight) (hw : ∀ n, w (-n) = w n)
    (u : PeriodicFourierLebesgue L w p) :
    coefficientsLM w p (conjugate w hw u) =
      WeightedCoeff.conjugateReflection w hw (coefficientsLM w p u) := by
  apply Subtype.ext
  funext n
  rw [WeightedCoeff.conjugateReflection_apply]
  change u.val.conjugate (mode (-n)) = star (u.val (mode (-(-n))))
  simp only [Distribution.conjugate_coefficient, neg_neg]

/-- No constant is lost in the original weighted Fourier norm, including at infinity. -/
theorem norm_conjugate (w : Weight) (hw : ∀ n, w (-n) = w n)
    (u : PeriodicFourierLebesgue L w p) : ‖conjugate w hw u‖ = ‖u‖ := by
  change ‖coefficientsLM w p (conjugate w hw u)‖ = ‖coefficientsLM w p u‖
  rw [coefficientsLM_conjugate, WeightedCoeff.norm_conjugateReflection]

/-- The real-pair condition holds on the actual native spaces at every Sobolev order. -/
theorem sobolev_real_pair_iff (s : ℝ)
    (u v : FourierLebesgueSpace L s p) :
    v = conjugate (Weight.sobolev s) (Weight.sobolev_neg s) u ↔
      ∀ n : ℤ, (coefficientsLM (Weight.sobolev s) p v).val n =
        star ((coefficientsLM (Weight.sobolev s) p u).val (-n)) := by
  constructor
  · rintro rfl n
    change u.val.conjugate (mode (-n)) = star (u.val (mode (-(-n))))
    simp only [Distribution.conjugate_coefficient, neg_neg]
  · intro h
    apply Subtype.ext
    apply (Distribution.eq_conjugate_iff_coefficients u.val v.val).mpr
    intro n
    have hn := h n
    change v.val (mode (-n)) = star (u.val (mode (-(-n)))) at hn
    simpa only [neg_neg] using hn

end PeriodicFourierLebesgue
end NLS.Fourier
