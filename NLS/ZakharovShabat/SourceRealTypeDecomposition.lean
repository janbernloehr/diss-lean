import NLS.ZakharovShabat.SourceRealTypeConvex
import NLS.SequenceSpaces.Reflection

/-!
# Splitting complex source perturbations into real-type parts

Physical conjugation exchanges the two Fourier components and reverses
frequency. Its fixed points are precisely the real-type sources. Every
complex source is the sum of two real-type sources, with the second
multiplied by `I`; both parts are norm controlled.
-/

noncomputable section
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem sourcePair_ext {u v : CoeffPair p}
    (h₁ : ∀ n : ℤ, u.fst n = v.fst n)
    (h₂ : ∀ n : ℤ, u.snd n = v.snd n) : u = v := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext
  · change u.fst = v.fst
    ext n
    exact h₁ n
  · change u.snd = v.snd
    ext n
    exact h₂ n

/-- Physical conjugation on unweighted source coefficient pairs. -/
def sourceConjugation (u : CoeffPair p) : CoeffPair p :=
  (CoeffPair.toMax p).symm
    (star (Coeff.reflection u.snd), star (Coeff.reflection u.fst))

@[simp] theorem sourceConjugation_fst (u : CoeffPair p) (n : ℤ) :
    (sourceConjugation u).fst n = conj (u.snd (-n)) := by
  simp [sourceConjugation, lp.star_apply]

@[simp] theorem sourceConjugation_snd (u : CoeffPair p) (n : ℤ) :
    (sourceConjugation u).snd n = conj (u.fst (-n)) := by
  simp [sourceConjugation, lp.star_apply]

@[simp] theorem sourceConjugation_involutive (u : CoeffPair p) :
    sourceConjugation (sourceConjugation u) = u := by
  apply sourcePair_ext <;> intro n <;> simp

theorem sourceConjugation_add (u v : CoeffPair p) :
    sourceConjugation (u + v) = sourceConjugation u + sourceConjugation v := by
  apply sourcePair_ext <;> intro n <;> simp

theorem sourceConjugation_smul (z : ℂ) (u : CoeffPair p) :
    sourceConjugation (z • u) = (conj z) • sourceConjugation u := by
  apply sourcePair_ext <;> intro n <;> simp [map_mul]

theorem sourceConjugation_sub (u v : CoeffPair p) :
    sourceConjugation (u - v) = sourceConjugation u - sourceConjugation v := by
  apply sourcePair_ext <;> intro n <;> simp

theorem sourceConjugation_fixed_iff (u : CoeffPair p) :
    sourceConjugation u = u ↔ IsRealType (CoeffPair.toMax p u) := by
  constructor
  · intro h n
    simpa using congrArg (fun v : CoeffPair p => v.snd n) h |>.symm
  · intro h
    apply sourcePair_ext
    · intro n
      exact (IsRealType.fst_eq (CoeffPair.toMax p u) h n).symm
    · intro n
      exact (h n).symm

@[simp] theorem norm_sourceConjugation (hp : p ≠ ⊤) (u : CoeffPair p) :
    ‖sourceConjugation u‖ = ‖u‖ := by
  rw [CoeffPair.norm_eq_tsum_rpow hp, CoeffPair.norm_eq_tsum_rpow hp]
  simp only [sourceConjugation_fst, sourceConjugation_snd, Complex.norm_conj]
  rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ =>
    ‖u.snd (-n)‖ ^ p.toReal + ‖u.fst (-n)‖ ^ p.toReal)]
  congr 1
  apply tsum_congr
  intro n
  simp only [Equiv.neg_apply, neg_neg]
  exact add_comm _ _

/-- The real-type part of a complex source perturbation. -/
def sourceRealPart (u : CoeffPair p) : CoeffPair p :=
  ((1 / 2 : ℂ)) • (u + sourceConjugation u)

/-- The imaginary-type part, represented as a real-type source. -/
def sourceImagPart (u : CoeffPair p) : CoeffPair p :=
  ((Complex.I / 2 : ℂ)) • (sourceConjugation u - u)

theorem sourceRealPart_fixed (u : CoeffPair p) :
    sourceConjugation (sourceRealPart u) = sourceRealPart u := by
  rw [sourceRealPart, sourceConjugation_smul, sourceConjugation_add,
    sourceConjugation_involutive]
  simp only [map_div₀, map_one, map_ofNat]
  module

theorem sourceImagPart_fixed (u : CoeffPair p) :
    sourceConjugation (sourceImagPart u) = sourceImagPart u := by
  rw [sourceImagPart, sourceConjugation_smul, sourceConjugation_sub,
    sourceConjugation_involutive]
  simp only [map_div₀, Complex.conj_I, map_ofNat]
  module

theorem sourceRealPart_realType (u : CoeffPair p) :
    IsRealType (CoeffPair.toMax p (sourceRealPart u)) :=
  (sourceConjugation_fixed_iff _).mp (sourceRealPart_fixed u)

theorem sourceImagPart_realType (u : CoeffPair p) :
    IsRealType (CoeffPair.toMax p (sourceImagPart u)) :=
  (sourceConjugation_fixed_iff _).mp (sourceImagPart_fixed u)

/-- Every complex source is the sum of two real-type sources. -/
theorem sourceRealPart_add_I_smul_sourceImagPart (u : CoeffPair p) :
    sourceRealPart u + Complex.I • sourceImagPart u = u := by
  have hI : Complex.I * (Complex.I / 2) = -(1 / 2 : ℂ) := by
    rw [div_eq_mul_inv, ← mul_assoc, ← pow_two, Complex.I_sq]
    ring
  simp only [sourceRealPart, sourceImagPart, smul_smul]
  rw [hI]
  module

theorem norm_sourceRealPart_le (hp : p ≠ ⊤) (u : CoeffPair p) :
    ‖sourceRealPart u‖ ≤ ‖u‖ := by
  calc
    ‖sourceRealPart u‖ = (1 / 2 : ℝ) * ‖u + sourceConjugation u‖ := by
      change ‖(1 / 2 : ℂ) • (u + sourceConjugation u)‖ = _
      rw [norm_smul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * (‖u‖ + ‖sourceConjugation u‖) := by
      gcongr
      exact norm_add_le _ _
    _ = ‖u‖ := by rw [norm_sourceConjugation hp]; ring

theorem norm_sourceImagPart_le (hp : p ≠ ⊤) (u : CoeffPair p) :
    ‖sourceImagPart u‖ ≤ ‖u‖ := by
  calc
    ‖sourceImagPart u‖ = (1 / 2 : ℝ) * ‖sourceConjugation u - u‖ := by
      change ‖(Complex.I / 2 : ℂ) • (sourceConjugation u - u)‖ = _
      rw [norm_smul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * (‖sourceConjugation u‖ + ‖u‖) := by
      gcongr
      exact norm_sub_le _ _
    _ = ‖u‖ := by rw [norm_sourceConjugation hp]; ring

end NLS.ZakharovShabat
