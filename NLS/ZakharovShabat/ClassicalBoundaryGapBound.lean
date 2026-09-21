import NLS.ZakharovShabat.ClassicalRealMonodromy
import NLS.ZakharovShabat.ClassicalBoundaryMonodromy
import NLS.ZakharovShabat.HilbertDiscriminant
import NLS.ZakharovShabat.RealGapCharacterization

/-! # Boundary trace inequalities for the original continuous potential
At a real separated eigenvalue the anti-discriminant square is nonnegative,
so the trace lies outside the open interval from minus two to two. The
comparison with an intrinsic periodic discriminant uses a common physical
representative, keeping the periodic and reflected boundary potentials distinct.
-/

noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

/-- The real trace-square identity at either classical separated root. -/
theorem classicalDiscriminant_re_sq_sub_four_of_separated_zero (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (hΦ : ∀ t, (Φ t).2 = conj (Φ t).1) (x : ℝ)
    (hx : classicalSeparatedCharacteristic b Φ x = 0) :
    (classicalDiscriminant Φ x).re^2-4 = (classicalAntiDiscriminant Φ x).re^2 := by
  have he := congrArg Complex.re (classicalDiscriminant_sq_sub_four_of_separated_zero b Φ x hx)
  simpa only [sub_re,pow_two,mul_re,classicalDiscriminant_im_eq_zero Φ hΦ x,
    classicalAntiDiscriminant_im_eq_zero Φ hΦ x,mul_zero,sub_zero,show (4 : ℂ).re = 4 from rfl] using he

/-- Every real separated root of a real-type continuous potential has trace modulus at least two. -/
theorem two_le_abs_classicalDiscriminant_re_of_separated_zero (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (hΦ : ∀ t, (Φ t).2 = conj (Φ t).1) (x : ℝ)
    (hx : classicalSeparatedCharacteristic b Φ x = 0) : 2 ≤ |(classicalDiscriminant Φ x).re| := by
  have he := classicalDiscriminant_re_sq_sub_four_of_separated_zero b Φ hΦ x hx
  nlinarith [sq_nonneg (classicalAntiDiscriminant Φ x).re,
    sq_abs (classicalDiscriminant Φ x).re,abs_nonneg (classicalDiscriminant Φ x).re]

/-- The trace is strictly beyond two exactly when the anti-discriminant is nonzero. -/
theorem two_lt_abs_classicalDiscriminant_re_iff (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (hΦ : ∀ t, (Φ t).2 = conj (Φ t).1) (x : ℝ)
    (hx : classicalSeparatedCharacteristic b Φ x = 0) :
    2 < |(classicalDiscriminant Φ x).re| ↔ classicalAntiDiscriminant Φ x ≠ 0 := by
  have he := classicalDiscriminant_re_sq_sub_four_of_separated_zero b Φ hΦ x hx
  have hi := classicalAntiDiscriminant_im_eq_zero Φ hΦ x
  have hn : classicalAntiDiscriminant Φ x ≠ 0 ↔ (classicalAntiDiscriminant Φ x).re ≠ 0 := by
    rw [ne_eq,Complex.ext_iff]
    simp only [zero_re,zero_im,hi,and_true]
  rw [hn]
  constructor
  · intro h hzero
    rw [hzero] at he
    nlinarith [sq_abs (classicalDiscriminant Φ x).re]
  · intro h
    have hpos := sq_pos_of_ne_zero h
    nlinarith [sq_abs (classicalDiscriminant Φ x).re,abs_nonneg (classicalDiscriminant Φ x).re]

/-- Equality at the spectral edge is exactly vanishing of the anti-discriminant. -/
theorem abs_classicalDiscriminant_re_eq_two_iff (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (hΦ : ∀ t, (Φ t).2 = conj (Φ t).1) (x : ℝ)
    (hx : classicalSeparatedCharacteristic b Φ x = 0) :
    |(classicalDiscriminant Φ x).re| = 2 ↔ classicalAntiDiscriminant Φ x = 0 := by
  have hl := two_le_abs_classicalDiscriminant_re_of_separated_zero b Φ hΦ x hx
  have hs := two_lt_abs_classicalDiscriminant_re_iff b Φ hΦ x hx
  constructor
  · intro he
    by_contra hn
    have ht := hs.mpr hn
    linarith
  · intro he
    have hn : ¬2 < |(classicalDiscriminant Φ x).re| := fun ht => (hs.mp ht) he
    exact le_antisymm (le_of_not_gt hn) hl

/-- The trace bound applies to eigenvalues defined by the original interval differential equation. -/
theorem two_le_abs_classicalDiscriminant_re_of_classicalEigenvalue (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (hΦ : ∀ t, (Φ t).2 = conj (Φ t).1)
    (hL : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (x : ℝ)
    (hx : (x : ℂ) ∈ b.classicalEigenvalues (extend Φ)) : 2 ≤ |(classicalDiscriminant Φ x).re| :=
  two_le_abs_classicalDiscriminant_re_of_separated_zero b Φ hΦ x
    (classicalSeparatedCharacteristic_eq_zero_of_mem_classicalEigenvalues b Φ hL x hx)

/-- A common physical representative gives the exact original periodic trace identity at a boundary eigenvalue. -/
theorem canonicalDiscriminant_sq_sub_four_of_boundaryEigenvalue
    (b : BoundaryCondition) (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (ψ : PairSpace 2) (hψ : ψ ∈ dirichletSubspace) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hΨ : physicalBase ψ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ)
    (hz : z ∈ b.spectrum (by simp) ψ hψ) :
    (canonicalDiscriminant (by simp) φ z)^2-4 = (classicalAntiDiscriminant Φ z)^2 := by
  rw [canonicalDiscriminant_eq_classical φ hφ Φ hΦ]
  exact classicalDiscriminant_sq_sub_four_of_separated_zero b Φ z
    (classicalSeparatedCharacteristic_eq_zero_of_mem_boundarySpectrum b ψ hψ Φ hΨ z hz)

/-- The original periodic trace satisfies the gap bound at every compatible real boundary eigenvalue. -/
theorem two_le_abs_canonicalDiscriminant_re_of_boundaryEigenvalue
    (b : BoundaryCondition) (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (ψ : PairSpace 2) (hψ : ψ ∈ dirichletSubspace) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hΨ : physicalBase ψ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hr : ∀ t, (Φ t).2 = conj (Φ t).1) (x : ℝ) (hx : (x : ℂ) ∈ b.spectrum (by simp) ψ hψ) :
    2 ≤ |(canonicalDiscriminant (by simp) φ x).re| := by
  rw [canonicalDiscriminant_eq_classical φ hφ Φ hΦ]
  exact two_le_abs_classicalDiscriminant_re_of_separated_zero b Φ hr x
    (classicalSeparatedCharacteristic_eq_zero_of_mem_boundarySpectrum b ψ hψ Φ hΨ x hx)

/-- Each compatible real boundary eigenvalue lies in a gap of the original periodic spectrum. -/
theorem exists_canonicalGap_of_boundaryEigenvalue
    (b : BoundaryCondition) (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ)
    (ψ : PairSpace 2) (hψ : ψ ∈ dirichletSubspace) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hΨ : physicalBase ψ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hr : ∀ t, (Φ t).2 = conj (Φ t).1) (x : ℝ) (hx : (x : ℂ) ∈ b.spectrum (by simp) ψ hψ) :
    ∃ n : ℤ, x ∈ Icc (canonicalPeriodicLeft (by simp) (by norm_num) φ hφ n).re
      (canonicalPeriodicRight (by simp) (by norm_num) φ hφ n).re := by
  apply (two_le_norm_discriminant_iff_mem_canonicalGap (by simp) (by norm_num) φ hφ hreal x).mp
  exact (two_le_abs_canonicalDiscriminant_re_of_boundaryEigenvalue b φ hφ ψ hψ Φ hΦ hΨ hr x hx).trans
    (Complex.abs_re_le_norm _)

end NLS.ZakharovShabat
