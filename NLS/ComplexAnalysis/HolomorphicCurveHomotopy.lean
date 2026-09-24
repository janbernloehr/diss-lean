import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Homotopy invariance of holomorphic line integrals

A holomorphic scalar function defines a closed complex one-form. The
curve-integral homotopy theorem therefore identifies its integrals along
smooth homotopic closed loops, including loops with moving basepoints.
-/

noncomputable section
open Set
open scoped unitInterval

namespace NLS.ComplexAnalysis

/-- The complex one-form associated with a scalar function. -/
def holomorphicOneForm (f : ℂ → ℂ) (z : ℂ) : ℂ →L[ℂ] ℂ :=
  f z • ContinuousLinearMap.id ℂ ℂ

/-- The real Fréchet derivative of the associated one-form when `f` is holomorphic. -/
def holomorphicOneFormDeriv (f : ℂ → ℂ) (z : ℂ) :
    ℂ →L[ℝ] ℂ →L[ℂ] ℂ :=
  ((fderiv ℂ f z).smulRight (ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ

@[simp] theorem holomorphicOneForm_apply (f : ℂ → ℂ) (z v : ℂ) :
    holomorphicOneForm f z v = f z * v := by
  simp [holomorphicOneForm, smul_eq_mul]

private theorem complex_linear_map_eq_mul_one (L : ℂ →L[ℂ] ℂ) (u : ℂ) :
    L u = u * L 1 := by
  calc
    L u = L (u • (1:ℂ)) := by simp
    _ = u • L 1 := map_smul L u 1
    _ = u * L 1 := by simp [smul_eq_mul]

private theorem holomorphicOneForm_hasFDerivAt (f : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℂ f z) :
    HasFDerivAt (holomorphicOneForm f) (holomorphicOneFormDeriv f z) z := by
  exact (hf.hasFDerivAt.smul_const (ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ

private theorem holomorphicOneFormDeriv_symmetric (f : ℂ → ℂ) (z u v : ℂ) :
    holomorphicOneFormDeriv f z u v = holomorphicOneFormDeriv f z v u := by
  change ((fderiv ℂ f z) u) * v = ((fderiv ℂ f z) v) * u
  rw [complex_linear_map_eq_mul_one (fderiv ℂ f z) u,
    complex_linear_map_eq_mul_one (fderiv ℂ f z) v]
  ring

private theorem holomorphicOneForm_continuousOn (f : ℂ → ℂ) (t : Set ℂ)
    (hf : ∀ z ∈ t, DifferentiableAt ℂ f z) :
    ContinuousOn (holomorphicOneForm f) t := by
  intro z hz
  exact ((hf z hz).continuousAt.smul continuousAt_const).continuousWithinAt

/-- For a smooth homotopy of open paths, the difference between the
two path integrals is exactly the difference between the integrals
along its two endpoint traces. -/
theorem curveIntegral_add_sides_eq_of_holomorphic_homotopy
    {a b c d : ℂ} {γ₁ : Path a b} {γ₂ : Path c d}
    (f : ℂ → ℂ)
    (φ : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    {t : Set ℂ}
    (hφt : ∀ s ∈ Ioo (0:I) 1, ∀ u ∈ Ioo (0:I) 1, φ (s, u) ∈ t)
    (hf : ∀ z ∈ closure t, DifferentiableAt ℂ f z)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    (∫ᶜ x in γ₁, holomorphicOneForm f x) +
      ∫ᶜ x in φ.evalAt 1, holomorphicOneForm f x =
    (∫ᶜ x in γ₂, holomorphicOneForm f x) +
      ∫ᶜ x in φ.evalAt 0, holomorphicOneForm f x := by
  have hω (z : ℂ) (hz : z ∈ t) :
      HasFDerivWithinAt (holomorphicOneForm f) (holomorphicOneFormDeriv f z) t z :=
    ((holomorphicOneForm_hasFDerivAt f z (hf z (subset_closure hz))).hasFDerivWithinAt)
  have hc : ContinuousOn (holomorphicOneForm f) (closure t) :=
    holomorphicOneForm_continuousOn f (closure t) hf
  have hs (z : ℂ) (_hz : z ∈ t)
      (u : ℂ) (_hu : u ∈ tangentConeAt ℝ t z)
      (v : ℂ) (_hv : v ∈ tangentConeAt ℝ t z) :
      holomorphicOneFormDeriv f z u v = holomorphicOneFormDeriv f z v u :=
    holomorphicOneFormDeriv_symmetric f z u v
  exact φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    hφt hω hc hs hcontdiff

private theorem homotopy_side_integrals_eq
    {a b : ℂ} {γ₁ : Path a a} {γ₂ : Path b b}
    (f : ℂ → ℂ) (φ : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hloop : ∀ s : I, φ (s, 1) = φ (s, 0)) :
    ∫ᶜ x in φ.evalAt 1, holomorphicOneForm f x =
      ∫ᶜ x in φ.evalAt 0, holomorphicOneForm f x := by
  have h₁ : γ₁ (0:I) = γ₁ 1 := by
    simpa using (hloop 0).symm
  have h₂ : γ₂ (0:I) = γ₂ 1 := by
    simpa using (hloop 1).symm
  have heq : (φ.evalAt 1).cast h₁ h₂ = φ.evalAt 0 := by
    apply Path.ext
    funext s
    exact hloop s
  calc
    ∫ᶜ x in φ.evalAt 1, holomorphicOneForm f x =
        ∫ᶜ x in (φ.evalAt 1).cast h₁ h₂, holomorphicOneForm f x := by simp
    _ = ∫ᶜ x in φ.evalAt 0, holomorphicOneForm f x := by rw [heq]

/-- Holomorphic complex line integrals agree along smooth homotopies of
closed paths when the moving paths avoid the singular set. -/
theorem curveIntegral_eq_of_holomorphic_homotopy
    {a b : ℂ} {γ₁ : Path a a} {γ₂ : Path b b}
    (f : ℂ → ℂ)
    (φ : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hloop : ∀ s : I, φ (s, 1) = φ (s, 0))
    {t : Set ℂ}
    (hφt : ∀ s ∈ Ioo (0:I) 1, ∀ u ∈ Ioo (0:I) 1, φ (s, u) ∈ t)
    (hf : ∀ z ∈ closure t, DifferentiableAt ℂ f z)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, holomorphicOneForm f x =
      ∫ᶜ x in γ₂, holomorphicOneForm f x := by
  have h := curveIntegral_add_sides_eq_of_holomorphic_homotopy
    f φ hφt hf hcontdiff
  have hside := homotopy_side_integrals_eq f φ hloop
  rw [hside] at h
  exact add_right_cancel h

end NLS.ComplexAnalysis
