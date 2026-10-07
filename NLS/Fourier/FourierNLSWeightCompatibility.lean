import NLS.Fourier.FourierNLSUniqueness

/-! # Compatibility of local NLS solutions across weighted spaces

Weight inclusions preserve the free flow, the literal cubic coefficients,
and the trajectory predicate. Uniqueness in the unit-weight space then
identifies solutions constructed in any two spectral weights on their common
interval. No ordering between those two weights is required.
-/
noncomputable section
open Set
namespace NLS.Fourier

/-- Forgetting part of a weight commutes with the free Schrödinger group. -/
theorem inclusion_nlsFreeFlow (w v : SpectralWeight) (h : ∀ n, v n ≤ w n)
    (time : ℝ) (a : WeightedCoeff w.toWeight 1) :
    WeightedCoeff.inclusionCLM w.toWeight v.toWeight h (nlsFreeFlow w.toWeight time a) =
      nlsFreeFlow v.toWeight time (WeightedCoeff.inclusionCLM w.toWeight v.toWeight h a) := by
  apply Subtype.ext
  funext n
  simp only [WeightedCoeff.inclusionCLM_apply,nlsFreeFlow_apply]

/-- The cubic field is coefficient-identical under every dominated weight inclusion. -/
theorem inclusion_cubicNLS (w v : SpectralWeight) (h : ∀ n, v n ≤ w n)
    (a : WeightedCoeff w.toWeight 1) :
    WeightedCoeff.inclusionCLM w.toWeight v.toWeight h (cubicNLS w a) =
      cubicNLS v (WeightedCoeff.inclusionCLM w.toWeight v.toWeight h a) := by
  apply Subtype.ext
  funext n
  simp only [WeightedCoeff.inclusionCLM_apply,cubicNLS_apply]

/-- The strong interaction fields commute with the same bounded inclusion. -/
theorem inclusion_nlsInteraction (w v : SpectralWeight) (h : ∀ n, v n ≤ w n)
    (time : ℝ) (a : WeightedCoeff w.toWeight 1) :
    WeightedCoeff.inclusionCLM w.toWeight v.toWeight h (nlsInteraction w time a) =
      nlsInteraction v time (WeightedCoeff.inclusionCLM w.toWeight v.toWeight h a) := by
  unfold nlsInteraction
  rw [inclusion_nlsFreeFlow,inclusion_cubicNLS,inclusion_nlsFreeFlow]

/-- Every solution in a stronger weight is a solution in a dominated weight. -/
theorem IsFourierNLSTrajectoryOn.inclusion
    {w : SpectralWeight} {a b : ℝ} {u : ℝ → WeightedCoeff w.toWeight 1}
    (hu : IsFourierNLSTrajectoryOn w a b u) (v : SpectralWeight) (h : ∀ n, v n ≤ w n) :
    IsFourierNLSTrajectoryOn v a b
      (fun time => WeightedCoeff.inclusionCLM w.toWeight v.toWeight h (u time)) := by
  refine ⟨(WeightedCoeff.inclusionCLM w.toWeight v.toWeight h).continuous.comp_continuousOn hu.continuous,?_⟩
  intro time ht n
  simpa only [← inclusion_cubicNLS,WeightedCoeff.inclusionCLM_apply] using hu.equation time ht n

/-- Solutions in any two weights with the same original coefficients at an
interior time have identical coefficients throughout the whole closed interval. -/
theorem IsFourierNLSTrajectoryOn.eq_coefficients_of_eq_at
    {w v : SpectralWeight} {a b : ℝ}
    {u : ℝ → WeightedCoeff w.toWeight 1} {z : ℝ → WeightedCoeff v.toWeight 1}
    (hu : IsFourierNLSTrajectoryOn w a b u) (hz : IsFourierNLSTrajectoryOn v a b z)
    (initial : ℝ) (hi : initial ∈ Ioo a b) (hinit : ∀ n : ℤ, (u initial).val n = (z initial).val n) :
    ∀ time ∈ Icc a b, ∀ n : ℤ, (u time).val n = (z time).val n := by
  have hw : ∀ n, SpectralWeight.one n ≤ w n := fun n => w.one_le n
  have hv : ∀ n, SpectralWeight.one n ≤ v n := fun n => v.one_le n
  let L := WeightedCoeff.inclusionCLM (p := 1) w.toWeight SpectralWeight.one.toWeight hw
  let M := WeightedCoeff.inclusionCLM (p := 1) v.toWeight SpectralWeight.one.toWeight hv
  have hzero : L (u initial) = M (z initial) := by
    apply Subtype.ext
    funext n
    simpa only [L,M,WeightedCoeff.inclusionCLM_apply] using hinit n
  have he := (hu.inclusion SpectralWeight.one hw).eqOn_of_eq_at
    (hz.inclusion SpectralWeight.one hv) initial hi hzero
  intro time ht n
  have h := congrArg (fun x : WeightedCoeff SpectralWeight.one.toWeight 1 => x.val n) (he ht)
  simpa only [WeightedCoeff.inclusionCLM_apply] using h

/-- Independently constructed solutions agree on an overlap containing the
common initial time in its interior, even when their weights are incomparable. -/
theorem IsFourierNLSTrajectoryOn.eq_coefficients_on_overlap
    {w v : SpectralWeight} {a b c d : ℝ}
    {u : ℝ → WeightedCoeff w.toWeight 1} {z : ℝ → WeightedCoeff v.toWeight 1}
    (hu : IsFourierNLSTrajectoryOn w a b u) (hz : IsFourierNLSTrajectoryOn v c d z)
    (initial : ℝ) (hi : initial ∈ Ioo (max a c) (min b d))
    (hinit : ∀ n : ℤ, (u initial).val n = (z initial).val n) :
    ∀ time ∈ Icc (max a c) (min b d), ∀ n : ℤ, (u time).val n = (z time).val n :=
  (hu.restrict (le_max_left _ _) (min_le_left _ _)).eq_coefficients_of_eq_at
    (hz.restrict (le_max_right _ _) (min_le_right _ _)) initial hi hinit

end NLS.Fourier
