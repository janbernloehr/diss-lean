import NLS.ZakharovShabat.SourceAngularCollapsedIntegrand
import NLS.ComplexAnalysis.CurveIntegralInteriorCongruence

/-!
# Off-diagonal angular path integrals through collapsed gaps

The removable extension has an integrable one-form on every C¹ path
in its domain. An admissible path's interior avoids the collapsed
point, so its raw canonical-sheet integral equals the extension's
integral. A convex chart supplies a primitive, giving path independence
and zero integrals on loops based at the collapsed endpoint.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Changing the spectral sheet sign negates the actual curve integral,
including when the path has singular endpoints. -/
theorem sourceAngularPathIntegral_neg_sheet (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (Q : ℂ × CoeffPair p → ℂ)
    (ψ : CoeffPair p) {a b : ℂ} (γ : Path a b) :
    sourceAngularPathIntegral n s (fun t => -Q t) ψ γ =
      -sourceAngularPathIntegral n s Q ψ γ := by
  unfold sourceAngularPathIntegral
  have hω : holomorphicOneForm (fun w => sourceAngularIntegrand n s (fun t => -Q t) (w,ψ)) =
      fun z => -holomorphicOneForm (fun w => sourceAngularIntegrand n s Q (w,ψ)) z := by
    funext z
    change sourceAngularIntegrand n s (fun t => -Q t) (z,ψ) • ContinuousLinearMap.id ℂ ℂ =
      -(sourceAngularIntegrand n s Q (z,ψ) • ContinuousLinearMap.id ℂ ℂ)
    rw [sourceAngularIntegrand_neg_sheet]
    exact _root_.neg_smul (sourceAngularIntegrand n s Q (z,ψ)) (ContinuousLinearMap.id ℂ ℂ)
  rw [hω]
  exact curveIntegral_fun_neg (ω := holomorphicOneForm (fun w => sourceAngularIntegrand n s Q (w,ψ)))

theorem sourceAngularCollapsedIntegrand_curveIntegrable
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (T : Set ℂ) (hT : T ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγT : ∀ t : I, γ t ∈ T) :
    CurveIntegrable (holomorphicOneForm (sourceAngularCollapsedIntegrand hp hp1 n m s ψ)) γ := by
  have hf := (sourceAngularCollapsedIntegrand_analyticOnNhd hp hp1 n m s ψ hdata).continuousOn.mono hT
  have hω : ContinuousOn (holomorphicOneForm (sourceAngularCollapsedIntegrand hp hp1 n m s ψ)) T :=
    hf.smul continuousOn_const
  exact hω.curveIntegrable_of_contDiffOn hγ hγT

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual raw quotient is integrable and has the same integral
as its removable extension. Its endpoint values need not agree. -/
theorem angular_collapsed_pathIntegral_eq_extension
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (T : Set ℂ) (hT : T ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγT : ∀ t : I, γ t ∈ T)
    (hdom : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    CurveIntegrable (holomorphicOneForm (fun z =>
      sourceAngularIntegrand n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ))) γ ∧
      sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ =
        ∫ᶜ z in γ, holomorphicOneForm (sourceAngularCollapsedIntegrand hp hp1 n m s ψ) z := by
  let f : ℂ → ℂ := fun z =>
    sourceAngularIntegrand n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)
  let F := sourceAngularCollapsedIntegrand hp hp1 n m s ψ
  have heq : ∀ t ∈ Ioo (0:ℝ) 1, f (γ.extend t) = F (γ.extend t) :=
    fun t ht => hs.angular_collapsed_integrand_eq_canonical ψ hψ n m hmn hgap _ (hdom t ht)
  exact ⟨(curveIntegrable_holomorphicOneForm_congr_interior f F γ heq).mpr
    (sourceAngularCollapsedIntegrand_curveIntegrable hp hp1 n m s ψ hdata T hT γ hγ hγT),
    curveIntegral_holomorphicOneForm_congr_interior f F γ heq⟩

/-- Removing the collapsed point makes the actual off-diagonal
angular integral path independent throughout a convex omitted-root chart. -/
theorem angular_collapsed_pathIntegral_eq_of_convex_paths
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (T : Set ℂ) (hT : T ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hconv : Convex ℝ T) (hopen : IsOpen T)
    {a b : ℂ} (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1)) (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ₁T : ∀ t : I, γ₁ t ∈ T) (hγ₂T : ∀ t : I, γ₂ t ∈ T)
    (hdom₁ : ∀ t ∈ Ioo (0:ℝ) 1, γ₁.extend t ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (hdom₂ : ∀ t ∈ Ioo (0:ℝ) 1, γ₂.extend t ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ₁ =
      sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ₂ := by
  rw [(hs.angular_collapsed_pathIntegral_eq_extension ψ hψ n m hmn hgap hdata T hT
    γ₁ hγ₁ hγ₁T hdom₁).2,
    (hs.angular_collapsed_pathIntegral_eq_extension ψ hψ n m hmn hgap hdata T hT
      γ₂ hγ₂ hγ₂T hdom₂).2]
  apply curveIntegral_eq_of_convex_paths_one _ T hconv hopen
    ((sourceAngularCollapsedIntegrand_analyticOnNhd hp hp1 n m s ψ hdata).mono hT).differentiableOn
    γ₁ γ₂ hγ₁ hγ₂
  · intro t ht
    simpa only [Path.extend_apply γ₁ ht] using hγ₁T ⟨t,ht⟩
  · intro t ht
    simpa only [Path.extend_apply γ₂ ht] using hγ₂T ⟨t,ht⟩
  · exact sourceAngularCollapsedIntegrand_curveIntegrable hp hp1 n m s ψ hdata T hT γ₁ hγ₁ hγ₁T
  · exact sourceAngularCollapsedIntegrand_curveIntegrable hp hp1 n m s ψ hdata T hT γ₂ hγ₂ hγ₂T

/-- A loop from a collapsed endpoint back to itself has zero actual
off-diagonal angular integral, including its singular endpoint values. -/
theorem angular_collapsed_loop_integral_eq_zero
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m)
    (T : Set ℂ) (hT : T ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hconv : Convex ℝ T) (hopen : IsOpen T)
    {a : ℂ} (γ : Path a a) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγT : ∀ t : I, γ t ∈ T)
    (hdom : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceAngularPathIntegral n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) ψ γ = 0 := by
  rw [(hs.angular_collapsed_pathIntegral_eq_extension ψ hψ n m hmn hgap hdata T hT γ hγ hγT hdom).2]
  apply curveIntegral_eq_zero_of_convex_loop_one _ T hconv hopen
    ((sourceAngularCollapsedIntegrand_analyticOnNhd hp hp1 n m s ψ hdata).mono hT).differentiableOn
    γ hγ
  · intro t ht
    simpa only [Path.extend_apply γ ht] using hγT ⟨t,ht⟩
  · exact sourceAngularCollapsedIntegrand_curveIntegrable hp hp1 n m s ψ hdata T hT γ hγ hγT

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
