import NLS.ZakharovShabat.SourceCriticalRootRatioOpenPathHomotopy
import NLS.ComplexAnalysis.ContinuousSmoothLoopHomotopy
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Continuous deformations of smooth open quotient paths

The quotient integral is locally constant in the uniform topology on
twice-smooth open paths with fixed endpoints and image in the root
domain. Consequently a continuous family of such paths preserves the
integral even without joint differentiability of its homotopy square.
-/

noncomputable section
open Set Metric Complex Filter
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A smooth open path in the root domain has a uniform neighborhood
of smooth paths with the same endpoints and the same quotient integral. -/
theorem exists_sourceCriticalRootRatio_openPathIntegral_eq_of_uniform_perturbation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 2 γ.extend (Icc 0 1))
    (hγdom : ∀ u : I, γ u ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : Path a b,
      ContDiffOn ℝ 2 η.extend (Icc 0 1) →
      (∀ u : I, dist (η u) (γ u) ≤ δ) →
      (∫ᶜ z in η, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z) =
        ∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z := by
  let Ω := sourceCanonicalRootDomain hp hp1 ψ
  have hK : IsCompact (range γ) := isCompact_range (map_continuous γ)
  have hKΩ : range γ ⊆ Ω := by
    rintro z ⟨u,rfl⟩
    exact hγdom u
  obtain ⟨ε,hε,hthick⟩ := hK.exists_thickening_subset_open
    (isOpen_sourceCanonicalRootDomain_of_realType hp hp1 ψ hreal) hKΩ
  refine ⟨ε/2,half_pos hε,?_⟩
  intro η hη hclose
  let H := ContinuousMap.Homotopy.affine (γ : C(I,ℂ)) (η : C(I,ℂ))
  have hHΩ : range H ⊆ Ω := by
    rintro z ⟨⟨s,u⟩,rfl⟩
    have hdist : dist (H (s,u)) (γ u) ≤ ε/2 := by
      rw [ContinuousMap.Homotopy.affine_apply]
      change dist (AffineMap.lineMap (γ u) (η u) (s:ℝ)) (γ u) ≤ ε/2
      rw [dist_lineMap_left]
      have hs0 : 0 ≤ (s:ℝ) := s.property.1
      have hs1 : (s:ℝ) ≤ 1 := s.property.2
      rw [Real.norm_eq_abs, abs_of_nonneg hs0]
      have hεs : (s:ℝ)*(ε/2) ≤ ε/2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (half_pos hε).le]
      have hc : dist (γ u) (η u) ≤ ε/2 := by
        simpa only [dist_comm] using hclose u
      exact (mul_le_mul_of_nonneg_left hc hs0).trans hεs
    apply hthick
    exact mem_thickening_iff.mpr
      ⟨γ u,⟨u,rfl⟩,lt_of_le_of_lt hdist (half_lt_self hε)⟩
  have hends (s : I) : H (s,0) = a ∧ H (s,1) = b := by
    simp [H, ContinuousMap.Homotopy.affine_apply]
  exact (sourceCriticalRootRatio_openPathIntegral_eq_of_homotopy_range
    hp hp1 ψ H hends hHΩ
      (NLS.ComplexAnalysis.affineHomotopy_contDiffOn hγ hη)).symm

/-- The open path at time `s` in a homotopy that fixes both endpoints. -/
def sourceHomotopyPath
    {a b : ℂ} {γ₁ γ₂ : Path a b}
    (H : (γ₁ : C(I,ℂ)).Homotopy γ₂)
    (hends : ∀ s : I, H (s,0) = a ∧ H (s,1) = b)
    (s : I) : Path a b where
  toFun := H.toContinuousMap.curry s
  source' := (hends s).1
  target' := (hends s).2

@[simp] theorem sourceHomotopyPath_apply
    {a b : ℂ} {γ₁ γ₂ : Path a b}
    (H : (γ₁ : C(I,ℂ)).Homotopy γ₂)
    (hends : ∀ s : I, H (s,0) = a ∧ H (s,1) = b)
    (s u : I) : sourceHomotopyPath H hends s u = H (s,u) := rfl

/-- A continuous fixed-endpoint homotopy of twice-smooth paths in the
root domain preserves the critical-root quotient integral. -/
theorem sourceCriticalRootRatio_openPathIntegral_eq_of_continuous_smooth_homotopy
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {a b : ℂ} {γ₁ γ₂ : Path a b}
    (H : (γ₁ : C(I,ℂ)).Homotopy γ₂)
    (hends : ∀ s : I, H (s,0) = a ∧ H (s,1) = b)
    (hsmooth : ∀ s : I,
      ContDiffOn ℝ 2 (sourceHomotopyPath H hends s).extend (Icc 0 1))
    (havoid : ∀ s u : I, H (s,u) ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    (∫ᶜ z in γ₁, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z) =
      ∫ᶜ z in γ₂, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z := by
  let J : I → ℂ := fun s =>
    ∫ᶜ z in sourceHomotopyPath H hends s,
      NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z
  have hHuc : UniformContinuous (fun x : I × I => H x) :=
    CompactSpace.uniformContinuous_of_continuous H.continuous
  have hJ : IsLocallyConstant J := by
    apply (IsLocallyConstant.iff_eventually_eq J).2
    intro s
    obtain ⟨ε,hε,hstable⟩ :=
      exists_sourceCriticalRootRatio_openPathIntegral_eq_of_uniform_perturbation
        hp hp1 ψ hreal (sourceHomotopyPath H hends s) (hsmooth s)
        (fun u => by simpa only [sourceHomotopyPath_apply] using havoid s u)
    obtain ⟨δ,hδ,huniform⟩ := Metric.uniformContinuous_iff.mp hHuc ε hε
    filter_upwards [Metric.ball_mem_nhds s hδ] with t ht
    have hclose (u : I) :
        dist (sourceHomotopyPath H hends t u)
          (sourceHomotopyPath H hends s u) ≤ ε := by
      rw [sourceHomotopyPath_apply, sourceHomotopyPath_apply]
      apply le_of_lt
      apply huniform
      simpa only [dist_prod_same_right, mem_ball] using ht
    exact hstable (sourceHomotopyPath H hends t) (hsmooth t) hclose
  have hconst : J 0 = J 1 :=
    hJ.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ 0) (mem_univ 1)
  have h0 : sourceHomotopyPath H hends 0 = γ₁ := by
    apply Path.ext
    funext u
    simp [sourceHomotopyPath_apply]
  have h1 : sourceHomotopyPath H hends 1 = γ₂ := by
    apply Path.ext
    funext u
    simp [sourceHomotopyPath_apply]
  simpa [J,h0,h1] using hconst

end NLS.ZakharovShabat
