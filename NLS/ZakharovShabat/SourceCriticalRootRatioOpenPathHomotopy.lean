import NLS.ZakharovShabat.SourceCriticalRootRatioContourHomotopy

/-!
# Homotopy invariance for open quotient paths

A smooth deformation of two open paths preserves the quotient integral
when its endpoint traces stay fixed and its image avoids all periodic
gap segments. This complements the existing closed-loop homotopy
theorem and permits crossings outside a single half-plane.
-/

noncomputable section
open Set Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Two smooth open paths with the same fixed endpoints have equal
critical-root quotient integrals under a smooth gap-avoiding homotopy. -/
theorem sourceCriticalRootRatio_openPathIntegral_eq_of_homotopy_range
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    {a b : ℂ} {γ₁ γ₂ : Path a b}
    (H : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hends : ∀ s : I, H (s, 0) = a ∧ H (s, 1) = b)
    (havoid : range H ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (hsmooth : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
      (Icc 0 1)) :
    (∫ᶜ z in γ₁, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
        sourceCanonicalRoot hp hp1 ψ w) z) =
      ∫ᶜ z in γ₂, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z := by
  let f : ℂ → ℂ := fun w =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
      sourceCanonicalRoot hp hp1 ψ w
  have hclosed : IsClosed (range H) :=
    (isCompact_range (map_continuous H)).isClosed
  have heq := NLS.ComplexAnalysis.curveIntegral_add_sides_eq_of_holomorphic_homotopy
    f H (t := range H)
    (by intro s _ u _; exact ⟨(s,u),rfl⟩)
    (by
      intro z hz
      rw [hclosed.closure_eq] at hz
      exact (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z
        (havoid hz)).differentiableAt)
    hsmooth
  have hγ₁a : γ₁ (0:I) = a := by simp
  have hγ₂a : γ₂ (0:I) = a := by simp
  have hγ₁b : γ₁ (1:I) = b := by simp
  have hγ₂b : γ₂ (1:I) = b := by simp
  have hleft : (H.evalAt 0).cast hγ₁a.symm hγ₂a.symm = Path.refl a := by
    apply Path.ext
    funext s
    exact (hends s).1
  have hright : (H.evalAt 1).cast hγ₁b.symm hγ₂b.symm = Path.refl b := by
    apply Path.ext
    funext s
    exact (hends s).2
  have hleftIntegral :
      (∫ᶜ z in H.evalAt 0, NLS.ComplexAnalysis.holomorphicOneForm f z) = 0 := by
    calc
      _ = ∫ᶜ z in (H.evalAt 0).cast hγ₁a.symm hγ₂a.symm,
          NLS.ComplexAnalysis.holomorphicOneForm f z := by simp
      _ = 0 := by rw [hleft]; simp
  have hrightIntegral :
      (∫ᶜ z in H.evalAt 1, NLS.ComplexAnalysis.holomorphicOneForm f z) = 0 := by
    calc
      _ = ∫ᶜ z in (H.evalAt 1).cast hγ₁b.symm hγ₂b.symm,
          NLS.ComplexAnalysis.holomorphicOneForm f z := by simp
      _ = 0 := by rw [hright]; simp
  rw [hleftIntegral, hrightIntegral] at heq
  simpa only [add_zero] using heq

end NLS.ZakharovShabat
