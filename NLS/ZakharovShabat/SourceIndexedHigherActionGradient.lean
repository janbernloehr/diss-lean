import NLS.ZakharovShabat.SourceHigherActionCircleGradient
import NLS.ZakharovShabat.SourceIndexedHigherActionAnalytic

/-! Actual indexed higher-action gradients at every real-type source.
One circle works before all levels and all complex source directions. -/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_sourceIndexedHigherAction_gradient_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ ∧
      ∀ k : ℕ, AnalyticAt ℂ (sourceIndexedHigherAction hp hp1 n k) φ ∧
        ∀ h : CoeffPair p,
          (fderiv ℂ (sourceIndexedHigherAction hp hp1 n k) φ) h=
            -(Real.pi : ℂ)⁻¹ * (∮ z in C(c,R), z^k *
              (fderiv ℂ (fun ψ : CoeffPair p =>
                canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
                  sourceCanonicalRoot hp hp1 φ z) := by
  obtain ⟨W,hW,_,hreal,H⟩ := sourceSection11Contours hp hp1
  have hφW : φ ∈ W := hreal hφ
  obtain ⟨U,hU,_,hφU,_,D,c,hD,C,_⟩ := H.neighborhoods φ hφW
  have hR : 0 < C.radius n := (C.inner_pos n).trans (C.inner_lt n)
  have hcircle : sphere (C.center n : ℂ) (C.radius n) ⊆ sourceCanonicalRootDomain hp hp1 φ :=
    (C.periodCircle hD φ hφU n).sphere_subset_rootDomain
  refine ⟨C.center n,C.radius n,hR,hcircle,?_⟩
  intro k
  refine ⟨H.analytic_indexedHigherAction hW n k φ hφW,?_⟩
  intro h
  have he : sourceIndexedHigherAction hp hp1 n k =ᶠ[𝓝 φ]
      (fun ψ => sourceHigherActionCircle hp hp1 ψ (C.center n : ℂ) (C.radius n) k) := by
    filter_upwards [hU.mem_nhds hφU] with ψ hψ
    exact sourceIndexedHigherAction_eq_circle (C.periodCircle hD ψ hψ n) k
  rw [he.fderiv_eq]
  exact fderiv_sourceHigherActionCircle_eq_gradient_integral hp hp1 φ hφ _ _ hR hcircle k h

end NLS.ZakharovShabat
