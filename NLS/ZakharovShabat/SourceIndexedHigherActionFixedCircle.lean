import NLS.ZakharovShabat.SourceIndexedHigherActionGradient
import NLS.ZakharovShabat.SourceCanonicalRootJointAnalytic

/-! One actual indexed-action gradient circle works on an open source
neighborhood before all levels. The derivative formula is proved at
every real source in that neighborhood, and the same circle lies in
one open joint domain of the actual analytic canonical root. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_sourceIndexedHigherAction_fixed_gradient_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∃ W : Set (CoeffPair p), IsOpen (sourceCanonicalRootJointDomain hp hp1 W) ∧
        AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1)
          (sourceCanonicalRootJointDomain hp hp1 W) ∧ U ⊆ W ∧
        ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
          (∀ ψ ∈ U, sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) ∧
          ∀ ψ ∈ U, IsRealType (CoeffPair.toMax p ψ) → ∀ k : ℕ,
            AnalyticAt ℂ (sourceIndexedHigherAction hp hp1 n k) ψ ∧
              ∀ h : CoeffPair p, (fderiv ℂ (sourceIndexedHigherAction hp hp1 n k) ψ) h =
                -(Real.pi:ℂ)⁻¹*(∮ z in C(c,R), z^k*
                  (fderiv ℂ (fun χ : CoeffPair p =>
                    canonicalDiscriminant hp (periodOnePotential χ) z) ψ) h /
                      sourceCanonicalRoot hp hp1 ψ z) := by
  obtain ⟨V,hV,_,hRV,H⟩ := sourceSection11Contours hp hp1
  obtain ⟨U,hU,_,hφU,hUV,D,c,hD,C,_⟩ := H.neighborhoods φ (hRV hφ)
  obtain ⟨W,hW,_,hRW,hDW,hroot⟩ := exists_global_source_analytic_canonicalRoot hp hp1
  have hR : 0 < C.radius n := (C.inner_pos n).trans (C.inner_lt n)
  refine ⟨U ∩ W,hU.inter hW,⟨hφU,hRW hφ⟩,W,hDW,hroot,inter_subset_right,
    C.center n,C.radius n,hR,(fun ψ hψ => (C.periodCircle hD ψ hψ.1 n).sphere_subset_rootDomain),?_⟩
  intro ψ hψ hreal k
  refine ⟨H.analytic_indexedHigherAction hV n k ψ (hUV hψ.1),?_⟩
  intro h
  have he : sourceIndexedHigherAction hp hp1 n k =ᶠ[𝓝 ψ]
      (fun χ => sourceHigherActionCircle hp hp1 χ (C.center n:ℂ) (C.radius n) k) := by
    filter_upwards [hU.mem_nhds hψ.1] with χ hχ
    exact sourceIndexedHigherAction_eq_circle (C.periodCircle hD χ hχ n) k
  rw [he.fderiv_eq]
  exact fderiv_sourceHigherActionCircle_eq_gradient_integral hp hp1 ψ hreal _ _ hR
    (C.periodCircle hD ψ hψ.1 n).sphere_subset_rootDomain k h

end NLS.ZakharovShabat
