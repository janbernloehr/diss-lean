import NLS.ZakharovShabat.SourceCriticalRootRatioSourceAnalytic

/-!
# Joint exterior analyticity of the deleted spectral factor

The exterior factorization gives a local formula for the deleted
factor using only jointly analytic spectral/source functions and the
single selected critical coordinate. Thus the deleted factor is
jointly analytic near every exterior point over a real-type source.
-/

noncomputable section
open Set Complex Filter Topology Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The deleted factor is jointly analytic in spectral point and
complex source at every exterior point over a real-type source. -/
theorem analyticAt_sourceCriticalRootRatioExtension_jointExterior
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
      sourceCriticalRootRatioExtension hp hp1 n t.2 t.1) (z,φ) := by
  let c (ψ : CoeffPair p) := canonicalCriticalPoints hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let Q := sourceCriticalRootRatioJoint hp hp1
  let S (t : ℂ × CoeffPair p) := sourceStandardRoot hp hp1 t.2 n t.1
  let E (t : ℂ × CoeffPair p) :=
    sourceCriticalRootRatioExtension hp hp1 n t.2 t.1
  have hcBase : AnalyticAt ℂ c φ :=
    analyticAt_sourceCanonicalCriticalPoint_of_realType hp hp1 n φ hreal
  have hc : AnalyticAt ℂ (fun t : ℂ × CoeffPair p => c t.2) (z,φ) := by
    exact hcBase.comp (f := fun t : ℂ × CoeffPair p => t.2)
      (analyticAt_snd (𝕜 := ℂ) (p := (z,φ)))
  obtain ⟨W₁,_,_,hreal₁,hDopen,hquot⟩ :=
    exists_global_sourceCriticalRootRatio_jointAnalytic hp hp1
  have hpoint : (z,φ) ∈ sourceCanonicalRootJointDomain hp hp1 W₁ :=
    ⟨hreal₁ hreal,hz⟩
  have hQ : AnalyticAt ℂ Q (z,φ) := hquot (z,φ) hpoint
  obtain ⟨W₂,_,_,hreal₂,hstd⟩ :=
    exists_global_source_analytic_standardRoot hp hp1
  have hS : AnalyticAt ℂ S (z,φ) :=
    hstd φ (hreal₂ hreal) n z (hz n)
  have hden : AnalyticAt ℂ
      (fun t : ℂ × CoeffPair p => c t.2 - t.1) (z,φ) :=
    hc.sub analyticAt_fst
  have hcrit : c φ - z ≠ 0 := by
    intro he
    have hcz : c φ = z := sub_eq_zero.mp he
    exact (hz n) (hcz ▸
      sourceCanonicalCriticalPoint_mem_periodicSegment_of_realType
        hp hp1 n φ hreal)
  have hratio : AnalyticAt ℂ
      (fun t : ℂ × CoeffPair p => Q t * S t / (c t.2 - t.1)) (z,φ) :=
    (hQ.mul hS).div hden hcrit
  have hdomain : ∀ᶠ t : ℂ × CoeffPair p in 𝓝 (z,φ),
      t.1 ∈ sourceCanonicalRootDomain hp hp1 t.2 := by
    have hnear := hDopen.mem_nhds hpoint
    filter_upwards [hnear] with t ht
    exact ht.2
  have hcne : ∀ᶠ t : ℂ × CoeffPair p in 𝓝 (z,φ),
      c t.2 - t.1 ≠ 0 :=
    hden.continuousAt.eventually_ne hcrit
  have heq : (fun t : ℂ × CoeffPair p =>
      Q t * S t / (c t.2 - t.1)) =ᶠ[𝓝 (z,φ)] E := by
    filter_upwards [hdomain,hcne] with t htdom htc
    have hfact := sourceCriticalRootRatio_eq_selectedFactor_mul_extension
      hp hp1 t.2 n t.1 htdom
    have hSnonzero : S t ≠ 0 :=
      sourceStandardRoot_ne_zero_off_segment hp hp1 t.2 n t.1 (htdom n)
    change Q t = ((c t.2-t.1)/S t)*E t at hfact
    apply (div_eq_iff htc).2
    rw [hfact]
    field_simp [hSnonzero]
  exact hratio.congr heq

/-- Every point of a fixed enclosing circle has joint spectral/source
analyticity of the deleted factor at the base real-type source. -/
theorem exists_sourceCriticalRootRatioExtension_jointAnalytic_onEnclosingCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      sourcePeriodicSegment hp hp1 φ n ⊆ ball c R ∧
      ∀ z ∈ sphere c R,
        AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
          sourceCriticalRootRatioExtension hp hp1 n t.2 t.1) (z,φ) := by
  obtain ⟨V,_,hφV,c,R,hR,hgeom⟩ :=
    exists_local_sourceCriticalRootRatio_uniformEnclosingCircle
      hp hp1 φ hreal n
  refine ⟨c,R,hR,(hgeom φ hφV).1,?_⟩
  intro z hz
  exact analyticAt_sourceCriticalRootRatioExtension_jointExterior
    hp hp1 n φ hreal z ((hgeom φ hφV).2.2 hz)

/-- Compactness of the enclosing circle turns pointwise joint
analyticity into a single open spectral/source tube. The same fixed
circle continues to enclose the selected moving gap throughout the
source neighborhood. -/
theorem exists_local_sourceCriticalRootRatioExtension_analyticTube
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        ∃ U : Set ℂ, IsOpen U ∧ sphere c R ⊆ U ∧
          (∀ ψ ∈ V,
            sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
            sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) ∧
          ∀ ψ ∈ V, ∀ z ∈ U,
            AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
              sourceCriticalRootRatioExtension hp hp1 n t.2 t.1) (z,ψ) := by
  obtain ⟨V₀,hV₀open,hφV₀,c,R,hR,hgeom⟩ :=
    exists_local_sourceCriticalRootRatio_uniformEnclosingCircle
      hp hp1 φ hreal n
  let E : ℂ × CoeffPair p → ℂ := fun t =>
    sourceCriticalRootRatioExtension hp hp1 n t.2 t.1
  let A : Set (ℂ × CoeffPair p) := {t | AnalyticAt ℂ E t}
  have hAopen : IsOpen A := isOpen_analyticAt ℂ E
  have hcircle : ∀ z ∈ sphere c R, AnalyticAt ℂ E (z,φ) := by
    intro z hz
    exact analyticAt_sourceCriticalRootRatioExtension_jointExterior
      hp hp1 n φ hreal z ((hgeom φ hφV₀).2.2 hz)
  have hsubset : sphere c R ×ˢ {φ} ⊆ A := by
    rintro ⟨z,ψ⟩ ⟨hz,hψ⟩
    have hψeq : ψ = φ := by simpa using hψ
    subst ψ
    exact hcircle z hz
  obtain ⟨U,V₁,hUopen,hV₁open,hKU,hφV₁,hUV⟩ :=
    generalized_tube_lemma (isCompact_sphere c R)
      isCompact_singleton hAopen hsubset
  refine ⟨V₀ ∩ V₁,hV₀open.inter hV₁open,
    ⟨hφV₀,hφV₁ (mem_singleton φ)⟩,c,R,hR,
    U,hUopen,hKU,?_,?_⟩
  · intro ψ hψ
    exact ⟨(hgeom ψ hψ.1).1,(hgeom ψ hψ.1).2.2⟩
  · intro ψ hψ z hz
    exact hUV ⟨hz,hψ.2⟩

end NLS.ZakharovShabat
