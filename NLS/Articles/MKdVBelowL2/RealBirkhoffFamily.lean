import NLS.Articles.MKdVBelowL2.CompatibleBirkhoffFamily
import NLS.Dynamics.ConjugatePairEquiv

/-! # Real analytic geometry in the article's actual complex target -/
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat NLS.Birkhoff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The chosen physical family on the article's conjugate-pair real target. -/
def realBirkhoffFamily (hp : p ≠ ⊤) (hp1 : 1 < p) :
    PhysicalRealInput p → conjugatePairSubmodule p :=
  fun u => conjugatePairEquiv
    (physicalRealBirkhoff hp hp1 (originalBirkhoffChart hp hp1).roots u)

/-- The real target restriction retains exactly the chosen complex coordinates. -/
theorem realBirkhoffFamily_val (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalRealInput p) :
    (realBirkhoffFamily hp hp1 u).val = compatibleBirkhoff hp hp1 u.val := by
  change Birkhoff.rectangularToComplex
    (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p))
      (sourceRealBirkhoffMap hp hp1 (originalBirkhoffChart hp hp1).roots
        (physicalRealCoefficientsCL u))) = _
  rw [(originalBirkhoffChart hp hp1).data.complex.real_map_complex_inclusion]
  rfl

/-- The full real map is analytic, injective, an open embedding, and has dense image. -/
theorem realBirkhoffFamily_geometry (hp : p ≠ ⊤) (hp1 : 1 < p) :
    AnalyticOnNhd ℝ (realBirkhoffFamily hp hp1) univ ∧
      IsOpenEmbedding (realBirkhoffFamily hp hp1) ∧
      DenseRange (realBirkhoffFamily hp hp1) := by
  let D := (originalBirkhoffChart hp hp1).data.complex
  refine ⟨?_,?_,?_⟩
  · intro u _
    exact (conjugatePairEquiv.analyticAt _).comp (physicalRealBirkhoff_analytic D u (mem_univ _))
  · exact conjugatePairEquiv.toHomeomorph.isOpenEmbedding.comp (physicalRealBirkhoff_isOpenEmbedding D)
  · exact conjugatePairEquiv.surjective.denseRange.comp
      (physicalRealBirkhoff_geometry D).2.2 conjugatePairEquiv.continuous

/-- Local inverse in the physical Banach norms and the article's conjugate target. -/
theorem realBirkhoffFamily_localInverse (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalRealInput p) :
    ∃ g : conjugatePairSubmodule p → PhysicalRealInput p,
      AnalyticAt ℝ g (realBirkhoffFamily hp hp1 u) ∧
      g (realBirkhoffFamily hp hp1 u) = u ∧
      (∀ᶠ v in 𝓝 u, g (realBirkhoffFamily hp hp1 v) = v) ∧
      (∀ᶠ z in 𝓝 (realBirkhoffFamily hp hp1 u), realBirkhoffFamily hp hp1 (g z) = z) := by
  obtain ⟨g,hg,hu,hl,hr⟩ := physicalRealBirkhoff_localInverse
    (originalBirkhoffChart hp hp1).data.complex u
  refine ⟨fun z => g (conjugatePairEquiv.symm z),?_,?_,?_,?_⟩
  · have he : conjugatePairEquiv.symm (realBirkhoffFamily hp hp1 u) =
        physicalRealBirkhoff hp hp1 (originalBirkhoffChart hp hp1).roots u := by
      simp only [realBirkhoffFamily,ContinuousLinearEquiv.symm_apply_apply]
    rw [← he] at hg
    exact hg.comp ((conjugatePairEquiv (p := p)).symm.analyticAt (realBirkhoffFamily hp hp1 u))
  · simpa only [realBirkhoffFamily,ContinuousLinearEquiv.symm_apply_apply] using hu
  · simpa only [realBirkhoffFamily,ContinuousLinearEquiv.symm_apply_apply] using hl
  · have hlim := ((conjugatePairEquiv (p := p)).symm.continuous.tendsto (realBirkhoffFamily hp hp1 u))
    have hr' := hlim.eventually (by simpa only [realBirkhoffFamily,ContinuousLinearEquiv.symm_apply_apply] using hr)
    filter_upwards [hr'] with z hz
    apply conjugatePairEquiv.symm.injective
    simpa only [realBirkhoffFamily,ContinuousLinearEquiv.symm_apply_apply] using hz

/-- Surjectivity at p=2, together with the already proved analytic local inverse. -/
theorem realBirkhoffFamily_surjective (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    Function.Surjective (realBirkhoffFamily hp hp1) :=
  conjugatePairEquiv.surjective.comp
    (physicalRealBirkhoff_surjective (originalBirkhoffChart hp hp1).data.complex hp2)
/-- At Hilbert regularity the very same map is a global bi-real-analytic diffeomorphism. -/
theorem realBirkhoffFamily_globalInverse (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ e : PhysicalRealInput p ≃ₜ conjugatePairSubmodule p,
      (∀ u, e u = realBirkhoffFamily hp hp1 u) ∧
      AnalyticOnNhd ℝ (fun u => e u) univ ∧ AnalyticOnNhd ℝ (fun z => e.symm z) univ := by
  let D := (originalBirkhoffChart hp hp1).data.complex
  let e := physicalRealCoefficientsCL.toHomeomorph.trans
    ((D.realHomeomorph hp2).trans conjugatePairEquiv.toHomeomorph)
  refine ⟨e,fun _ => rfl,(realBirkhoffFamily_geometry hp hp1).1,?_⟩
  intro z _
  have h := D.realHomeomorph_symm_analytic hp2
    ((conjugatePairEquiv (p := p)).symm z) (mem_univ _)
  exact ((physicalRealCoefficientsCL (p := p)).symm.analyticAt _).comp
    (h.comp ((conjugatePairEquiv (p := p)).symm.analyticAt z))

end NLS.Articles.MKdVBelowL2
