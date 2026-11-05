import NLS.Articles.KdVPseudomeasures.EndpointIsospectralTorusImage
import NLS.Articles.KdVPseudomeasures.NativeEndpointBallBound
import NLS.SequenceSpaces.SignedSobolevPositiveEquivalence
import NLS.FunctionalAnalysis.LinearTargetDerivative
import NLS.FunctionalAnalysis.AnalyticEquivalenceInverse

/-! The article's LITERAL endpoint target bracket is1+abs(n), whereas the
native signed bracket ismax(1,abs(n)). An explicit coefficient-preserving
Banach equivalence retains ALL physical coordinates. The forward norm bound
is2^(1/2-r), the reverse bound is1; the two norms are never identified. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

abbrev ArticleEndpointRealTarget (r : ℝ) :=
  WeightedCoeff.fourierRealZeroSubmodule (Weight.sobolev (1/2-r)) ⊤

def articleEndpointTargetEquiv (r : ℝ) (hr : AdmissiblePredualOrder r) :
    HillEndpointRealSignedTarget r ≃L[ℝ] ArticleEndpointRealTarget r :=
  WeightedCoeff.physicalSignedSobolevPositiveEquiv (1/2-r) (by linarith only [hr.2]) ⊤

theorem articleEndpointTargetEquiv_apply (r : ℝ) (hr : AdmissiblePredualOrder r)
    (z : HillEndpointRealSignedTarget r) (k : ℤ) :
    (articleEndpointTargetEquiv r hr z).val.val.val k=z.val.val.val k :=
  WeightedCoeff.physicalSignedSobolevPositiveEquiv_apply _ _ z k

theorem articleEndpointTargetEquiv_symm_apply (r : ℝ) (hr : AdmissiblePredualOrder r)
    (z : ArticleEndpointRealTarget r) (k : ℤ) :
    ((articleEndpointTargetEquiv r hr).symm z).val.val.val k=z.val.val.val k :=
  WeightedCoeff.physicalSignedSobolevPositiveEquiv_symm_apply _ _ z k

/-- The ACTUAL endpoint output with the article's literal target norm. -/
def articleEndpointCoordinates (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    ArticleEndpointRealTarget r :=
  articleEndpointTargetEquiv r hr (originalEndpointRealSignedCoordinates r hr q)

theorem articleEndpointCoordinates_apply (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (k : ℤ) :
    (articleEndpointCoordinates r hr q).val.val.val k=
      (NLS.KdV.hillHminusNativeComplexMap (sourceNativePeriodOneCLM r hr q.val)).val k := by
  rw [articleEndpointCoordinates,articleEndpointTargetEquiv_apply,
    original_endpoint_real_coordinate_matches_native]

/-- The actual physical endpoint map, with the article's literal Banach target. -/
def articleEndpointPhysicalMap (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointRealMeanZeroSource r) : ArticleEndpointRealTarget r :=
  articleEndpointTargetEquiv r hr (hillEndpointRealSignedMap r hr q)

theorem analyticAt_articleEndpointPhysicalMap (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : HillEndpointRealMeanZeroSource r) : AnalyticAt ℝ (articleEndpointPhysicalMap r hr) q := by
  have he : AnalyticAt ℝ (articleEndpointTargetEquiv r hr).toContinuousLinearMap
      (hillEndpointRealSignedMap r hr q) := ContinuousLinearMap.analyticAt _ _
  exact he.comp (analyticAt_hillEndpointRealSignedMap r hr q)

theorem articleEndpointPhysicalMap_original (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    articleEndpointPhysicalMap r hr (originalEndpointRealSource r hr q)=articleEndpointCoordinates r hr q := rfl

/-- The exact free derivative, now as an equivalence with the literal article norm. -/
def articleEndpointFreeEquiv (r : ℝ) (hr : AdmissiblePredualOrder r) :
    HillEndpointRealMeanZeroSource r ≃L[ℝ] ArticleEndpointRealTarget r :=
  (WeightedCoeff.realMeanZeroNegativeOrderHalfFourierEquiv r hr.1 ⊤).trans (articleEndpointTargetEquiv r hr)

theorem fderiv_articleEndpointPhysicalMap_zero (r : ℝ) (hr : AdmissiblePredualOrder r) :
    fderiv ℝ (articleEndpointPhysicalMap r hr) 0=(articleEndpointFreeEquiv r hr).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro h
  change (fderiv ℝ (fun q => (articleEndpointTargetEquiv r hr).toContinuousLinearMap
    (hillEndpointRealSignedMap r hr q)) 0) h= _
  have hd := @NLS.FunctionalAnalysis.fderiv_comp_clm_apply ℝ
    (HillEndpointRealMeanZeroSource r) (HillEndpointRealSignedTarget r) (ArticleEndpointRealTarget r)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (hillEndpointRealSignedMap r hr) (articleEndpointTargetEquiv r hr).toContinuousLinearMap 0 h
    (analyticAt_hillEndpointRealSignedMap r hr 0).differentiableAt
  exact hd.trans (by rw [fderiv_hillEndpointRealSignedMap_zero]; rfl)


/-- Actual two-sided analytic inverse germs at the origin with the article's
literal target norm and the TRUE inverse derivative, at the full infinity endpoint. -/
theorem articleEndpointPhysicalMap_localInverse_zero (r : ℝ) (hr : AdmissiblePredualOrder r) :
    ∃ g : ArticleEndpointRealTarget r → HillEndpointRealMeanZeroSource r,
      AnalyticAt ℝ g 0 ∧ g 0=0 ∧
      (∀ᶠ q in nhds 0, g (articleEndpointPhysicalMap r hr q)=q) ∧
      (∀ᶠ z in nhds 0, articleEndpointPhysicalMap r hr (g z)=z) ∧
      fderiv ℝ g 0=(articleEndpointFreeEquiv r hr).symm.toContinuousLinearMap := by
  have hz : articleEndpointPhysicalMap r hr 0=0 := by
    change articleEndpointTargetEquiv r hr (hillEndpointRealSignedMap r hr 0)=0
    rw [hillEndpointRealSignedMap_zero,map_zero]
  simpa only [hz] using NLS.FunctionalAnalysis.exists_localInverse_of_equiv_fderiv
    (analyticAt_articleEndpointPhysicalMap r hr 0) (articleEndpointFreeEquiv r hr)
    (fderiv_articleEndpointPhysicalMap_zero r hr)

/-- Literal article endpoint action torus, in its full1+abs(n) weighted infinity norm. -/
def articleEndpointActionTorus (r : ℝ) (z : ArticleEndpointRealTarget r) : Set (ArticleEndpointRealTarget r) :=
  {w | ∀ n : ℕ+, w.val.val.val (n:ℤ)*w.val.val.val (-(n:ℤ))=
    z.val.val.val (n:ℤ)*z.val.val.val (-(n:ℤ))}

theorem articleEndpointTargetEquiv_image_actionTorus (r : ℝ) (hr : AdmissiblePredualOrder r)
    (z : HillEndpointRealSignedTarget r) :
    articleEndpointTargetEquiv r hr '' endpointActionTorus r z=
      articleEndpointActionTorus r (articleEndpointTargetEquiv r hr z) := by
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩ n
    simpa only [articleEndpointTargetEquiv_apply] using hv n
  · intro hw
    refine ⟨(articleEndpointTargetEquiv r hr).symm w,?_,(articleEndpointTargetEquiv r hr).apply_symm_apply w⟩
    intro n
    have hn := hw n
    simpa only [articleEndpointTargetEquiv_apply,articleEndpointTargetEquiv_symm_apply] using hn

/-- Source Lemma3.5(ii) with the article's LITERAL full target norm. -/
theorem sourceLemma3_5_ii_articleNorm (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    articleEndpointCoordinates r hr '' endpointIsospectralSet r hr q=
      articleEndpointActionTorus r (articleEndpointCoordinates r hr q) := by
  change (articleEndpointTargetEquiv r hr ∘ originalEndpointRealSignedCoordinates r hr) '' _= _
  rw [image_comp,sourceLemma3_5_ii,articleEndpointTargetEquiv_image_actionTorus]
  rfl

/-- Source Lemma3.6 with the article's LITERAL norm; the factor2^(1/2-r)
from native signed norm to article norm is explicitly retained. -/
theorem sourceLemma3_6_articleNorm (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q : Potential r, ‖q.val‖ ≤ R →
      ‖articleEndpointCoordinates r hr q‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := sourceLemma3_6 r hr R
  have hC : 0 ≤ (2:ℝ)^(1/2-r) := Real.rpow_nonneg (by norm_num) _
  refine ⟨(2:ℝ)^(1/2-r)*B,mul_nonneg hC hB,fun q hq => ?_⟩
  exact (WeightedCoeff.norm_physicalSignedSobolevPositiveEquiv_le _ _
    (originalEndpointRealSignedCoordinates r hr q)).trans
      (mul_le_mul_of_nonneg_left (hbound q hq) hC)

end NLS.Articles.KdVPseudomeasures
