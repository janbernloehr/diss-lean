import NLS.Articles.KdVPseudomeasures.SourceAiryFlowGeneric
import NLS.FunctionalAnalysis.AnalyticInverseChart

/-! Generic strong norm discontinuity of the actual KdV solution curves
on a neighborhood of the zero original physical potential. -/
noncomputable section
open Set NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem sourceRemark1_2_KdV (r : ℝ) (hr : AdmissiblePredualOrder r) :
    ∃ U : Set (Potential r), IsOpen U ∧ originalEndpointPotential r hr 0 ∈ U ∧
      ∃ G : Set U, IsOpen G ∧ Dense G ∧
        ∀ q ∈ G, ¬ContinuousAt (hillEndpointCanonicalKdVFlow r hr q.val) 0 := by
  obtain ⟨P,hPzero,hP⟩ := NLS.FunctionalAnalysis.exists_openPartialHomeomorph_of_equiv_fderiv
    (analyticAt_articleEndpointPhysicalMap r hr 0) (articleEndpointFreeEquiv r hr)
    (fderiv_articleEndpointPhysicalMap_zero r hr)
  let H := originalEndpointRealSourceHomeomorph r hr
  let T := H.toOpenPartialHomeomorph.trans P
  have hT (q : Potential r) : T q=articleEndpointCoordinates r hr q := by
    change P (H q)=articleEndpointCoordinates r hr q
    rw [hP]
    exact articleEndpointPhysicalMap_original r hr q
  have hzero : originalEndpointPotential r hr 0 ∈ T.source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨by trivial,?_⟩
    change originalEndpointRealSource r hr (originalEndpointPotential r hr 0) ∈ P.source
    rw [originalEndpointRealSource_potential]
    exact hPzero
  let G := {q : T.source | ¬PositiveWeightedC0 (Weight.sobolev (1/2-r)) (T q.val)}
  refine ⟨T.source,T.open_source,hzero,G,?_,?_,?_⟩
  · exact (isOpen_not_positiveWeightedC0 (Weight.sobolev (1/2-r))).preimage
      T.isOpenEmbedding_restrict.continuous
  · exact (dense_not_positiveWeightedC0 (Weight.sobolev (1/2-r)) (Weight.sobolev_neg (1/2-r))).preimage
      T.isOpenEmbedding_restrict.isOpenMap
  · intro q hq
    apply sourceKdV_not_continuousAt_norm_of_not_c0 r hr q.val
    change ¬PositiveWeightedC0 (Weight.sobolev (1/2-r)) (T q.val) at hq
    rw [hT q.val] at hq
    exact hq

/-- Full Remark 1.2, with generic stated precisely as an open dense set
in the original norm topology, globally for Airy and near zero for KdV. -/
theorem sourceRemark1_2 (r : ℝ) (hr : AdmissiblePredualOrder r) :
    (∃ G : Set (Potential r), IsOpen G ∧ Dense G ∧
      ∀ q ∈ G, ¬ContinuousAt (sourceAiryFlow r hr q) 0) ∧
    (∃ U : Set (Potential r), IsOpen U ∧ originalEndpointPotential r hr 0 ∈ U ∧
      ∃ G : Set U, IsOpen G ∧ Dense G ∧
        ∀ q ∈ G, ¬ContinuousAt (hillEndpointCanonicalKdVFlow r hr q.val) 0) :=
  ⟨sourceRemark1_2_Airy r hr,sourceRemark1_2_KdV r hr⟩

end NLS.Articles.KdVPseudomeasures
