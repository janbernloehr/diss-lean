import NLS.SequenceSpaces.RealAtlasInversePredicate
import NLS.SequenceSpaces.RealCoefficientCoordinates
import NLS.SequenceSpaces.NonnegativeAtlasCoordinates

/-! # Real inverse loci under compatible cone coordinates -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {E S : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace S] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Coordinate transport of the real inverse germ includes its actual base point. -/
theorem real_inverse_germ_in_coordinates
    (L : E ≃L[ℂ] Coeff p) (e : S ≃ₜ nonnegativeLocus p) (i : S → E)
    (hi : ∀ y, i (e.symm y) = L.symm y.val)
    (f : S → E) (U : Set S) (F : S → E → E)
    (ha : ∀ x ∈ U, AnalyticAt ℂ (F x) (i x))
    (he : ∀ x ∈ U, f =ᶠ[𝓝 x] (fun y => F x (i y))) (x : S) :
    (x ∈ U ∧ ComplexAnalysis.HasAnalyticInverse (𝕜 := ℝ)
      (coordinateRestriction L (F x)) (coordinateReCLM L (i x))) ↔
    e x ∈ (NonnegativeAnalyticAtlas.ofCoordinates L e i hi f U F ha he).realLocalInversePoints := by
  rw [NonnegativeAnalyticAtlas.realLocalInversePoints_eq_germs]
  change (x ∈ U ∧ _) ↔ (e.symm (e x) ∈ U ∧ _)
  rw [e.symm_apply_apply]
  apply and_congr_right
  intro _
  have hic : (e x).val = L (i x) := by
    have hh := congrArg L (hi (e x))
    simpa only [e.symm_apply_apply,L.apply_symm_apply] using hh.symm
  have hh := hasAnalyticInverse_coordinateRestriction_iff L (f := F x) (x := coordinateReCLM L (i x))
  rw [coordinateRealEquiv_coordinateReCLM] at hh
  simpa only [NonnegativeAnalyticAtlas.ofCoordinates,e.symm_apply_apply,hic] using hh.symm

/-- Transport a differentiable real left-inverse seed at its actual cone center. -/
theorem real_leftInverse_seed_in_coordinates
    (L : E ≃L[ℂ] Coeff p) (e : S ≃ₜ nonnegativeLocus p) (i : S → E)
    (hi : ∀ y, i (e.symm y) = L.symm y.val)
    (f : S → E) (U : Set S) (F : S → E → E)
    (ha : ∀ x ∈ U, AnalyticAt ℂ (F x) (i x))
    (he : ∀ x ∈ U, f =ᶠ[𝓝 x] (fun y => F x (i y))) (x : S)
    (hs : ComplexAnalysis.HasDifferentiableLeftInverse (𝕜 := ℝ)
      (coordinateRestriction L (F x)) (coordinateReCLM L (i x))) :
    ComplexAnalysis.HasDifferentiableLeftInverse (𝕜 := ℝ)
      (realRestriction ((NonnegativeAnalyticAtlas.ofCoordinates L e i hi f U F ha he).extension (e x)))
      (reCLM p (e x).val) := by
  have hic : (e x).val = L (i x) := by
    have hh := congrArg L (hi (e x))
    simpa only [e.symm_apply_apply,L.apply_symm_apply] using hh.symm
  have hh := differentiableLeftInverse_coordinateRestriction L hs
  rw [coordinateRealEquiv_coordinateReCLM] at hh
  simpa only [NonnegativeAnalyticAtlas.ofCoordinates,e.symm_apply_apply,hic] using hh

end NLS.Coeff
