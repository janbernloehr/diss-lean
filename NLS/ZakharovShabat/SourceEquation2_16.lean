import NLS.ZakharovShabat.SourceActionPiecewiseContour
import NLS.ZakharovShabat.SourceIndexedActionAnalytic

/-!
# Equation (2.16) on the unchanged common source domain

One indexed action is represented by the literal normalized integral on
every admissible counterclockwise piecewise C¹ circuit in every original
isolating family. The definition is analytic throughout W, agrees with
the existing real action and has the same complex germs as the earlier
chart construction. The gradient assertion of Lemma 11.1 is separate.
-/

noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal action definition and its contour-independent common-domain package. -/
structure SourceEquation2_16Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceSection11ContourData hp hp1 W
  circuit : ∀ {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ},
    SourceIsolatingNeighborhoods hp hp1 V D c → ∀ ψ ∈ W, ψ ∈ V → ∀ n : ℤ,
    ∀ Γ : PiecewiseC1Loop, Γ.Inside (D n \ sourcePeriodicSegment hp hp1 ψ n) →
      Γ.windingIntegral
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) = 1 →
      sourceIndexedAction hp hp1 n ψ = (Real.pi : ℂ)⁻¹*Γ.integral
        (fun z => z*deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z)
  analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceIndexedAction hp hp1 n) W
  real_agreement : ∀ n : ℤ, ∀ φ : CoeffPair p, ∀ hφ : IsRealType (CoeffPair.toMax p φ),
    sourceIndexedAction hp hp1 n φ = sourceRealAction hp hp1 φ hφ n
  complex_germs : ∀ n : ℤ, ∀ φ : CoeffPair p, IsRealType (CoeffPair.toMax p φ) → φ ∈ W →
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∩ sourceComplexActionDomain hp hp1 n ∧
      EqOn (sourceIndexedAction hp hp1 n) (sourceComplexAction hp hp1 n) U

/-- Define the actions without shrinking W or losing any preceding contour data. -/
theorem SourceSection11ContourData.defineActions
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceSection11ContourData hp hp1 W) (hW : IsOpen W) : SourceEquation2_16Data hp hp1 W := by
  refine ⟨h,?_,h.analytic_indexedAction hW,sourceIndexedAction_eq_sourceRealAction hp hp1,
    h.indexedAction_eq_complexAction_near_real hW⟩
  intro V D c hD ψ _ hψ n Γ hΓ hw
  simpa only [sourceActionContour,sourceCriticalRootRatioJoint,mul_div_assoc] using!
    hD.indexedAction_eq_circuit ψ hψ n Γ hΓ hw

/-- Equation (2.16) for every finite p>1 on the retained open connected
neighborhood of the entire real-type source locus. -/
theorem sourceEquation2_16 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceEquation2_16Data hp hp1 W := by
  obtain ⟨W,ho,hc,hr,h⟩ := sourceSection11Contours hp hp1
  exact ⟨W,ho,hc,hr,h.defineActions ho⟩

end NLS.ZakharovShabat
