import NLS.ZakharovShabat.SourceAbelianDiscCompatibility

/-! # One abelian primitive on the exterior and all continued discs

The union is open and carries one jointly analytic function with the
exact full differential. This gluing theorem does not yet assert that
one source neighborhood covers every spectral point off every cut.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def continuedChartDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) :
    Option (SourceAbelianDiscJointChart hp hp1 W) → Set (ℂ × CoeffPair p)
  | none => sourceAbelianEnlargedDomain hp hp1 W
  | some D => D.domain

private def continuedChartFunction (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (n : ℤ) :
    Option (SourceAbelianDiscJointChart hp hp1 W) → ℂ × CoeffPair p → ℂ
  | none => sourceAbelianEnlargedPrimitive hp hp1 W n
  | some D => D.toFun n

private theorem continuedChart_compatible (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (D E : Option (SourceAbelianDiscJointChart hp hp1 W)) :
    EqOn (continuedChartFunction hp hp1 W n D) (continuedChartFunction hp hp1 W n E)
      (continuedChartDomain hp hp1 W D ∩ continuedChartDomain hp hp1 W E) := by
  cases D with
  | none =>
    cases E with
    | none => intro t _; rfl
    | some E => exact fun _ ht => (E.eq_enlarged hD hroot n ⟨ht.2,ht.1⟩).symm
  | some D =>
    cases E with
    | none => exact D.eq_enlarged hD hroot n
    | some E => exact D.eqOn_overlap E hD hroot n

private theorem continuedChart_open (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (D : Option (SourceAbelianDiscJointChart hp hp1 W)) : IsOpen (continuedChartDomain hp hp1 W D) := by
  cases D with
  | none => exact isOpen_sourceAbelianEnlargedDomain hp hp1 W hD
  | some D => exact D.isOpen_domain hD

def sourceAbelianContinuedDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Set (ℂ × CoeffPair p) :=
  sourceAbelianEnlargedDomain hp hp1 W ∪ ⋃ D : SourceAbelianDiscJointChart hp hp1 W, D.domain

/-- The single function containing every old exterior value and every
normalized interior chart. Values outside the domain are immaterial. -/
def sourceAbelianContinuedPrimitive (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (n : ℤ) : ℂ × CoeffPair p → ℂ :=
  glueHolomorphicCharts (continuedChartDomain hp hp1 W) (continuedChartFunction hp hp1 W n)

theorem isOpen_sourceAbelianContinuedDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W)) : IsOpen (sourceAbelianContinuedDomain hp hp1 W) :=
  (isOpen_sourceAbelianEnlargedDomain hp hp1 W hD).union (isOpen_iUnion (fun D => D.isOpen_domain hD))

theorem sourceAbelianContinuedPrimitive_eq_enlarged (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) : EqOn (sourceAbelianContinuedPrimitive hp hp1 W n) (sourceAbelianEnlargedPrimitive hp hp1 W n)
      (sourceAbelianEnlargedDomain hp hp1 W) :=
  glueHolomorphicCharts_eq_on _ _ (continuedChart_compatible hp hp1 W hD hroot n) none

theorem sourceAbelianContinuedPrimitive_eq_disc (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (D : SourceAbelianDiscJointChart hp hp1 W) :
    EqOn (sourceAbelianContinuedPrimitive hp hp1 W n) (D.toFun n) D.domain :=
  glueHolomorphicCharts_eq_on _ _ (continuedChart_compatible hp hp1 W hD hroot n) (some D)

theorem sourceAbelianContinuedPrimitive_eventuallyEq_enlarged (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianEnlargedDomain hp hp1 W) :
    sourceAbelianContinuedPrimitive hp hp1 W n =ᶠ[𝓝 t] sourceAbelianEnlargedPrimitive hp hp1 W n :=
  glueHolomorphicCharts_eventuallyEq _ _ (continuedChart_open hp hp1 W hD)
    (continuedChart_compatible hp hp1 W hD hroot n) none t ht

theorem sourceAbelianContinuedPrimitive_eventuallyEq_disc (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (D : SourceAbelianDiscJointChart hp hp1 W) (t : ℂ × CoeffPair p) (ht : t ∈ D.domain) :
    sourceAbelianContinuedPrimitive hp hp1 W n =ᶠ[𝓝 t] D.toFun n :=
  glueHolomorphicCharts_eventuallyEq _ _ (continuedChart_open hp hp1 W hD)
    (continuedChart_compatible hp hp1 W hD hroot n) (some D) t ht

theorem sourceAbelianContinuedPrimitive_analytic (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) : AnalyticOnNhd ℂ (sourceAbelianContinuedPrimitive hp hp1 W n) (sourceAbelianContinuedDomain hp hp1 W) := by
  intro t ht
  rcases ht with ht | ht
  · exact (sourceAbelianEnlargedPrimitive_analytic hp hp1 W hD (sourceFloquetJointMultiplier_analyticOnNhd hp hp1 W hroot) n t ht).congr
      (sourceAbelianContinuedPrimitive_eventuallyEq_enlarged hp hp1 W hD hroot n t ht).symm
  · obtain ⟨D,ht⟩ := mem_iUnion.mp ht
    exact (D.analytic n t ht).congr (sourceAbelianContinuedPrimitive_eventuallyEq_disc hp hp1 W hD hroot n D t ht).symm

theorem sourceAbelianContinuedPrimitive_hasFDerivAt (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianContinuedDomain hp hp1 W) :
    HasFDerivAt (sourceAbelianContinuedPrimitive hp hp1 W n)
      ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t := by
  rcases ht with ht | ht
  · exact (sourceAbelianEnlargedPrimitive_hasFDerivAt hp hp1 W hD hroot n t ht).congr_of_eventuallyEq
      (sourceAbelianContinuedPrimitive_eventuallyEq_enlarged hp hp1 W hD hroot n t ht)
  · obtain ⟨D,ht⟩ := mem_iUnion.mp ht
    exact (D.hasFDerivAt hD hroot n t ht).congr_of_eventuallyEq
      (sourceAbelianContinuedPrimitive_eventuallyEq_disc hp hp1 W hD hroot n D t ht)

end NLS.ZakharovShabat
