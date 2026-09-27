import NLS.ZakharovShabat.SourceNormalizedActionNoncollapsed
import NLS.ZakharovShabat.SourceActionCircle

/-!
# The complex action vanishes on the collapsed-gap locus

Theorem 11.2 extends the quotient of an action by the squared gap.
Before constructing that extension, the action must vanish on the
complex zero locus of the squared gap. The fixed-circle action has
this property on a common neighborhood of the real-type sources;
the chart formula transfers it to the glued complex action.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A common complex neighborhood of the real-type locus on which
every indexed complex action vanishes whenever its selected periodic
gap collapses. The point must also belong to that action's domain. -/
theorem exists_global_sourceComplexAction_zero_of_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ,
        ψ ∈ sourceComplexActionDomain hp hp1 n →
        sourcePeriodicGapDisplacement hp hp1 ψ n = 0 →
        sourceComplexAction hp hp1 n ψ = 0 := by
  obtain ⟨W,hWopen,hreal,hzero⟩ :=
    exists_global_sourceActionCircle_zero_of_zeroGap hp hp1
  refine ⟨W,hWopen,hreal,?_⟩
  intro ψ hψ n hdom hgap
  obtain ⟨ch,hψch⟩ := hdom
  have hgeom := ch.geometry ψ hψch
  have hroot : sphere ch.spectralCenter ch.spectralRadius ⊆
      sourceCanonicalRootDomain hp hp1 ψ :=
    sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n
      ch.spectralCenter ch.spectralRadius hgeom.1 hgeom.2
  rw [sourceComplexAction_eq_chart hp hp1 n ch ψ hψch]
  exact hzero ψ hψ n hgap ch.spectralCenter ch.spectralRadius
    ch.spectralRadius_pos.le hgeom.2 hroot

/-- On that same neighborhood, vanishing of the analytic squared gap
forces the complex action to vanish. -/
theorem exists_global_sourceComplexAction_zero_of_squaredGap_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ,
        ψ ∈ sourceComplexActionDomain hp hp1 n →
        (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 = 0 →
        sourceComplexAction hp hp1 n ψ = 0 := by
  obtain ⟨W,hWopen,hreal,hzero⟩ :=
    exists_global_sourceComplexAction_zero_of_zeroGap hp hp1
  refine ⟨W,hWopen,hreal,?_⟩
  intro ψ hψ n hdom hgap
  apply hzero ψ hψ n hdom
  by_contra hne
  exact (pow_ne_zero 2 hne) hgap

/-- The analytic squared-gap and complex zero-locus statements hold
simultaneously on one neighborhood, independently of the index. This
is the local input needed for division by the squared gap. -/
theorem exists_global_sourceAction_analyticSquaredGap_zeroLocus
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ,
        AnalyticAt ℂ (fun χ : CoeffPair p =>
          (sourcePeriodicGapDisplacement hp hp1 χ n)^2) ψ ∧
        (ψ ∈ sourceComplexActionDomain hp hp1 n →
          (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 = 0 →
          sourceComplexAction hp hp1 n ψ = 0) := by
  obtain ⟨W₁,hW₁open,_,hreal₁,hanalytic⟩ :=
    exists_global_source_analytic_midpoint_squaredGap hp hp1
  obtain ⟨W₂,hW₂open,hreal₂,hzero⟩ :=
    exists_global_sourceComplexAction_zero_of_squaredGap_zero hp hp1
  refine ⟨W₁ ∩ W₂,hW₁open.inter hW₂open,?_,?_⟩
  · intro ψ hψ
    exact ⟨hreal₁ hψ,hreal₂ hψ⟩
  · intro ψ hψ n
    constructor
    · have hq := (hanalytic ψ hψ.1 n).2
      exact hq.congr (Filter.Eventually.of_forall fun χ => by
        simp only [sourcePeriodicGapDisplacement_apply])
    · exact hzero ψ hψ.2 n

end NLS.ZakharovShabat
