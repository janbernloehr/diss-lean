import NLS.ZakharovShabat.SourceRealActionConvexOverlap

/-!
# Compatible ball charts for indexed actions

The real-part projection does not increase distance from a real-type
source. Hence every nonempty intersection of balls centered at
real-type sources contains a real-type source. The convex-overlap
identity principle then identifies their fixed-circle action formulas
throughout the intersection.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source real-part projection fixes every real-type source. -/
theorem sourceRealPart_eq_self_of_realType
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    sourceRealPart φ = φ := by
  have hfix : sourceConjugation φ = φ :=
    (sourceConjugation_fixed_iff φ).mpr hφ
  simp only [sourceRealPart,hfix]
  module

/-- Projection onto the real-type source locus contracts distances
from every real-type source. -/
theorem dist_sourceRealPart_le_of_realType
    (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (ψ : CoeffPair p) :
    dist (sourceRealPart ψ) φ ≤ dist ψ φ := by
  have hfix : sourceConjugation φ = φ :=
    (sourceConjugation_fixed_iff φ).mpr hφ
  have hsub : sourceRealPart ψ - φ = sourceRealPart (ψ-φ) := by
    simp only [sourceRealPart,sourceConjugation_sub,hfix]
    module
  rw [dist_eq_norm,dist_eq_norm,hsub]
  exact norm_sourceRealPart_le hp (ψ-φ)

/-- Any nonempty intersection of balls centered at real-type
sources contains a real-type source. -/
theorem exists_realType_mem_inter_sourceBalls
    (hp : p ≠ ⊤)
    (φ₀ φ₁ : CoeffPair p)
    (hφ₀ : IsRealType (CoeffPair.toMax p φ₀))
    (hφ₁ : IsRealType (CoeffPair.toMax p φ₁))
    (r₀ r₁ : ℝ)
    (ψ : CoeffPair p)
    (hψ : ψ ∈ ball φ₀ r₀ ∩ ball φ₁ r₁) :
    ∃ θ : CoeffPair p,
      IsRealType (CoeffPair.toMax p θ) ∧
      θ ∈ ball φ₀ r₀ ∩ ball φ₁ r₁ := by
  refine ⟨sourceRealPart ψ,sourceRealPart_realType ψ,?_⟩
  constructor
  · exact lt_of_le_of_lt
      (dist_sourceRealPart_le_of_realType hp φ₀ hφ₀ ψ) hψ.1
  · exact lt_of_le_of_lt
      (dist_sourceRealPart_le_of_realType hp φ₁ hφ₁ ψ) hψ.2

/-- Every indexed real action has a complex-differentiable fixed-circle
extension on a ball centered at the real-type source. -/
theorem exists_sourceRealAction_ballChart
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        (∀ ψ ∈ ball φ ρ,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
        DifferentiableOn ℂ
          (fun ψ : CoeffPair p => sourceActionCircle hp hp1 ψ c R)
          (ball φ ρ) ∧
        ∀ ψ ∈ ball φ ρ,
          ∀ hψ : IsRealType (CoeffPair.toMax p ψ),
            sourceRealAction hp hp1 ψ hψ n =
              sourceActionCircle hp hp1 ψ c R := by
  obtain ⟨c,R,hR,V,hVopen,hφV,hgeom,hdiff,hagree⟩ :=
    exists_local_differentiable_extension_of_sourceRealAction
      hp hp1 φ hφ n
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hφV)
  refine ⟨ρ,hρ,c,R,hR,?_,hdiff.mono hball,?_⟩
  · intro ψ hψ
    exact hgeom ψ (hball hψ)
  · intro ψ hψ hψreal
    exact hagree ψ (hball hψ) hψreal

/-- Two differentiable fixed-circle action formulas that represent
the indexed real action on balls centered at real-type sources agree
on their full intersection. -/
theorem sourceActionCircle_eqOn_realCenteredBall_overlap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ₀ φ₁ : CoeffPair p)
    (hφ₀ : IsRealType (CoeffPair.toMax p φ₀))
    (hφ₁ : IsRealType (CoeffPair.toMax p φ₁))
    (n : ℤ) (c₀ c₁ : ℂ) (R₀ R₁ r₀ r₁ : ℝ)
    (hdiff₀ : DifferentiableOn ℂ
      (fun ψ : CoeffPair p => sourceActionCircle hp hp1 ψ c₀ R₀)
      (ball φ₀ r₀))
    (hdiff₁ : DifferentiableOn ℂ
      (fun ψ : CoeffPair p => sourceActionCircle hp hp1 ψ c₁ R₁)
      (ball φ₁ r₁))
    (hreal₀ : ∀ ψ ∈ ball φ₀ r₀,
      ∀ hψ : IsRealType (CoeffPair.toMax p ψ),
        sourceRealAction hp hp1 ψ hψ n =
          sourceActionCircle hp hp1 ψ c₀ R₀)
    (hreal₁ : ∀ ψ ∈ ball φ₁ r₁,
      ∀ hψ : IsRealType (CoeffPair.toMax p ψ),
        sourceRealAction hp hp1 ψ hψ n =
          sourceActionCircle hp hp1 ψ c₁ R₁) :
    ∀ ψ ∈ ball φ₀ r₀ ∩ ball φ₁ r₁,
      sourceActionCircle hp hp1 ψ c₀ R₀ =
        sourceActionCircle hp hp1 ψ c₁ R₁ := by
  intro ψ hψ
  obtain ⟨θ,hθreal,hθ⟩ :=
    exists_realType_mem_inter_sourceBalls hp φ₀ φ₁ hφ₀ hφ₁ r₀ r₁ ψ hψ
  exact sourceActionCircle_eqOn_convex_overlap
    hp hp1 θ hθreal n c₀ c₁ R₀ R₁
    (ball φ₀ r₀) (ball φ₁ r₁)
    isOpen_ball isOpen_ball (convex_ball _ _) (convex_ball _ _)
    hθ.1 hθ.2 hdiff₀ hdiff₁ hreal₀ hreal₁ ψ hψ

end NLS.ZakharovShabat
