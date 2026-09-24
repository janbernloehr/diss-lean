import NLS.ZakharovShabat.SourceComplexActionProperties

/-!
# Uniqueness of the glued complex action

The open domain is covered by convex balls centered at real-type
sources. On each ball, the real-form identity principle and complex
line analyticity force a differentiable extension of the indexed real
action to equal the glued action. Thus the glued extension is unique
among complex-differentiable functions on its domain.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The glued action is the unique complex-differentiable extension
of the indexed real action on its open source domain. -/
theorem sourceComplexAction_unique_of_real_agreement
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (F : CoeffPair p → ℂ)
    (hFdiff : DifferentiableOn ℂ F
      (sourceComplexActionDomain hp hp1 n))
    (hFreal : ∀ φ : CoeffPair p,
      ∀ hφ : IsRealType (CoeffPair.toMax p φ),
        F φ = sourceRealAction hp hp1 φ hφ n) :
    EqOn F (sourceComplexAction hp hp1 n)
      (sourceComplexActionDomain hp hp1 n) := by
  intro ψ hψ
  obtain ⟨ch,hψch⟩ := hψ
  let B := ball ch.center ch.radius
  have hBD : B ⊆ sourceComplexActionDomain hp hp1 n := by
    intro b hb
    exact ⟨ch,hb⟩
  have hFball : DifferentiableOn ℂ F B := hFdiff.mono hBD
  have hGball : DifferentiableOn ℂ (sourceComplexAction hp hp1 n) B :=
    (sourceComplexAction_differentiableOn hp hp1 n).mono hBD
  have hrealEq : ∀ b ∈ B ∩ B,
      IsRealType (CoeffPair.toMax p b) →
        F b = sourceComplexAction hp hp1 n b := by
    intro b _ hbReal
    exact (hFreal b hbReal).trans
      (sourceComplexAction_eq_sourceRealAction hp hp1 n b hbReal).symm
  have hEq := eqOn_convex_overlap_of_eqOn_realType
    hp ch.center ch.center_real B B
    isOpen_ball isOpen_ball (convex_ball _ _) (convex_ball _ _)
    (mem_ball_self ch.radius_pos) (mem_ball_self ch.radius_pos)
    F (sourceComplexAction hp hp1 n) hFball hGball hrealEq
  exact hEq ⟨hψch,hψch⟩

end NLS.ZakharovShabat
