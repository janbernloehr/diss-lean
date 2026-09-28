import NLS.ZakharovShabat.SourcePsiNearFreeRegularAnalytic
import NLS.ZakharovShabat.SourcePsiIsolatingRootSeparation

/-!
# Regular psi factor on an isolating disc

The deleted-root denominator of the regular factor stays nonzero on
a selected closed disc contained in its assigned isolating disc.
Analyticity of the single-root quotient then gives analyticity of the
weighted regular factor throughout that selected disc.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem analyticOnNhd_deletedPsi_gapRegularFactor_of_isolatingDisc
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φiso : CoeffPair p) (N : ℕ) (ε : ℝ)
    (n m : ℤ) (a : Coeff p)
    (ψ : CoeffPair p) (W : Set (CoeffPair p)) (hψW : ψ ∈ W)
    (hQ : AnalyticOnNhd ℂ
      (sourceSingleRootQuotientJointProduct hp hp1 m)
      (sourceSingleRootQuotientJointDomain hp hp1 W m))
    (c : ℂ) (R : ℝ)
    (hdom : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hclosed : closedBall c R ⊆
      sourceIsolatingDisc hp hp1 φiso N ε m)
    (hrootn : displacedRoots a n ∈
      sourceIsolatingDisc hp hp1 φiso N ε n)
    (hdisjoint : Disjoint
      (sourceIsolatingDisc hp hp1 φiso N ε m)
      (sourceIsolatingDisc hp hp1 φiso N ε n)) :
    AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m a ψ z))
      (closedBall c R) := by
  intro z hz
  have hquot : AnalyticAt ℂ
      (fun w => sourceSingleRootQuotientJointProduct hp hp1 m
        (w,(a,ψ))) z := by
    have hmap : AnalyticAt ℂ
        (fun w : ℂ => (w,(a,ψ))) z :=
      analyticAt_id.prod (analyticAt_const.prod analyticAt_const)
    exact (hQ (z,(a,ψ)) ⟨hψW,hdom hz⟩).comp
      (f := fun w => (w,(a,ψ))) hmap
  have hden : displacedRoots a n-z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hrootm : displacedRoots a n ∈
        sourceIsolatingDisc hp hp1 φiso N ε m :=
      he ▸ hclosed hz
    exact Set.disjoint_left.mp hdisjoint hrootm hrootn
  have hD : AnalyticAt ℂ
      (fun w => displacedRoots a n-w) z :=
    analyticAt_const.sub analyticAt_id
  change AnalyticAt ℂ (fun w =>
    (((n-m : ℤ) : ℂ) *
      (I * sourceSingleRootQuotientJointProduct hp hp1 m
        (w,(a,ψ)) /
        (displacedRoots a n-w)))) z
  exact analyticAt_const.mul ((analyticAt_const.mul hquot).div hD hden)

end NLS.ZakharovShabat
