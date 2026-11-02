import NLS.ZakharovShabat.SourceDiagonalLaurentAtlas
import NLS.ZakharovShabat.SourceHigherActionAtlas

/-! # Compatibility with the existing positive-level NLS actions

The Laurent construction extends the already checked higher actions.
Agreement is proved on full complex overlaps, with independence of both
atlases; it is not merely a matching definition on the real diagonal.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceRealLaurentAction_nat (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (k : ℕ) :
    sourceRealLaurentAction hp hp1 φ n ((k : ℤ)+1) = (sourceRealHigherAction hp hp1 φ n k : ℂ) := by
  simp only [sourceRealLaurentAction,sourceRealHigherAction,add_sub_cancel_right,zpow_natCast]

namespace SourceDiagonalLaurentAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} (A : SourceDiagonalLaurentAtlas hp hp1)

theorem action_eq_higherAction (B : SourceHigherActionAtlas hp hp1)
    (n : ℤ) (k : ℕ) (hn : n ≠ 0) :
    EqOn (A.action n ((k : ℤ)+1)) (B.action n k) (A.domain ∩ B.domain) := by
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ.1
  obtain ⟨θ,hθ⟩ := mem_iUnion.mp hψ.2
  rw [A.action_eq_local n _ hn φ hφ,B.action_eq_local n k θ hθ]
  apply eqOn_sourceRealCenteredBalls_of_real_agreement hp ⟨φ.val,φ.property.1⟩ θ
    _ _ _ _ ((A.localChart φ).analytic_action n _ hn).differentiableOn
    ((B.localChart θ).analytic n k).differentiableOn ?_ ⟨hφ,hθ⟩
  intro χ hχ
  rw [(A.localChart φ).action_eq_real ⟨χ.val,χ.property⟩ hχ.1 n _ hn,
    sourceRealLaurentAction_nat]
  exact ((B.localChart θ).agrees_real ⟨χ.val,χ.property⟩ hχ.2 n k).symm

end SourceDiagonalLaurentAtlas

theorem sourceDiagonalLaurentAction_nat (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (k : ℕ) (hn : n ≠ 0) :
    EqOn (sourceDiagonalLaurentAction hp hp1 n ((k : ℤ)+1)) (sourceComplexHigherAction hp hp1 n k)
      (sourceDiagonalLaurentDomain hp hp1 ∩ sourceComplexHigherActionDomain hp hp1) :=
  (sourceDiagonalLaurentAtlas hp hp1).action_eq_higherAction (sourceHigherActionAtlas hp hp1) n k hn

end NLS.ZakharovShabat
