import NLS.ZakharovShabat.SourceDiagonalLaurentCompatibility
import NLS.ZakharovShabat.SourceComplexActionAnalytic

/-! # The full ordinary-action cotangent of the Laurent extension

The existing higher-action compatibility identifies complex germs at
every real diagonal. Thus level one has exactly the original NLS action's
entire Frechet derivative, including at collapsed action gaps.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem eventually_sourceDiagonalLaurentAction_one (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realDiagonalSourceLocus p) (n : ℤ) (hn : n ≠ 0) :
    sourceDiagonalLaurentAction hp hp1 n 1 =ᶠ[𝓝 φ.val] sourceComplexAction hp hp1 n := by
  have ho := ((isOpen_sourceDiagonalLaurentDomain hp hp1).inter
    (isOpen_sourceComplexHigherActionDomain hp hp1)).inter (isOpen_sourceComplexActionDomain hp hp1 n)
  have hm : φ.val ∈ (sourceDiagonalLaurentDomain hp hp1 ∩ sourceComplexHigherActionDomain hp hp1) ∩
      sourceComplexActionDomain hp hp1 n :=
    ⟨⟨realDiagonal_subset_sourceDiagonalLaurentDomain hp hp1 φ.property,
      realType_subset_sourceComplexHigherActionDomain hp hp1 φ.property.1⟩,
      realTypeSourceLocus_subset_sourceComplexActionDomain hp hp1 n φ.property.1⟩
  filter_upwards [ho.mem_nhds hm] with χ hχ
  have he := sourceDiagonalLaurentAction_nat hp hp1 n 0 hn hχ.1
  simp only [Nat.cast_zero,zero_add] at he
  exact he.trans (sourceComplexHigherAction_zero hp hp1 n ⟨hχ.1.2,hχ.2⟩)

theorem fderiv_sourceDiagonalLaurentAction_one (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realDiagonalSourceLocus p) (n : ℤ) (hn : n ≠ 0) :
    fderiv ℂ (sourceDiagonalLaurentAction hp hp1 n 1) φ.val =
      fderiv ℂ (sourceComplexAction hp hp1 n) φ.val :=
  (eventually_sourceDiagonalLaurentAction_one hp hp1 φ n hn).fderiv_eq

end NLS.ZakharovShabat
