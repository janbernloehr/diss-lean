import NLS.ZakharovShabat.SourceBirkhoffProposition17_1
import Mathlib.Topology.IsLocalHomeomorph

/-! # The actual real Birkhoff map as a local homeomorphism -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B W : Set (CoeffPair p)} {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Proposition 17.1 supplies the local-homeomorphism structure on the
complete real source space, for every finite exponent above one. -/
theorem real_map_isLocalHomeomorph
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    IsLocalHomeomorph (sourceRealBirkhoffMap hp hp1 s) := by
  intro φ
  have ha := D.real_map_analytic φ (mem_univ φ)
  have hd : HasStrictFDerivAt (sourceRealBirkhoffMap hp hp1 s)
      (D.realJacobianEquivAll φ).toContinuousLinearMap φ :=
    ha.contDiffAt.hasStrictFDerivAt (n := 1) one_ne_zero
  exact ⟨hd.toOpenPartialHomeomorph (sourceRealBirkhoffMap hp hp1 s),
    hd.mem_toOpenPartialHomeomorph_source,hd.toOpenPartialHomeomorph_coe.symm⟩

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
