import NLS.SequenceSpaces.FourierRealZeroSubmodule
import NLS.SequenceSpaces.WeightedFourierTail

/-! Symmetric finite Fourier truncations preserve the exact physical
real form and zero mode, and converge in every finite weighted lp norm. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def fourierRealZeroTruncate (w : Weight) (N : ℕ) (a : fourierRealZeroSubmodule w p) :
    fourierRealZeroSubmodule w p :=
  ⟨⟨truncate w p (Coeff.lowFrequencies N) a.val.val,by
    change (truncate w p (Coeff.lowFrequencies N) a.val.val).val 0=0
    rw [truncate_apply]
    split_ifs
    · exact a.val.property
    · rfl⟩,by
    intro k
    change (truncate w p (Coeff.lowFrequencies N) a.val.val).val (-k)=
      (starRingEnd ℂ) ((truncate w p (Coeff.lowFrequencies N) a.val.val).val k)
    simp only [truncate_apply,Coeff.mem_lowFrequencies,Int.natAbs_neg]
    split_ifs
    · exact a.property k
    · exact (map_zero _).symm⟩

@[simp] theorem fourierRealZeroTruncate_apply (w : Weight) (N : ℕ)
    (a : fourierRealZeroSubmodule w p) (k : ℤ) :
    (fourierRealZeroTruncate w N a).val.val.val k = if k.natAbs < N then a.val.val.val k else 0 := by
  exact (truncate_apply w p (Coeff.lowFrequencies N) a.val.val k).trans
    (by simp only [Coeff.mem_lowFrequencies])

/-- Finite symmetric truncations converge in the actual physical real norm. -/
theorem tendsto_fourierRealZeroTruncate (hp : p ≠ ⊤) (w : Weight)
    (a : fourierRealZeroSubmodule w p) :
    Tendsto (fun N : ℕ => fourierRealZeroTruncate w N a) atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := Metric.tendsto_atTop.mp (tendsto_fourierTail hp w a.val.val) ε hε
  refine ⟨K,fun N hN => ?_⟩
  have ht := hK N hN
  rw [dist_eq_norm,sub_zero] at ht
  rw [dist_eq_norm]
  change ‖truncate w p (Coeff.lowFrequencies N) a.val.val-a.val.val‖ < ε
  have he : truncate w p (Coeff.lowFrequencies N) a.val.val-a.val.val = -fourierTail w N a.val.val := by
    apply Subtype.ext
    funext k
    simp only [sub_val,neg_val,truncate_apply,Coeff.mem_lowFrequencies,fourierTail_apply]
    by_cases hk : k.natAbs < N
    · rw [if_pos hk,if_neg (by omega),sub_self,neg_zero]
    · rw [if_neg hk,if_pos (by omega),zero_sub]
  rw [he,norm_neg]
  exact ht

end NLS.WeightedCoeff
