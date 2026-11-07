import NLS.SequenceSpaces.FourierRealZeroTruncation
import NLS.SequenceSpaces.WeightedDomination

/-! Symmetric finite replacements stay in the original physical real
zero-mode space and converge in every finite weighted Banach exponent. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Pointwise raw norm comparison controls the actual physical weighted norm. -/
theorem fourierRealZero_norm_le_of_coordinates (w : Weight)
    (a b : fourierRealZeroSubmodule w p)
    (h : ∀ k : ℤ, ‖a.val.val.val k‖ ≤ ‖b.val.val.val k‖) : ‖a‖ ≤ ‖b‖ := by
  obtain ⟨c,hc,hn⟩ := exists_of_norm_le w b.val.val a.val.val.val 1 (by norm_num)
    (fun k => by simpa only [one_mul] using h k)
  have he : c=a.val.val := Subtype.ext (funext hc)
  change ‖a.val.val‖ ≤ ‖b.val.val‖
  simpa only [he,one_mul] using hn

/-- Replace the symmetric finite head by the target, retaining the old tail. -/
def fourierRealZeroReplace (w : Weight) (N : ℕ) (a b : fourierRealZeroSubmodule w p) :
    fourierRealZeroSubmodule w p :=
  fourierRealZeroTruncate w N b+(a-fourierRealZeroTruncate w N a)

theorem fourierRealZeroReplace_apply (w : Weight) (N : ℕ) (a b : fourierRealZeroSubmodule w p) (k : ℤ) :
    (fourierRealZeroReplace w N a b).val.val.val k=if k.natAbs<N then b.val.val.val k else a.val.val.val k := by
  change (fourierRealZeroTruncate w N b).val.val.val k+
    (a.val.val.val k-(fourierRealZeroTruncate w N a).val.val.val k)= _
  rw [fourierRealZeroTruncate_apply,fourierRealZeroTruncate_apply]
  split_ifs <;> ring

theorem norm_fourierRealZeroReplace_sub_le (w : Weight) (N : ℕ) (a b : fourierRealZeroSubmodule w p) :
    ‖fourierRealZeroReplace w N a b-a‖ ≤ ‖b-a‖ := by
  apply fourierRealZero_norm_le_of_coordinates
  intro k
  change ‖(fourierRealZeroReplace w N a b).val.val.val k-a.val.val.val k‖ ≤ ‖b.val.val.val k-a.val.val.val k‖
  rw [fourierRealZeroReplace_apply]
  split_ifs
  · exact le_rfl
  · simp only [sub_self,norm_zero,norm_nonneg]

/-- The same replacements converge in the FULL actual physical norm. -/
theorem tendsto_fourierRealZeroReplace (hp : p ≠ ⊤) (w : Weight) (a b : fourierRealZeroSubmodule w p) :
    Tendsto (fun N : ℕ => fourierRealZeroReplace w N a b) atTop (𝓝 b) := by
  have h := (tendsto_fourierRealZeroTruncate hp w b).add
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).sub
      (tendsto_fourierRealZeroTruncate hp w a))
  simpa only [fourierRealZeroReplace,sub_self,add_zero] using h

end NLS.WeightedCoeff
