import NLS.SequenceSpaces.PositiveScalarExtension
import Mathlib.Topology.Instances.Real.Lemmas

/-! The literal odd extension of positive real frequency modes. -/
noncomputable section
namespace NLS.LpSequence

def oddPositiveFrequency (f : ℕ+ → ℝ) (k : ℤ) : ℝ :=
  (k.sign:ℝ)*(if hk : k=0 then 0 else f ⟨k.natAbs,Int.natAbs_pos.mpr hk⟩)

theorem oddPositiveFrequency_zero (f : ℕ+ → ℝ) : oddPositiveFrequency f 0=0 := by
  simp [oddPositiveFrequency]

theorem oddPositiveFrequency_neg (f : ℕ+ → ℝ) (k : ℤ) :
    oddPositiveFrequency f (-k)=-oddPositiveFrequency f k := by
  by_cases hk : k=0
  · subst k
    simp [oddPositiveFrequency]
  · simp only [oddPositiveFrequency,dif_neg hk,dif_neg (neg_ne_zero.mpr hk),
      Int.natAbs_neg,Int.sign_neg,Int.cast_neg,neg_mul]

theorem oddPositiveFrequency_positive (f : ℕ+ → ℝ) (n : ℕ+) :
    oddPositiveFrequency f (n:ℤ)=f n := by
  have hn : (0:ℤ)<(n:ℤ) := by exact_mod_cast n.pos
  simp only [oddPositiveFrequency,dif_neg (ne_of_gt hn),Int.sign_eq_one_of_pos hn,
    Int.cast_one,one_mul,Int.natAbs_natCast]
  rfl

theorem continuous_oddPositiveFrequency_family {X : Type*} [TopologicalSpace X]
    (f : X → ℕ+ → ℝ) (hf : ∀ n, Continuous (fun x => f x n)) (k : ℤ) :
    Continuous (fun x => oddPositiveFrequency (f x) k) := by
  by_cases hk : k=0
  · subst k
    simpa only [oddPositiveFrequency_zero] using (continuous_const : Continuous (fun _ : X => (0:ℝ)))
  · simp only [oddPositiveFrequency,dif_neg hk]
    exact continuous_const.mul (hf _)

end NLS.LpSequence
