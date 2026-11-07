import NLS.SequenceSpaces.WeightedSingle
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! Exact weighted supremum norm of a nonzero symmetric two-mode
potential, with no estimate replacing the actual norm. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff

def twoSymmetricInfinityModes (w : Weight) (m : ℤ) : WeightedCoeff w ⊤ :=
  single w m 1+single w (-m) 1

theorem twoSymmetricInfinityModes_apply (w : Weight) (m k : ℤ) :
    (twoSymmetricInfinityModes w m).val k = (if k=m then 1 else 0)+(if k=-m then 1 else 0) := by
  simp only [twoSymmetricInfinityModes, add_val, single_val,Pi.single_apply]

theorem norm_twoSymmetricInfinityModes (w : Weight) (hw : ∀ k, w (-k)=w k)
    (m : ℤ) (hm : m ≠ 0) : ‖twoSymmetricInfinityModes w m‖ = w m := by
  have hneg : m ≠ -m := by omega
  have hraw (k : ℤ) := twoSymmetricInfinityModes_apply w m k
  have hmval : (twoSymmetricInfinityModes w m).val m = 1 := by
    rw [hraw m, if_pos rfl, if_neg hneg, add_zero]
  apply le_antisymm
  · change ‖weightEquiv w ⊤ (twoSymmetricInfinityModes w m)‖ ≤ w m
    apply lp.norm_le_of_forall_le (w.positive m).le
    intro k
    rw [weightEquiv_apply,hraw k]
    by_cases hk : k=m
    · subst k
      simp only [ite_true,if_neg hneg,add_zero,mul_one,Complex.norm_real,
        Real.norm_of_nonneg (w.positive m).le,le_refl]
    by_cases hk' : k=-m
    · subst k
      simp only [if_neg (Ne.symm hneg),ite_true,zero_add,mul_one,Complex.norm_real,
        hw,Real.norm_of_nonneg (w.positive m).le,le_refl]
    · simp only [if_neg hk,if_neg hk',zero_add,mul_zero,norm_zero]
      exact (w.positive m).le
  · have h := lp.norm_apply_le_norm (by simp : (⊤:ℝ≥0∞) ≠ 0)
      (weightEquiv w ⊤ (twoSymmetricInfinityModes w m)) m
    simpa only [weightEquiv_apply,hmval,mul_one,Complex.norm_real,
      Real.norm_of_nonneg (w.positive m).le,← norm_eq] using h

theorem tsum_twoSymmetricInfinityModes_mul (w : Weight) (m a : ℤ) (g : ℤ → ℂ) :
    (∑' k : ℤ, (twoSymmetricInfinityModes w m).val (a-k)*g k) = g (a-m)+g (a+m) := by
  have he : (fun k : ℤ => (twoSymmetricInfinityModes w m).val (a-k)*g k) =
      Pi.single (a-m) (g (a-m))+Pi.single (a+m) (g (a+m)) := by
    funext k
    rw [twoSymmetricInfinityModes_apply]
    have h₁ : a-k=m ↔ k=a-m := by omega
    have h₂ : a-k=-m ↔ k=a+m := by omega
    simp only [h₁,h₂,add_mul]
    congr 1
    · by_cases hk : k=a-m
      · subst k
        simp only [ite_true,one_mul,Pi.single_eq_same]
      · simp only [if_neg hk,zero_mul,Pi.single_apply]
    · by_cases hk : k=a+m
      · subst k
        simp only [ite_true,one_mul,Pi.single_eq_same]
      · simp only [if_neg hk,zero_mul,Pi.single_apply]
  rw [he]
  change (∑' k : ℤ, ((Pi.single (a-m) (g (a-m)) : ℤ → ℂ) k+(Pi.single (a+m) (g (a+m)) : ℤ → ℂ) k))=_
  simp only [Pi.single_apply]
  exact
    ((hasSum_ite_eq (a-m) (g (a-m))).add (hasSum_ite_eq (a+m) (g (a+m)))).tsum_eq

end NLS.WeightedCoeff
