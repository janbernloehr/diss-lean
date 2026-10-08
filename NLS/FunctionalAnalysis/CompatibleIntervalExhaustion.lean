import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Gluing compatible curves on an exhaustion of the real line -/
noncomputable section
open Set
namespace NLS.FunctionalAnalysis

/-- The positive radii of the closed interval exhaustion. -/
def exhaustionRadius (n : ℕ) : ℝ := (n : ℝ)+1

theorem exhaustionRadius_pos (n : ℕ) : 0 < exhaustionRadius n := by
  unfold exhaustionRadius
  positivity

theorem exhaustionRadius_mono {m n : ℕ} (h : m ≤ n) : exhaustionRadius m ≤ exhaustionRadius n := by
  unfold exhaustionRadius
  have h' : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr h
  exact add_le_add h' le_rfl

/-- Every real time lies in the interior of its chosen exhaustion interval. -/
theorem mem_Ioo_exhaustionRadius (time : ℝ) :
    time ∈ Ioo (-exhaustionRadius (Nat.ceil |time|)) (exhaustionRadius (Nat.ceil |time|)) := by
  have h : |time| < exhaustionRadius (Nat.ceil |time|) := by
    have hceil : |time| ≤ (Nat.ceil |time| : ℝ) := Nat.le_ceil _
    dsimp [exhaustionRadius]
    linarith
  exact abs_lt.mp h

/-- Every closed finite interval is contained in one exhaustion interval. -/
theorem exists_exhaustionRadius_cover (a b : ℝ) :
    ∃ n : ℕ, -exhaustionRadius n ≤ a ∧ b ≤ exhaustionRadius n := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max |a| |b|)
  refine ⟨n,?_,?_⟩ <;> dsimp [exhaustionRadius]
  · have ha := (le_max_left |a| |b|).trans_lt hn
    linarith [neg_abs_le a]
  · have hb := (le_max_right |a| |b|).trans_lt hn
    linarith [le_abs_self b]

/-- Choose a curve on an interval containing the requested time. -/
def exhaustionCurve {E : Type*} (u : ℕ → ℝ → E) (time : ℝ) : E := u (Nat.ceil |time|) time

/-- Compatibility makes the glued curve equal to each original curve on
its whole closed interval, including both boundary times. -/
theorem exhaustionCurve_eqOn {E : Type*} (u : ℕ → ℝ → E)
    (hcomp : ∀ m n : ℕ, m ≤ n → EqOn (u m) (u n) (Icc (-exhaustionRadius m) (exhaustionRadius m)))
    (n : ℕ) : EqOn (exhaustionCurve u) (u n) (Icc (-exhaustionRadius n) (exhaustionRadius n)) := by
  intro time ht
  let m := Nat.ceil |time|
  have hm : time ∈ Icc (-exhaustionRadius m) (exhaustionRadius m) :=
    ⟨(mem_Ioo_exhaustionRadius time).1.le,(mem_Ioo_exhaustionRadius time).2.le⟩
  exact (hcomp m (max m n) (le_max_left _ _) hm).trans
    (hcomp n (max m n) (le_max_right _ _) ht).symm

end NLS.FunctionalAnalysis
