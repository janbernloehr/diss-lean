import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Strictly different power growth cannot be uniformly bounded -/
open Filter Topology
namespace NLS

/-- A positive larger power eventually exceeds a smaller power plus a constant. -/
theorem not_forall_nat_rpow_growth {a b δ C K : ℝ}
    (ha : 0 < a) (hab : a < b) (hδ : 0 < δ) (hK : 0 ≤ K) :
    ¬ ∀ n : ℕ, δ*(n : ℝ)^b ≤ C*(n : ℝ)^a+K := by
  intro h
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^(b-a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  obtain ⟨n,hn,hpow⟩ := ((eventually_ge_atTop (1 : ℕ)).and
    (ht.eventually (eventually_gt_atTop ((C+K)/δ)))).exists
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hna : (1 : ℝ) ≤ (n : ℝ)^a := Real.one_le_rpow hn1 ha.le
  have hlarge : C+K < δ*(n : ℝ)^(b-a) := by
    have hh := (div_lt_iff₀ hδ).mp hpow
    linarith
  have hmul := mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hn0 a)
  have he : (n : ℝ)^(b-a)*(n : ℝ)^a = (n : ℝ)^b := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have hbound := h n
  nlinarith [mul_le_mul_of_nonneg_left hna hK]

end NLS
