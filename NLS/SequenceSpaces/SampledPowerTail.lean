import NLS.SequenceSpaces.FourierTail
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Power sums of sampled Fourier tails

Injective frequency sampling cannot increase a nonnegative coefficient
power sum. A high-frequency sample therefore has a convergent power tail
bounded by the exact Fourier remainder norm.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An injectively sampled tail has power sum bounded by the source Fourier-tail norm. -/
theorem sampled_fourierTail_power (hp : p ≠ ⊤) (a : Coeff p) (f : ℤ → ℤ)
    (hf : Function.Injective f) (N M : ℕ)
    (hfreq : ∀ n : ℤ, N ≤ n.natAbs → M ≤ (f n).natAbs) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then ‖a (f n)‖^p.toReal else 0) ∧
      (∑' n : ℤ, if N ≤ n.natAbs then ‖a (f n)‖^p.toReal else 0) ≤ ‖fourierTail M a‖^p.toReal := by
  have hP : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  have hs := (lp.memℓp (fourierTail M a)).summable hP
  have hcomp := hs.comp_injective hf
  have hnonneg (n : ℤ) : 0 ≤ (if N ≤ n.natAbs then ‖a (f n)‖^p.toReal else 0) := by
    split_ifs <;> positivity
  have hpoint (n : ℤ) : (if N ≤ n.natAbs then ‖a (f n)‖^p.toReal else 0) ≤
      ‖fourierTail M a (f n)‖^p.toReal := by
    split_ifs with hn
    · rw [fourierTail_apply, if_pos (hfreq n hn)]
    · positivity
  have hactual := hcomp.of_nonneg_of_le hnonneg hpoint
  refine ⟨hactual, (hactual.tsum_le_tsum hpoint hcomp).trans ?_⟩
  rw [lp.norm_rpow_eq_tsum hP]
  exact tsum_comp_le_tsum_of_inj hs (fun _ => by positivity) hf

end NLS.Coeff
