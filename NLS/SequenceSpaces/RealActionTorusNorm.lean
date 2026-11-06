import NLS.SequenceSpaces.RealActionRotationOrbit

/-! # A uniform norm bound on action tori

Every point of a real action torus has norm at most twice the norm of
any fixed point. The bound is independent of the number of rotated modes.
-/
noncomputable section
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Equal actions give a uniform bound in the full product norm. -/
theorem norm_le_two_mul_of_pairAction_eq (z w : RealCoeff p × RealCoeff p)
    (h : ∀ n, pairAction w n = pairAction z n) : ‖w‖ ≤ 2*‖z‖ := by
  let b : RealCoeff p := lp.toNorm z.1+lp.toNorm z.2
  have hb : ‖b‖ ≤ 2*‖z‖ := by
    calc
      ‖b‖ ≤ ‖lp.toNorm z.1‖+‖lp.toNorm z.2‖ := norm_add_le _ _
      _ = ‖z.1‖+‖z.2‖ := by rw [lp.norm_toNorm,lp.norm_toNorm]
      _ ≤ 2*‖z‖ := by nlinarith [norm_fst_le z,norm_snd_le z]
  have hc (n : ℤ) : ‖w.1 n‖ ≤ ‖b n‖ ∧ ‖w.2 n‖ ≤ ‖b n‖ := by
    change |w.1 n| ≤ |‖z.1 n‖+‖z.2 n‖| ∧ |w.2 n| ≤ |‖z.1 n‖+‖z.2 n‖|
    rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact abs_coordinates_le_of_pairAction_eq z w n (h n)
  rw [Prod.norm_def]
  exact max_le
    ((lp.norm_mono (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p)))
      (fun n => (hc n).1)).trans hb)
    ((lp.norm_mono (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p)))
      (fun n => (hc n).2)).trans hb)

end NLS.RealCoeff
