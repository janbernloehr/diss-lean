import NLS.SequenceSpaces.RealActionWeightedMembership
import NLS.SequenceSpaces.Reflection

/-! # Positive modes determine weighted regularity for even actions

An even quadratic action sequence controls the two negative coordinates
by the positive pair radius. The zero mode is a finite contribution.
-/
noncomputable section
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem abs_pair_le_of_radius_eq (x y u v : ℝ) (h : (x^2+y^2)/2 = (u^2+v^2)/2) :
    |x| ≤ |u|+|v| ∧ |y| ≤ |u|+|v| := by
  have hprod := mul_nonneg (abs_nonneg u) (abs_nonneg v)
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mp
    nlinarith [sq_abs x,sq_abs u,sq_abs v,sq_nonneg y]
  · apply (sq_le_sq₀ (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mp
    nlinarith [sq_abs y,sq_abs u,sq_abs v,sq_nonneg x]

private theorem norm_neg_mem {f : ℤ → ℝ} (hp : p ≠ ⊤) (hf : Memℓp f p) :
    Memℓp (fun n => ‖f (-n)‖) p := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp
  exact memℓp_gen ((Equiv.neg ℤ).summable_iff.mpr (hf.norm.summable hp0))

/-- Positive weighted membership suffices when the real pair actions and
weight are even. No individual action has to be nonzero. -/
theorem weighted_mem_of_positive_of_even_action (hp : p ≠ ⊤) (w : ℤ → ℝ)
    (hw : ∀ n, w (-n) = w n) (z : RealCoeff p × RealCoeff p)
    (heven : ∀ n, pairAction z (-n) = pairAction z n)
    (hx : Memℓp (fun n => if 0 < n then w n*z.1 n else 0) p)
    (hy : Memℓp (fun n => if 0 < n then w n*z.2 n else 0) p) :
    Memℓp (fun n => w n*z.1 n) p ∧ Memℓp (fun n => w n*z.2 n) p := by
  let f : ℤ → ℝ := fun n => if 0 < n then w n*z.1 n else 0
  let g : ℤ → ℝ := fun n => if 0 < n then w n*z.2 n else 0
  have hf : Memℓp (fun n => ‖f (-n)‖) p := norm_neg_mem hp hx
  have hg : Memℓp (fun n => ‖g (-n)‖) p := norm_neg_mem hp hy
  let c : RealCoeff p := lp.single p 0 (‖w 0*z.1 0‖+‖w 0*z.2 0‖)
  have hmajor : Memℓp (fun n => (‖f n‖+‖g n‖)+(‖f (-n)‖+‖g (-n)‖)+c n) p := ((hx.norm.add hy.norm).add (hf.add hg)).add (lp.memℓp c)
  have hb (n : ℤ) : ‖w n*z.1 n‖ ≤ (‖f n‖+‖g n‖)+(‖f (-n)‖+‖g (-n)‖)+c n ∧
      ‖w n*z.2 n‖ ≤ (‖f n‖+‖g n‖)+(‖f (-n)‖+‖g (-n)‖)+c n := by
    by_cases hn : 0 < n
    · simp only [f,g,if_pos hn,if_neg (show ¬0 < -n by omega),norm_zero,
        c,lp.single_apply,Pi.single_eq_of_ne (ne_of_gt hn),add_zero]
      exact ⟨le_add_of_nonneg_right (norm_nonneg _),le_add_of_nonneg_left (norm_nonneg _)⟩
    · by_cases hz : n = 0
      · subst n
        simp only [f,g,lt_self_iff_false,if_false,norm_zero,neg_zero,c,lp.single_apply,
          Pi.single_eq_same,zero_add]
        exact ⟨le_add_of_nonneg_right (norm_nonneg _),le_add_of_nonneg_left (norm_nonneg _)⟩
      · have hneg : 0 < -n := by omega
        obtain ⟨hx',hy'⟩ := abs_pair_le_of_radius_eq (z.1 n) (z.2 n) (z.1 (-n)) (z.2 (-n))
          (heven n).symm
        simp only [f,g,if_neg hn,if_pos hneg,norm_zero,zero_add,c,lp.single_apply,
          Pi.single_eq_of_ne hz,add_zero,hw,norm_mul,Real.norm_eq_abs,← mul_add]
        exact ⟨mul_le_mul_of_nonneg_left hx' (abs_nonneg _),
          mul_le_mul_of_nonneg_left hy' (abs_nonneg _)⟩
  exact ⟨hmajor.mono (fun n => (hb n).1),hmajor.mono (fun n => (hb n).2)⟩

end NLS.RealCoeff
