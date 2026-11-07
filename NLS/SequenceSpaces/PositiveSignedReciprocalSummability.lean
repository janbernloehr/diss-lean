import NLS.SequenceSpaces.UniformHolderSums
import NLS.SequenceSpaces.CompactPuncturedKernel

/-! Absolute convergence on positive indices from a two-sided
reciprocal tail bound and two actual full-l2 coefficient sequences.
Finite low indices are unrestricted; the diagonal is explicitly zero. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal Classical
namespace NLS.Coeff

theorem summable_norm_positive_of_signed_reciprocal_tail
    (a d : Coeff 2) (n : ℕ+) (u : ℕ+ → ℂ) (hdiag : u n = 0)
    (K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ m : ℕ+, K < (m:ℕ) → m ≠ n → ‖u m‖ ≤
      C*(‖a ((m:ℕ):ℤ)‖+‖d ((m:ℕ):ℤ)‖)*
        (1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))) :
    Summable (fun m => ‖u m‖) := by
  let κ := puncturedLattice 2 (by norm_num : 1 < (2:ℝ≥0∞))
  let b := shift ((n:ℕ):ℤ) κ
  let e := shift (-((n:ℕ):ℤ)) κ
  have hc : (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal := Real.HolderConjugate.two_two
  have hsZ : Summable (fun k : ℤ => (‖a k‖+‖d k‖)*(‖b k‖+‖e k‖)) := by
    convert (((lp.tsum_mul_le_mul_norm hc a b).1.add (lp.tsum_mul_le_mul_norm hc a e).1).add
      ((lp.tsum_mul_le_mul_norm hc d b).1.add (lp.tsum_mul_le_mul_norm hc d e).1)) using 1
    funext k
    ring
  have hinj : Function.Injective (fun m : ℕ+ => ((m:ℕ):ℤ)) := by
    intro i j h
    apply PNat.coe_injective
    exact Int.ofNat.inj h
  have hs := (hsZ.comp_injective hinj).mul_left C
  let v : ℕ+ → ℂ := fun m => if K < (m:ℕ) then u m else 0
  have hv : Summable (fun m => ‖v m‖) := by
    apply hs.of_nonneg_of_le (fun m => norm_nonneg _) _
    intro m
    change ‖v m‖ ≤ C*((‖a ((m:ℕ):ℤ)‖+‖d ((m:ℕ):ℤ)‖)*(‖b ((m:ℕ):ℤ)‖+‖e ((m:ℕ):ℤ)‖))
    by_cases hmK : K < (m:ℕ)
    · dsimp only [v]
      rw [if_pos hmK]
      by_cases hmn : m = n
      · subst m
        rw [hdiag,norm_zero]
        positivity
      · have hpos : ((m:ℕ):ℤ) ≠ ((n:ℕ):ℤ) := by exact_mod_cast hmn
        have hneg : ((m:ℕ):ℤ) ≠ -((n:ℕ):ℤ) := by have := n.pos; have := m.pos; omega
        have hb : ‖b ((m:ℕ):ℤ)‖+‖e ((m:ℕ):ℤ)‖ =
            1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ) := by
          rw [norm_shift_puncturedLattice_apply (by norm_num : 1 < (2:ℝ≥0∞)),
            norm_shift_puncturedLattice_apply (by norm_num : 1 < (2:ℝ≥0∞)),if_neg hpos,if_neg hneg]
          push_cast
          rw [sub_neg_eq_add,abs_sub_comm,abs_of_nonneg (by positivity : 0 ≤ ((m:ℕ):ℝ)+(n:ℕ)),add_comm ((m:ℕ):ℝ)]
          simp only [one_div]
        simpa only [hb,mul_assoc] using hu m hmK hmn
    · simp only [v,if_neg hmK,norm_zero]
      positivity
  have hfinite : {m : ℕ+ | (m:ℕ) ≤ K}.Finite :=
    (Set.finite_Iic K).preimage (fun _ _ _ _ h => PNat.coe_injective h)
  apply hv.congr_cofinite
  filter_upwards [hfinite.compl_mem_cofinite] with m hm
  have hmK : K < (m:ℕ) := by
    change ¬ (m:ℕ) ≤ K at hm
    exact lt_of_not_ge hm
  simp only [v,if_pos hmK]

end NLS.Coeff
