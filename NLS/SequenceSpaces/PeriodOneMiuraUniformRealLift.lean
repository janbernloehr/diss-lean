import NLS.SequenceSpaces.PeriodOneMiuraRealLift

/-!
# One real shifted Miura chart for an entire bounded family

The energy translation is selected before the potential. Every real
H-minus-one potential in the specified ball has a real L2 lift at that same
translation, and all the lifts have one common L2 norm bound.
-/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS

/-- One arbitrarily large positive energy translation and one L2 bound
serve every real potential in an entire specified H-minus-one ball. -/
theorem exists_uniform_real_periodOneMiura_shift {B : ℝ} (hB : 0 ≤ B) (A : ℝ) :
    ∃ c : ℝ, 0 < c ∧ A < c ∧ ∀ q : PeriodOneHminusOne, ‖q‖ ≤ B →
      IsRealPeriodOneHminusOne q → ∃ u : PeriodOneRealL2,
        ‖u.val‖ ≤ 4*B+1+c ∧
        periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 ((c:ℂ)^2)) := by
  obtain ⟨M,hM⟩ := exists_real_periodOneShiftedMiura_on_bounded_ball hB
  obtain ⟨N,hN⟩ := exists_nat_gt (2*max A 0+2)
  let m := max M N
  let c : ℝ := ((m:ℝ)+1)/2
  have hmN : (N:ℝ) ≤ m := by exact_mod_cast (le_max_right M N)
  have hc : 0 < c := by dsimp [c]; positivity
  have hAc : A < c := by dsimp [c]; linarith [le_max_left A 0]
  refine ⟨c,hc,hAc,fun q hq hreal => ?_⟩
  obtain ⟨v,hv,hsolve⟩ := hM m (le_max_left _ _) q hq hreal
  let u : Coeff 2 := v.val+lp.single 2 0 (c:ℂ)
  have hureal : ∀ n : ℤ, u (-n) = conj (u n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [u,lp.coeFn_add,Pi.add_apply,lp.single_apply,Pi.single_apply,
        neg_zero,if_true,map_add,conj_ofReal]
      exact congrArg (fun a : ℂ => a+(c:ℂ)) (v.property 0)
    · have hnn : -n ≠ 0 := neg_ne_zero.mpr hn
      simpa only [u,lp.coeFn_add,Pi.add_apply,lp.single_apply,Pi.single_apply,
        if_neg hn,if_neg hnn,add_zero,map_add,map_zero] using v.property n
  refine ⟨⟨u,hureal⟩,?_,?_⟩
  · have hnorm := norm_add_le v.val (lp.single 2 0 (c:ℂ))
    rw [lp.norm_single (by norm_num),Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc] at hnorm
    exact hnorm.trans (by linarith only [hv])
  · have hs := periodOneMiura_shift m v.val
    have hs' := hs.trans (congrArg (fun a : PeriodOneHminusOne => a+periodOneL2Inclusion
      (lp.single 2 0 ((((m:ℝ)+1:ℝ)/2:ℂ)^2))) hsolve)
    simpa only [u,c,ofReal_div,ofReal_ofNat] using hs'

end NLS
