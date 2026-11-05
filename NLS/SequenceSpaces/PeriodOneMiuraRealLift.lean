import NLS.SequenceSpaces.PeriodOneHminusOneRealDensity
import NLS.SequenceSpaces.ConjugateReflection
import NLS.SequenceSpaces.PeriodOneMiuraShift
import NLS.ComplexAnalysis.SmallQuadraticInverse

/-! Real shifted Miura lifts for every real unit-period H-minus-one
potential, with the positive spectral translation chosen arbitrarily large. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS

def coeffRealConjugation (v : Coeff 2) : Coeff 2 := star (Coeff.reflection v)

theorem coeffRealConjugation_apply (v : Coeff 2) (n : ℤ) :
    coeffRealConjugation v n = conj (v (-n)) := by
  change star (v (-n)) = conj (v (-n))
  rw [Complex.star_def]

theorem norm_coeffRealConjugation (v : Coeff 2) : ‖coeffRealConjugation v‖ = ‖v‖ := by
  rw [coeffRealConjugation,norm_star,Coeff.reflection.norm_map]

theorem periodOneMassSymbol_conjugate (m : ℕ) (n : ℤ) :
    conj (periodOneMassSymbol m (-n)) = periodOneMassSymbol m n := by
  simp [periodOneMassSymbol,map_ofNat]

theorem periodOneShiftedMiura_realConjugation (m : ℕ) (v : Coeff 2) :
    periodOneShiftedMiura m (coeffRealConjugation v) =
      WeightedCoeff.conjugateReflection (Weight.sobolev (-1)) (Weight.sobolev_neg (-1))
        (periodOneShiftedMiura m v) := by
  apply Subtype.ext
  funext n
  rw [periodOneShiftedMiura_apply,WeightedCoeff.conjugateReflection_apply,
    periodOneShiftedMiura_apply,map_add,map_mul,periodOneMassSymbol_conjugate,
    WeightedCoeff.conj_tsum_convolution]
  simp only [coeffRealConjugation_apply]

theorem periodOne_realConjugation_eq_self (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) :
    WeightedCoeff.conjugateReflection (Weight.sobolev (-1)) (Weight.sobolev_neg (-1)) q = q := by
  apply Subtype.ext
  funext n
  rw [WeightedCoeff.conjugateReflection_apply]
  simpa only [neg_neg] using (hq (-n)).symm

/-- Small shifted Miura solutions in the same specified ball are unique. -/
theorem periodOneShiftedMiura_injective_on_ball (m : ℕ) (R : ℝ)
    (hsmall : ‖periodOneMassKernel m‖*R ≤ 1/4)
    (u v : Coeff 2) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R)
    (h : periodOneShiftedMiura m u = periodOneShiftedMiura m v) : u = v := by
  have he : u+periodOneResolvedProduct m u u = v+periodOneResolvedProduct m v v := by
    rw [← periodOneMassInverse_shiftedMiura,← periodOneMassInverse_shiftedMiura,h]
  have hd : u-v = -(periodOneResolvedProduct m u u-periodOneResolvedProduct m v v) := by
    calc
      u-v = (u+periodOneResolvedProduct m u u)-(v+periodOneResolvedProduct m v v)-
          (periodOneResolvedProduct m u u-periodOneResolvedProduct m v v) := by abel
      _ = _ := by rw [he,sub_self,zero_sub]
  have hb := ComplexAnalysis.quadratic_difference_bound (periodOneResolvedProduct m)
    (norm_nonneg (periodOneMassKernel m)) (norm_periodOneResolvedProduct_le m) hu hv
  rw [← norm_neg,← hd] at hb
  have hn : ‖u-v‖ = 0 := by
    have hc := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (u-v))
    nlinarith [norm_nonneg (u-v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- One mass cutoff serves every real potential in a specified full H-minus-one ball. -/
theorem exists_real_periodOneShiftedMiura_on_bounded_ball {B : ℝ} (hB : 0 ≤ B) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ q : PeriodOneHminusOne, ‖q‖ ≤ B →
      IsRealPeriodOneHminusOne q → ∃ v : PeriodOneRealL2,
        ‖v.val‖ ≤ 4*B+1 ∧ periodOneShiftedMiura m v.val = q := by
  let R := 4*B+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hlim : Tendsto (fun m => ‖periodOneMassKernel m‖*R) atTop (𝓝 0) := by
    simpa only [norm_zero,zero_mul] using tendsto_periodOneMassKernel_zero.norm.mul_const R
  obtain ⟨M₁,hM₁⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)))
  obtain ⟨M₂,hM₂⟩ := exists_periodOneMiuraCharts_on_bounded_ball hB
  refine ⟨max M₁ M₂,fun m hm q hq hreal => ?_⟩
  obtain ⟨v,hv,hsolve,_⟩ := hM₂ m ((le_max_right _ _).trans hm) q hq
  have hsolve' : periodOneShiftedMiura m (coeffRealConjugation v) = q := by
    rw [periodOneShiftedMiura_realConjugation,hsolve,periodOne_realConjugation_eq_self q hreal]
  have heq : v = coeffRealConjugation v := periodOneShiftedMiura_injective_on_ball m R
    (hM₁ m ((le_max_left _ _).trans hm)).le v (coeffRealConjugation v)
      hv (by rw [norm_coeffRealConjugation]; exact hv) (hsolve.trans hsolve'.symm)
  have hvreal : ∀ n : ℤ, v (-n) = conj (v n) := by
    intro n
    have hh := congrArg (fun a : Coeff 2 => a (-n)) heq
    simpa only [coeffRealConjugation_apply,neg_neg] using hh
  exact ⟨⟨v,hvreal⟩,hv,hsolve⟩

/-- Every real H-minus-one potential has a real L2 Miura lift after a
positive energy translation whose square root exceeds any specified bound. -/
theorem exists_real_periodOneMiura_shift (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (A : ℝ) :
    ∃ c : ℝ, 0 < c ∧ A < c ∧ ∃ u : PeriodOneRealL2,
      periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 ((c:ℂ)^2)) := by
  obtain ⟨M,hM⟩ := exists_real_periodOneShiftedMiura_on_bounded_ball (norm_nonneg q)
  obtain ⟨N,hN⟩ := exists_nat_gt (2*max A 0+2)
  let m := max M N
  obtain ⟨v,_,hv⟩ := hM m (le_max_left _ _) q le_rfl hq
  let c : ℝ := ((m:ℝ)+1)/2
  have hmN : (N:ℝ) ≤ m := by exact_mod_cast (le_max_right M N)
  have hc : 0 < c := by dsimp [c]; positivity
  have hAc : A < c := by dsimp [c]; linarith [le_max_left A 0]
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
  refine ⟨c,hc,hAc,⟨u,hureal⟩,?_⟩
  have hs := periodOneMiura_shift m v.val
  have hs' := hs.trans (congrArg (fun a : PeriodOneHminusOne => a+periodOneL2Inclusion
    (lp.single 2 0 ((((m:ℝ)+1:ℝ)/2:ℂ)^2))) hv)
  simpa only [u,c,ofReal_div,ofReal_ofNat] using hs'

/-- The spectral translation may always be chosen to avoid zero square-root
energy at a prescribed complex physical spectral parameter. -/
theorem exists_real_periodOneMiura_shift_avoiding (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (lambda : ℂ) :
    ∃ c : ℝ, 0 < c ∧ ∃ u : PeriodOneRealL2,
      periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 ((c:ℂ)^2)) ∧
        lambda+(c:ℂ)^2 ≠ 0 := by
  obtain ⟨c,hc,hbig,u,hu⟩ := exists_real_periodOneMiura_shift q hq (‖lambda‖+1)
  refine ⟨c,hc,u,hu,fun he => ?_⟩
  have hn := congrArg norm (eq_neg_of_add_eq_zero_left he)
  rw [norm_neg,norm_pow,norm_real,Real.norm_eq_abs,abs_of_pos hc] at hn
  nlinarith [norm_nonneg lambda]

end NLS
