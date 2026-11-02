import NLS.KdV.ClassicalTwoWeightedNormalizedCoefficients

/-! # Actual summable residue coefficients of the normalized entire family

Two index weights and Hilbert Holder multiplication construct the literal
positive coefficients m*(R e_n)_m in l1, analytically in the potential.
The same coefficients give the exact critical resolvent expansion away
from the selected critical energies.
-/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

def classicalHillNormalizedResidues
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) : NLS.Coeff 1 :=
  NLS.Coeff.holderProduct NLS.Coeff.positiveReciprocalHilbert
    ((n : ℂ)^2 • Q q (lp.single 2 (n : ℤ) 1))

theorem classicalHillNormalizedResidues_positive
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : NLS.LinearVolterra.Curve ℂ)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q q (lp.single 2 j 1)) m) (n k : ℕ+) :
    classicalHillNormalizedResidues Q n q (k : ℤ) =
      (k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ) := by
  have hn : (0 : ℤ) < n := by exact_mod_cast n.pos
  have hk : (0 : ℤ) < k := by exact_mod_cast k.pos
  have hwn : NLS.Coeff.positiveIndexWeight (n : ℤ) = (n : ℂ) := by
    simp only [NLS.Coeff.positiveIndexWeight,if_pos hn,Int.cast_natCast]
  have hwk : NLS.Coeff.positiveIndexWeight (k : ℤ) = (k : ℂ) := by
    simp only [NLS.Coeff.positiveIndexWeight,if_pos hk,Int.cast_natCast]
  have he := hcompat (k : ℤ) (n : ℤ)
  rw [hwn,hwk] at he
  simp only [classicalHillNormalizedResidues,NLS.Coeff.holderProduct_apply,
    NLS.Coeff.positiveReciprocalHilbert_apply,if_pos hk,Int.cast_natCast,
    lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,← he]
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast k.ne_zero
  field_simp

theorem classicalHillNormalizedResidues_nonpositive
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (m : ℤ) (hm : m ≤ 0) :
    classicalHillNormalizedResidues Q n q m = 0 := by
  simp only [classicalHillNormalizedResidues,NLS.Coeff.holderProduct_apply,
    NLS.Coeff.positiveReciprocalHilbert_apply,if_neg (by omega : ¬ 0 < m),zero_mul]

theorem classicalHillNormalizedResidues_analytic
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (V : Set (NLS.LinearVolterra.Curve ℂ)) (hQa : AnalyticOnNhd ℂ Q V) (n : ℕ+) :
    AnalyticOnNhd ℂ (classicalHillNormalizedResidues Q n) V := by
  intro q hq
  have hc : AnalyticAt ℂ (fun x : NLS.LinearVolterra.Curve ℂ =>
      (n : ℂ)^2 • Q x (lp.single 2 (n : ℤ) 1)) q := by
    apply (analyticAt_const (v := (n : ℂ)^2)).smul
    simpa only [Function.comp_def] using!
      ((ContinuousLinearMap.apply ℂ (NLS.Coeff 2) (lp.single 2 (n : ℤ) 1)).analyticAt (Q q)).comp
        (f := Q) (hQa q hq)
  simpa only [classicalHillNormalizedResidues,Function.comp_def] using!
    ((NLS.Coeff.holderProduct (q := 1) NLS.Coeff.positiveReciprocalHilbert).analyticAt _).comp
      (f := fun x : NLS.LinearVolterra.Curve ℂ => (n : ℂ)^2 • Q x (lp.single 2 (n : ℤ) 1)) hc

theorem summable_norm_classicalHillNormalizedResidues_positive
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : NLS.LinearVolterra.Curve ℂ)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q q (lp.single 2 j 1)) m) (n : ℕ+) :
    Summable (fun k : ℕ+ => ‖(k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ)‖) := by
  have hi : Function.Injective (fun k : ℕ+ => (k : ℤ)) := by
    intro i j hij
    apply Subtype.ext
    exact Int.ofNat_inj.mp hij
  simpa only [Function.comp_def,classicalHillNormalizedResidues_positive R Q q hcompat n] using!
    ((lp.memℓp (classicalHillNormalizedResidues Q n q)).norm.summable_of_one).comp_injective hi

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem bounded_critical_reciprocals (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) (lambda : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ+, ‖(lambda-classicalHillUniformCriticalPoint N n q)⁻¹‖ ≤ C := by
  let R : ℝ := ‖lambda‖+1
  have hR : 0 < R := by dsimp only [R]; positivity
  obtain ⟨M,hM⟩ := exists_nat_gt (8*R/Real.pi^2+1)
  let f (j : ℕ) : ℝ := ‖(lambda-classicalHillUniformCriticalPoint N (⟨j+1,by omega⟩ : ℕ+) q)⁻¹‖
  let C : ℝ := 1+∑ j ∈ Finset.range M, f j
  have hC : 0 < C := by dsimp only [C,f]; positivity
  refine ⟨C,hC,?_⟩
  intro n
  by_cases hn : (n : ℕ) ≤ M
  · let i := (n : ℕ)-1
    have hi : i+1 = (n : ℕ) := Nat.sub_add_cancel n.property
    have himem : i ∈ Finset.range M := Finset.mem_range.mpr (by dsimp only [i]; omega)
    have hidx : (⟨i+1,by omega⟩ : ℕ+) = n := Subtype.ext hi
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.range M) => show 0 ≤ f j from norm_nonneg _) himem
    dsimp only [f] at hh
    rw [hidx] at hh
    exact hh.trans (by dsimp only [C]; linarith)
  · have hmn : (M : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : M < (n : ℕ))
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.property
    have hRtail : R ≤ Real.pi^2/8*(n : ℝ)^2 := by
      have hp : (0 : ℝ) < Real.pi^2 := by positivity
      have he := (div_lt_iff₀ hp).mp (show 8*R/Real.pi^2 < (n : ℝ) by linarith)
      nlinarith [mul_nonneg hp.le (show (0 : ℝ) ≤ (n : ℝ)^2-(n : ℝ) by nlinarith)]
    have hg := D.critical_energy_growth n q hq
    have ht := norm_sub_norm_le (classicalHillUniformCriticalPoint N n q) lambda
    rw [norm_sub_rev] at ht
    have hden : 1 ≤ ‖lambda-classicalHillUniformCriticalPoint N n q‖ := by
      dsimp only [R] at hRtail
      linarith
    rw [norm_inv]
    exact (inv_le_one_of_one_le₀ hden).trans
      (by dsimp only [C]; exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))

theorem summable_norm_normalized_resolvent
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q q (lp.single 2 j 1)) m) (n : ℕ+) (lambda : ℂ) :
    Summable (fun k : ℕ+ => ‖(k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ)/
      (lambda-classicalHillUniformCriticalPoint N k q)‖) := by
  obtain ⟨C,_,hC⟩ := D.bounded_critical_reciprocals q hq lambda
  apply ((summable_norm_classicalHillNormalizedResidues_positive R Q q hcompat n).mul_left C).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro k
  rw [norm_div,div_eq_mul_inv]
  simpa only [norm_inv,mul_comm] using
    mul_le_mul_of_nonneg_left (hC k) (norm_nonneg ((k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ)))

/-- The actual normalized entire function has its literal critical
resolvent expansion away from every selected energy. -/
theorem normalizedNumerator_resolvent
    (R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) (lambda : ℂ)
    (hlambda : ∀ k : ℕ+, lambda ≠ classicalHillUniformCriticalPoint N k q) :
    classicalHillNormalizedNumerator N R n (lambda,q) =
      (2*(Real.pi : ℂ)*deriv (classicalHillDiscriminant q) lambda)*
        ∑' k : ℕ+, (k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ)/
          (lambda-classicalHillUniformCriticalPoint N k q) := by
  rw [(D.normalizedNumerator_positive_series R n (lambda,q) ⟨mem_univ _,hq⟩).2]
  have hB (k : ℕ+) : classicalHillUniformNumerator N k (lambda,q) =
      (2*(k : ℂ)*Real.pi)*deriv (classicalHillDiscriminant q) lambda/
        (lambda-classicalHillUniformCriticalPoint N k q) := by
    apply (eq_div_iff (sub_ne_zero.mpr (hlambda k))).mpr
    simpa only [mul_comm] using D.numerator_factor k q hq lambda
  calc
    _ = ∑' k : ℕ+, (2*(Real.pi : ℂ)*deriv (classicalHillDiscriminant q) lambda)*
        ((k : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ)/
          (lambda-classicalHillUniformCriticalPoint N k q)) := by
      apply tsum_congr
      intro k
      rw [hB k]
      ring
    _ = _ := tsum_mul_left

end ClassicalAllContourPeriodData
end NLS.KdV
