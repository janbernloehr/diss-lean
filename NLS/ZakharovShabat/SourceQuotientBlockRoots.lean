import NLS.ZakharovShabat.SourceSingleRootQuotientAbsolute
import NLS.ZakharovShabat.SourceSingleRootQuotientNormalization

/-!
# The finite-block numerator family at the free source

A constant displacement on indices 1 through L belongs to every sequence
space. Its fourth-power norm is explicit, and the actual analytic quotient
at an unperturbed free center is exactly a finite real product.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceQuotientBlockRootsFourFact : Fact (1 ≤ (4:ℝ≥0∞)) := ⟨by norm_num⟩

/-- Constant numerator displacement on the positive block `1,…,L`, in any exponent. -/
def sourceQuotientBlock (p : ℝ≥0∞) (L : ℕ) (a : ℂ) : Coeff p :=
  ⟨fun m => if m ∈ Finset.Icc (1:ℤ) L then a else 0,
    memℓp_of_eq_outside_finset zero_memℓp (Finset.Icc (1:ℤ) L)
      (by intro m hm; simp [hm])⟩

@[simp] theorem sourceQuotientBlock_apply (p : ℝ≥0∞) (L : ℕ) (a : ℂ) (m : ℤ) :
    sourceQuotientBlock p L a m = if m ∈ Finset.Icc (1:ℤ) L then a else 0 := rfl

/-- The l4 norm records both the amplitude and the number of perturbed roots. -/
theorem sourceQuotientBlock_norm_fourth (L : ℕ) (a : ℂ) : ‖sourceQuotientBlock 4 L a‖^4 = L*‖a‖^4 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (4:ℝ≥0∞).toReal) (sourceQuotientBlock 4 L a)
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_natCast] at h
  have h' : ‖sourceQuotientBlock 4 L a‖^4 = ∑' i : ℤ, ‖sourceQuotientBlock 4 L a i‖^4 := by simpa using! h
  rw [h',tsum_eq_sum (s := Finset.Icc (1:ℤ) L) (by
    intro m hm
    simp [sourceQuotientBlock_apply,hm])]
  calc
    (∑ m ∈ Finset.Icc (1:ℤ) L, ‖sourceQuotientBlock 4 L a m‖^4) =
        ∑ m ∈ Finset.Icc (1:ℤ) L, ‖a‖^4 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [sourceQuotientBlock_apply,if_pos hm]
    _ = L*‖a‖^4 := by simp [Int.card_Icc]

/-- At an unperturbed free center, the actual infinite quotient reduces to this finite product. -/
theorem sourceSingleRootQuotient_block_eq_finiteProduct (L : ℕ) (a : ℝ) (n : ℤ)
    (hn : n ∉ Finset.Icc (1:ℤ) L) :
    sourceSingleRootQuotientJointProduct (p := 4) (by norm_num) (by norm_num) n
      ((Real.pi:ℂ)*n,(sourceQuotientBlock 4 L (a:ℂ),0)) =
        ∏ m ∈ Finset.Icc (1:ℤ) L, (1-((a/(Real.pi*((n-m:ℤ):ℝ))):ℝ):ℂ) := by
  let hp : (4:ℝ≥0∞) ≠ ⊤ := by norm_num
  let hp1 : (1:ℝ≥0∞) < 4 := by norm_num
  let f := sourceSingleRootQuotientFactor hp hp1 0 (sourceQuotientBlock 4 L (a:ℂ)) ((Real.pi:ℂ)*n) n
  have hf (m : ℤ) (hm : m ∉ Finset.Icc (1:ℤ) L) : f m = 1 := by
    by_cases hmn : m = n
    · simp [f,sourceSingleRootQuotientFactor,hmn]
    · have hd : (Real.pi:ℂ)*m-(Real.pi:ℂ)*n ≠ 0 := by
        rw [← mul_sub]
        exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast sub_ne_zero.mpr hmn)
      simp [f,sourceSingleRootQuotientFactor,hmn,displacedRoots,hm,sourceStandardRoot_zero_source,hd]
  have hactual := hasProd_sourceSingleRootQuotientFactor hp hp1 0 (sourceQuotientBlock 4 L (a:ℂ))
    ((Real.pi:ℂ)*n) n (sourceStandardRootOmittedDomain_zero_source_contains_center hp hp1 n)
  have hfinite : HasProd f (∏ m ∈ Finset.Icc (1:ℤ) L, f m) := hasProd_prod_of_ne_finset_one hf
  rw [hactual.unique hfinite]
  apply Finset.prod_congr rfl
  intro m hm
  have hmn : m ≠ n := by intro he; subst m; exact hn hm
  have hd : (Real.pi:ℂ)*m-(Real.pi:ℂ)*n ≠ 0 := by
    rw [← mul_sub]
    exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast sub_ne_zero.mpr hmn)
  have hdn : (Real.pi:ℂ)*((n:ℂ)-m) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast sub_ne_zero.mpr hmn.symm)
  simp only [f,sourceSingleRootQuotientFactor,if_neg hmn,sourceStandardRoot_zero_source,
    displacedRoots,sourceQuotientBlock_apply,if_pos hm]
  have hmnC : (m:ℂ)-(n:ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hmn
  have hnmC : (n:ℂ)-(m:ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hmn.symm
  push_cast
  field_simp [hd,hdn,hmnC,hnmC]
  ring

end NLS.ZakharovShabat
