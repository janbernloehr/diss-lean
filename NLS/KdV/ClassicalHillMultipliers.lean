import NLS.KdV.ClassicalHillFlow
import NLS.FunctionalAnalysis.LinearVolterraLinearity

/-! # Periodic and antiperiodic scalar Hill endpoint multipliers

The actual normalized scalar IVP has multiplier +1 or -1 exactly at
discriminant +2 or -2. A nonzero state fixed by two iterations therefore
lies at a zero of the actual period-one discriminant squared minus four.
-/

noncomputable section
open Set Complex NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

theorem classicalHillFlow_add (q : Curve ℂ) (lambda : ℂ) (v w : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    classicalHillFlow q lambda (v+w) t = classicalHillFlow q lambda v t+classicalHillFlow q lambda w t :=
  solution_add _ _ _ t

theorem classicalHillFlow_zero_initial (q : Curve ℂ) (lambda : ℂ) (t : Icc (0 : ℝ) 1) :
    classicalHillFlow q lambda 0 t = 0 := solution_zero_initial _ t

theorem exists_classicalHillFlow_multiplier_iff (q : Curve ℂ) (lambda z σ : ℂ)
    (hz : z^2 = lambda) :
    (∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalHillFlow q lambda v 1 = σ • v) ↔
      ∃ u : ℂ × ℂ, u ≠ 0 ∧ classicalSolution (constantUpperPotential q) z u 1 = σ • u := by
  subst lambda
  have ht : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  constructor
  · rintro ⟨v, hv, he⟩
    refine ⟨constantUpperInitialVector z v, ?_, ?_⟩
    · intro hzero
      apply hv
      have h := constantUpperStateMap_initialVector z v
      rw [hzero, map_zero] at h
      exact h.symm
    · apply constantUpperStateMap_injective z
      rw [map_smul, constantUpperStateMap_initialVector]
      have h := classicalHillFlow_eq_constantUpper q z v ⟨1,ht⟩
      rw [he] at h
      exact h.symm
  · rintro ⟨u, hu, he⟩
    refine ⟨constantUpperStateMap z u, ?_, ?_⟩
    · intro hzero
      exact hu (constantUpperStateMap_injective z (hzero.trans (map_zero _).symm))
    · rw [classicalHillFlow_eq_constantUpper q z _ ⟨1,ht⟩,
        constantUpperInitialVector_stateMap, he, map_smul]

theorem classicalHillDiscriminant_eq_two_iff_flow (q : Curve ℂ) (lambda : ℂ) :
    classicalHillDiscriminant q lambda = 2 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalHillFlow q lambda v 1 = v := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq lambda (by norm_num : 0 < 2)
  rw [classicalHillDiscriminant_eq_of_sq q lambda z hz, classicalDiscriminant_eq_two_iff]
  simpa only [one_smul] using (exists_classicalHillFlow_multiplier_iff q lambda z 1 hz).symm

theorem classicalHillDiscriminant_eq_neg_two_iff_flow (q : Curve ℂ) (lambda : ℂ) :
    classicalHillDiscriminant q lambda = -2 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalHillFlow q lambda v 1 = -v := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq lambda (by norm_num : 0 < 2)
  rw [classicalHillDiscriminant_eq_of_sq q lambda z hz, classicalDiscriminant_eq_neg_two_iff]
  simpa only [neg_one_smul] using (exists_classicalHillFlow_multiplier_iff q lambda z (-1) hz).symm

theorem classicalHillRadicand_eq_zero_iff_flow (q : Curve ℂ) (lambda : ℂ) :
    classicalHillDiscriminant q lambda ^ 2-4 = 0 ↔
      (∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalHillFlow q lambda v 1 = v) ∨
      (∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalHillFlow q lambda v 1 = -v) := by
  rw [show classicalHillDiscriminant q lambda ^ 2-4 =
    (classicalHillDiscriminant q lambda-2)*(classicalHillDiscriminant q lambda+2) by ring,
    mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg,
    classicalHillDiscriminant_eq_two_iff_flow, classicalHillDiscriminant_eq_neg_two_iff_flow]

theorem classicalHillRadicand_zero_of_double_fixed (q : Curve ℂ) (lambda : ℂ)
    (v : ℂ × ℂ) (hv : v ≠ 0)
    (he : classicalHillFlow q lambda (classicalHillFlow q lambda v 1) 1 = v) :
    classicalHillDiscriminant q lambda ^ 2-4 = 0 := by
  rw [classicalHillRadicand_eq_zero_iff_flow]
  by_cases hz : classicalHillFlow q lambda v 1+v = 0
  · exact Or.inr ⟨v, hv, add_eq_zero_iff_eq_neg.mp hz⟩
  · apply Or.inl
    refine ⟨classicalHillFlow q lambda v 1+v, hz, ?_⟩
    rw [classicalHillFlow_add q lambda _ _ ⟨1,by norm_num⟩, he, add_comm]

end NLS.KdV
