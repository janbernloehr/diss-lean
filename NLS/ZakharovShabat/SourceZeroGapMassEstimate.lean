import NLS.ZakharovShabat.SourceFullAbelianInverseMomentReal
import NLS.ZakharovShabat.SourceFiniteGapActionTrace

/-! # The weak weighted-action bound for mass at a normalized central gap

The exact inverse-frequency mass identity absorbs half of the ordinary
action sum. The other half is bounded by the original first weighted
actions divided by pi times their actual signed spectral indices.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The physical Hilbert mass is bounded by the actual weak weighted
spectral action sum, with coefficient one. Both index signs are retained. -/
theorem sourceFiniteGap_mass_le_weak_weighted_actions
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hl : canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0)
    (hr : canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0) :
    (sourceHilbertMass φ.val).re ≤ ∑ n ∈ hf.toFinset,
      sourceRealHigherAction (by simp) (by norm_num) φ n 1/(Real.pi*(n : ℝ)) := by
  classical
  obtain ⟨W,_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num)
  obtain ⟨C,hC⟩ := hfamilies φ
  have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hC]
    exact mem_ball_self C.discs.sourceRadius_pos
  have hm := C.mass_eq_sum_real_inverse_moments φ hφ hf hl hr
  change (sourceHilbertMass φ.val).re = _ at hm
  have ha := congrArg Complex.re (sourceFiniteGap_sum_actions_eq_mass φ hf)
  simp only [Complex.re_sum] at ha
  have hgap0 : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0 := by
    rw [canonicalPeriodicGap,hl,hr,sub_self]
  have hs (n : ℤ) : n ∈ hf.toFinset ↔ canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0 := Set.Finite.mem_toFinset hf
  have hb := Finset.sum_le_sum (s := hf.toFinset) (fun n hn =>
    sourceRealAction_le_inverseMoment_add_higherAction (by simp) (by norm_num) φ hl hr n
      (by rintro rfl; exact (hs 0).mp hn hgap0))
  rw [ha,Finset.sum_add_distrib] at hb
  have he : (∑ n ∈ hf.toFinset, sourceRealHigherAction (by simp) (by norm_num) φ n 1/
      (2*Real.pi*(n : ℝ))) =
      (∑ n ∈ hf.toFinset, sourceRealHigherAction (by simp) (by norm_num) φ n 1/
        (Real.pi*(n : ℝ)))/2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  rw [he] at hb
  linarith

/-- The same exact estimate in the original pair norm. -/
theorem sourceFiniteGap_half_norm_sq_le_weak_weighted_actions
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hl : canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0)
    (hr : canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 = 0) :
    ‖φ.val‖^2/2 ≤ ∑ n ∈ hf.toFinset,
      sourceRealHigherAction (by simp) (by norm_num) φ n 1/(Real.pi*(n : ℝ)) := by
  have h := sourceFiniteGap_mass_le_weak_weighted_actions φ hf hl hr
  rwa [sourceHilbertMass_eq_half_norm_sq_of_realType φ.val φ.property,ofReal_re] at h

end NLS.ZakharovShabat
