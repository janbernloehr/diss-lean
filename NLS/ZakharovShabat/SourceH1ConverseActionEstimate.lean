import NLS.ZakharovShabat.SourceH1ActionSums
import NLS.ZakharovShabat.SobolevQuarticMassBound
import NLS.ZakharovShabat.PhysicalH1NormBound

/-! # Lemma 27.1: energy and H¹ norms controlled by the actions

The physical correction is nonpositive. The quartic mass bound and the
discrete Fourier comparison give the exact factor 1/3 in the source.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- Nonpositivity of the physical correction gives the first inequality of Lemma 27.1. -/
theorem sourceH1_energy_le_kinetic_actions (a : realTypeSobolevSourceLocus) :
    (periodOneSobolevHamiltonian a.val).re-2*(periodOneSobolevMass a.val).re^2 ≤
      ∑' n : ℤ, (sourceSobolevWeightedAction a.val n).re := by
  have h := (sourceSobolevPhysicalCorrection_nonpos a).1
  have hs := (summable_norm_sourceSobolevWeightedAction a.val a.property).of_norm
  have he : (2*(periodOneSobolevMass a.val)^2).re = 2*(periodOneSobolevMass a.val).re^2 := by
    rw [periodOneSobolevMass_real_eq]
    norm_cast
  rw [sourceSobolevPhysicalCorrection, sourceSobolevWeightedActionSum_eq_tsum _ a.property,
    Complex.sub_re, Complex.sub_re, he, Complex.re_tsum hs] at h
  linarith

/-- The printed energy inequality, with the literal signed-frequency kinetic weights. -/
theorem sourceH1_energy_action_bound (a : realTypeSobolevSourceLocus) :
    (periodOneSobolevHamiltonian a.val).re-2*(periodOneSobolevMass a.val).re^2 ≤
      ∑' n : ℤ, (2*Real.pi*(n:ℝ))^2*
        (sourceRealAction (by simp) (by norm_num) (sourceH1RealSource a).val
          (sourceH1RealSource a).property n).re := by
  simpa only [sourceSobolevWeightedAction_re] using sourceH1_energy_le_kinetic_actions a

/-- The energy is bounded by the weighted action norm and twice the squared total action. -/
theorem sourceH1_energy_le_weighted_actions (a : realTypeSobolevSourceLocus) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
        2*(∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)^2 := by
  rw [sourceH1_sum_actions_eq_mass]
  have hm : 0 ≤ (periodOneSobolevMass a.val).re := by
    rw [periodOneSobolevMass_real_eq, Complex.ofReal_re]
    positivity
  linarith [sourceH1_energy_le_kinetic_actions a, sourceH1_kinetic_actions_add_mass_le a]

/-- The exact H¹ norm corollary of Lemma 27.1, including its factor 1/3. -/
theorem sourceH1_third_norm_sq_le_actions (a : realTypeSobolevSourceLocus) :
    (1/3:ℝ)*‖sourcePhysicalH1Coordinates a.val‖^2 ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)^2 := by
  rw [sourceH1_sum_actions_eq_mass]
  have hnorm := sourcePhysicalH1_third_sq_le_mass_kinetic a
  have hquartic := periodOneSobolevMass_sq_le_quartic a
  have henergy := sourceH1_energy_le_kinetic_actions a
  have hsum := sourceH1_kinetic_actions_add_mass_le a
  rw [periodOneSobolevHamiltonian, Complex.add_re] at henergy
  linarith

end NLS.ZakharovShabat
