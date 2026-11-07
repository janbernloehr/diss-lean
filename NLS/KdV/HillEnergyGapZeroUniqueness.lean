import NLS.KdV.HillMiuraEnergyGapCoordinates
import NLS.KdV.MiuraCanonicalRootReflection
import NLS.ComplexAnalysis.QuadraticLiftUniqueness
import NLS.ZakharovShabat.Section7EntirePeriodUniqueness

/-! An entire energy function with sub-sine quadratic differential
growth and a zero in EVERY original positive Hill gap vanishes.
Positive original gaps give actual frequency zeros, reflection supplies
the negative gaps, and the exact2*z factor supplies the central zero.
This makes no root-square assertion on a cut. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillMiura_energy_eq_zero_of_all_original_gap_zeros
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q))
    (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ)
    (hzeros : ∀ m : ℕ+, ∃ E : ℝ,
      E ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ))) ∧ P (E:ℂ) = 0)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k), ‖(2*z*P (z^2-(c:ℂ)))/(-2*sin z)‖ ≤ ε) :
    P = 0 := by
  let F : ℂ → ℂ := fun z => 2*z*P (z^2-(c:ℂ))
  have hF : AnalyticOnNhd ℂ F univ := by
    intro z _
    exact (analyticAt_const.mul analyticAt_id).mul
      ((hP _ (mem_univ _)).comp (f := fun w : ℂ => w^2-(c:ℂ))
        ((analyticAt_id.pow 2).sub analyticAt_const))
  have hodd (z : ℂ) : F (-z) = -F z := by dsimp only [F]; rw [neg_sq]; ring
  have hpositive (m : ℕ+) : ∃ z ∈ sourcePeriodicSegment (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val) ((m:ℕ):ℤ), F z = 0 := by
    obtain ⟨E,hE,hzero⟩ := hzeros m
    have hfreq := hillMiura_frequency_of_original_gap q hq u c hi hc m E hE
    refine ⟨energyFrequency (c:ℂ) (E:ℂ),hfreq.2.1,?_⟩
    have he : (energyFrequency (c:ℂ) (E:ℂ))^2-(c:ℂ) = (E:ℂ) := by rw [energyFrequency_sq]; ring
    dsimp only [F]
    rw [he,hzero,mul_zero]
  have hzeroF : F = 0 := by
    apply section7_entire_zero_of_gap_zeros (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property F hF _ hsmall
    intro m
    rcases lt_trichotomy m 0 with hm | hm | hm
    · let k : ℕ+ := ⟨(-m).toNat,by omega⟩
      have hk : -((k:ℕ):ℤ) = m := by
        change -(((-m).toNat:ℕ):ℤ) = m
        rw [Int.toNat_of_nonneg (by omega)]
        exact neg_neg m
      obtain ⟨z,hz,hzF⟩ := hpositive k
      have hmem := ((sourcePeriodicReflection_hillMiuraDiagonal u.val).neg_mem_segment_iff ((k:ℕ):ℤ) z).mpr hz
      rw [hk] at hmem
      exact ⟨-z,hmem,by rw [hodd,hzF,neg_zero]⟩
    · subst m
      refine ⟨0,?_,?_⟩
      · simpa only [Complex.ofReal_zero] using sourcePeriodicSegment_mem_of_realIcc
          (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property 0 0
          (hillMiura_gap_zero_contains_zero u)
      · simp only [F,mul_zero,zero_mul]
    · let k : ℕ+ := ⟨m.toNat,by omega⟩
      have hk : ((k:ℕ):ℤ) = m := by
        change ((m.toNat:ℕ):ℤ) = m
        exact Int.toNat_of_nonneg hm.le
      have hx := hpositive k
      rw [hk] at hx
      exact hx
  apply eq_of_quadratic_differential_pullback_eq P (fun _ => 0)
    (continuousOn_univ.mp hP.continuousOn) continuous_const (c:ℂ)
  intro z
  have hz := congrFun hzeroF z
  simpa only [F,Pi.zero_apply,mul_zero] using hz

end NLS.KdV
