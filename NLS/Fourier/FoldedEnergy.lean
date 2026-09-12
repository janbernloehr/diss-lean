import NLS.Fourier.FoldedSobolev
import NLS.Fourier.SobolevEnergy

/-!
# Energy of classical reflected interval functions

Reflection preserves each half's `L²` energy. For classical `H¹` input the
derivative acquires a minus sign, which disappears in the squared norm.
No smoothness at the join or regularity outside `[0,1]` is assumed.
-/

noncomputable section
open MeasureTheory Set
namespace NLS.Fourier

/-- Original classical interval regularity includes square integrability of the function. -/
theorem memLp_of_intervalH1Regularity {f : ℝ → ℂ} (hf : HasIntervalH1Regularity f) :
    MemLp f 2 (volume.restrict (Ioc 0 1)) := by
  have hi : IntegrableOn f (Ioc 0 1) volume := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
    hf.1.continuousOn.intervalIntegrable
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
    (hf.1.continuousOn.norm.pow 2).intervalIntegrable

/-- The exact folded energy identity holds for arbitrary `L²` halves, even with jumps. -/
theorem integral_sq_folded_of_memLp (ε : ℂ) (hε : ‖ε‖ = 1) {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) :
    (∫ x in (0 : ℝ)..2, ‖folded ε f g x‖ ^ 2) =
      (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) + ∫ x in (0 : ℝ)..1, ‖g x‖ ^ 2 := by
  have hfs : IntervalIntegrable (fun x => ‖f x‖ ^ 2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)
  have hgs : IntervalIntegrable (fun x => ‖g x‖ ^ 2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg)
  have h01 : EqOn (fun x => ‖folded ε f g x‖ ^ 2) (fun x => ‖f x‖ ^ 2) (uIoc 0 1) := by
    intro x hx
    have hx' : x ≤ 1 := (show x ∈ Ioc (0 : ℝ) 1 from by simpa using hx).2
    simp [folded, hx']
  have h12 : EqOn (fun x => ‖folded ε f g x‖ ^ 2) (fun x => ‖g (2 - x)‖ ^ 2) (uIoc 1 2) := by
    intro x hx
    have hx' : 1 < x := (show x ∈ Ioc (1 : ℝ) 2 from by simpa using hx).1
    simp [folded, not_le.mpr hx', hε]
  have hgr : IntervalIntegrable (fun x => ‖g (2 - x)‖ ^ 2) volume 1 2 := by
    simpa only [sub_zero, show (2 : ℝ) - 1 = 1 by norm_num] using (hgs.comp_sub_left 2).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hfs.congr h01.symm) (hgr.congr h12.symm),
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall h01),
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall h12),
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => ‖g x‖ ^ 2) 2]
  norm_num

/-- The actual folded derivative has the sum of the two original derivative energies. -/
theorem integral_sq_deriv_folded (ε : ℂ) (hε : ‖ε‖ = 1) {f g : ℝ → ℂ}
    (hf : HasIntervalH1Regularity f) (hg : HasIntervalH1Regularity g) (hjoin : f 1 = ε * g 1) :
    (∫ x in (0 : ℝ)..2, ‖deriv (folded ε f g) x‖ ^ 2) =
      (∫ x in (0 : ℝ)..1, ‖deriv f x‖ ^ 2) + ∫ x in (0 : ℝ)..1, ‖deriv g x‖ ^ 2 := by
  have he : (∫ x in (0 : ℝ)..2, ‖deriv (folded ε f g) x‖ ^ 2) =
      ∫ x in (0 : ℝ)..2, ‖folded (-ε) (deriv f) (deriv g) x‖ ^ 2 := by
    apply intervalIntegral.integral_congr_ae_restrict
    simpa only [uIoc_of_le (show (0 : ℝ) ≤ 2 by norm_num), Function.comp_def] using
      (deriv_folded_ae ε hf hg hjoin).fun_comp (fun z : ℂ => ‖z‖ ^ 2)
  rw [he, integral_sq_folded_of_memLp (-ε) (by simpa using hε) hf.2 hg.2]

/-- Physical Sobolev energy is exactly additive across the signed reflection. -/
theorem intervalH1Energy_folded (ε : ℂ) (hε : ‖ε‖ = 1) {f g : ℝ → ℂ}
    (hf : HasIntervalH1Regularity f) (hg : HasIntervalH1Regularity g) (hjoin : f 1 = ε * g 1) :
    intervalH1Energy (folded ε f g) 0 2 = intervalH1Energy f 0 1 + intervalH1Energy g 0 1 := by
  rw [intervalH1Energy, integral_sq_folded_of_memLp ε hε
    (memLp_of_intervalH1Regularity hf) (memLp_of_intervalH1Regularity hg),
    integral_sq_deriv_folded ε hε hf hg hjoin]
  unfold intervalH1Energy
  ring

end NLS.Fourier
