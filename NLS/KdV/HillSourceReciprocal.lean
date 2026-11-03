import NLS.KdV.PseudomeasureSourceCircles
import NLS.KdV.PseudomeasureKernel
import NLS.SequenceSpaces.HillLogKernel

/-! Full free reciprocal bounds on the LITERAL periodic source circles,
retaining both resonant modes and the original pi²*n² energies. -/
noncomputable section
open Set Metric
namespace NLS.KdV

/-- Every free denominator on the original source circle has modulus at least n. -/
theorem freeHillSourceCircle_denominator_ge (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k : ℤ) :
    (n:ℝ) ≤ ‖z-(freeHillValue k:ℂ)‖ := by
  by_cases hk : k.natAbs=n
  · rcases (hill_resonance_iff n k).mp hk with rfl | rfl
    · simpa only [dist_eq_norm] using (mem_sphere.mp hz).ge
    · simpa only [freeHillValue_neg,dist_eq_norm] using (mem_sphere.mp hz).ge
  · exact freeHill_denominator_ge_index hn
      (freeHillSourceDisk_subset_strip n hn (sphere_subset_closedBall hz)) hk

/-- The complete reciprocal majorant includes both original resonant terms. -/
theorem freeHillSourceCircle_reciprocal_le (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (k : ℤ) :
    ‖z-(freeHillValue k:ℂ)‖⁻¹ ≤ NLS.ReciprocalSeries.mixedHillKernel 1 n k +
      (if k=(n:ℤ) then (n:ℝ)⁻¹ else 0) + (if k=-(n:ℤ) then (n:ℝ)⁻¹ else 0) := by
  have hnorm : ‖z-(freeHillValue n:ℂ)‖ = n := by simpa only [dist_eq_norm] using mem_sphere.mp hz
  by_cases hk : k.natAbs=n
  · rcases (hill_resonance_iff n k).mp hk with rfl | rfl
    · simp [hnorm,NLS.ReciprocalSeries.mixedHillKernel,show (n:ℤ) ≠ -(n:ℤ) by omega]
    · simp [freeHillValue_neg,hnorm,NLS.ReciprocalSeries.mixedHillKernel,show -(n:ℤ) ≠ (n:ℤ) by omega]
  · have hres := mt (hill_resonance_iff n k).mpr hk
    have hd := freeHill_inverse_norm_le_product hn
      (freeHillSourceDisk_subset_strip n hn (sphere_subset_closedBall hz)) hk
    simpa only [norm_inv,NLS.ReciprocalSeries.mixedHillKernel,if_neg hres,
      if_neg (not_or.mp hres).1,if_neg (not_or.mp hres).2,Real.rpow_neg_one,
      mul_inv,add_zero] using hd

/-- The complete free reciprocal lattice is summable on every original source circle. -/
theorem summable_freeHillSourceCircle_reciprocal (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    Summable (fun k : ℤ => ‖z-(freeHillValue k:ℂ)‖⁻¹) := by
  have hp : Summable (fun k : ℤ => if k=(n:ℤ) then (n:ℝ)⁻¹ else 0) := by
    apply summable_of_ne_finset_zero (s := {(n:ℤ)})
    intro k hk
    simp only [Finset.mem_singleton] at hk
    simp [hk]
  have hm : Summable (fun k : ℤ => if k=-(n:ℤ) then (n:ℝ)⁻¹ else 0) := by
    apply summable_of_ne_finset_zero (s := {-(n:ℤ)})
    intro k hk
    simp only [Finset.mem_singleton] at hk
    simp [hk]
  exact (((NLS.ReciprocalSeries.summable_mixedHillKernel 1 (by norm_num) le_rfl n hn).add hp).add hm).of_nonneg_of_le (fun _ => inv_nonneg.mpr (norm_nonneg _))
      (freeHillSourceCircle_reciprocal_le n hn z hz)

/-- The full reciprocal sum has the original logarithmic-over-index decay,
with an absolute explicit constant and both resonances included. -/
theorem tsum_freeHillSourceCircle_reciprocal_le_log (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    (∑' k : ℤ, ‖z-(freeHillValue k:ℂ)‖⁻¹) ≤
      (8*Real.exp 1+2)*Real.log (n:ℝ)/(n:ℝ) := by
  have hp : Summable (fun k : ℤ => if k=(n:ℤ) then (n:ℝ)⁻¹ else 0) := by
    apply summable_of_ne_finset_zero (s := {(n:ℤ)})
    intro k hk
    simp only [Finset.mem_singleton] at hk
    simp [hk]
  have hm : Summable (fun k : ℤ => if k=-(n:ℤ) then (n:ℝ)⁻¹ else 0) := by
    apply summable_of_ne_finset_zero (s := {-(n:ℤ)})
    intro k hk
    simp only [Finset.mem_singleton] at hk
    simp [hk]
  have hk := NLS.ReciprocalSeries.summable_mixedHillKernel 1 (by norm_num) le_rfl n hn
  have hs := (summable_freeHillSourceCircle_reciprocal n hn z hz).tsum_le_tsum
    (freeHillSourceCircle_reciprocal_le n hn z hz) ((hk.add hp).add hm)
  rw [(hk.add hp).tsum_add hm,hk.tsum_add hp] at hs
  simp only [tsum_ite_eq] at hs
  have hb := NLS.ReciprocalSeries.tsum_hillKernel_one_le_log n hn hlog
  have hi : 2*(n:ℝ)⁻¹ ≤ 2*Real.log (n:ℝ)/(n:ℝ) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  calc
    _ ≤ (8*Real.exp 1)*Real.log (n:ℝ)/(n:ℝ)+2*(n:ℝ)⁻¹ := by linarith
    _ ≤ (8*Real.exp 1)*Real.log (n:ℝ)/(n:ℝ)+2*Real.log (n:ℝ)/(n:ℝ) := add_le_add le_rfl hi
    _ = _ := by ring

end NLS.KdV
