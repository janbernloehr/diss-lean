import NLS.ZakharovShabat.FreeResolventExteriorLimit
import NLS.ZakharovShabat.UniformThresholds

/-!
# Uniform exterior estimates for bounded families with small tails

A bounded family of finite Fourier heads decays uniformly at spectral infinity.
The remaining tail is controlled by the common exterior resolvent norm. This
separates the finite head estimate from any choice of spectral root labels.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite Fourier head has an explicit bound independent of its coefficients. -/
theorem norm_scalarResolvent_truncate_le (hp : p ≠ ⊤) (s : Finset ℤ) (B : ℝ)
    (a : Coeff p) (ha : ‖a‖ ≤ B) (z : ℂ) (hz : z ∉ freeLattice) :
    ‖scalarResolventToL1 hp z hz (Coeff.truncate s a)‖ ≤
      ∑ n ∈ s, B/‖z-(Real.pi : ℂ)*n‖ := by
  rw [Coeff.truncate, map_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [scalarResolventToL1_single, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1), norm_div]
  exact div_le_div_of_nonneg_right
    ((lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' a n).trans ha) (norm_nonneg _)

/-- One threshold makes every bounded finite head small throughout the exterior. -/
theorem exists_threshold_scalarResolvent_truncate (hp : p ≠ ⊤) (s : Finset ℤ) (B : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ∀ hz : z ∉ freeLattice, ∀ a : Coeff p, ‖a‖ ≤ B →
      ‖scalarResolventToL1 hp z hz (Coeff.truncate s a)‖ ≤ ε := by
  have ht : Tendsto (fun z : ℂ => ∑ n ∈ s, B/‖z-(Real.pi : ℂ)*n‖)
      (comap (fun z : ℂ => ‖z‖) atTop) (𝓝 0) := by
    simpa only [Finset.sum_const_zero, id_eq] using tendsto_finsetSum s
      (fun n _ => (tendsto_norm_free_denominator_atTop id tendsto_comap n).const_div_atTop B)
  obtain ⟨R, hR⟩ := exists_threshold_of_eventually_comap_atTop (fun z : ℂ => ‖z‖)
    (ht.eventually (gt_mem_nhds hε))
  exact ⟨R, fun z hz hzfree a ha => (norm_scalarResolvent_truncate_le hp s B a ha z hzfree).trans (hR z hz).le⟩

/-- A uniformly small head and the common resolvent norm control any bounded input family. -/
theorem exists_threshold_scalarResolvent_small_tail (hp : p ≠ ⊤) (s : Finset ℤ) (B : ℝ)
    {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ∀ hsep : ∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖,
      ∀ a : Coeff p, ‖a‖ ≤ B →
      ‖scalarResolventToL1 hp z (notMem_freeLattice_of_separated hr hsep) a‖ ≤
        ε+(WeightedCoeff.sobolevEmbeddingConstant p hp/r)*‖a-Coeff.truncate s a‖ := by
  obtain ⟨R, hR⟩ := exists_threshold_scalarResolvent_truncate hp s B hε
  refine ⟨R, ?_⟩
  intro z hz hsep a ha
  let T := scalarResolventToL1 hp z (notMem_freeLattice_of_separated hr hsep)
  have he : a = Coeff.truncate s a+(a-Coeff.truncate s a) := by abel
  calc
    ‖T a‖ = ‖T (Coeff.truncate s a)+T (a-Coeff.truncate s a)‖ := by rw [← map_add, ← he]
    _ ≤ ‖T (Coeff.truncate s a)‖+‖T (a-Coeff.truncate s a)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (hR z hz _ a ha)
      (norm_scalarResolventToL1_le_of_separated hp z _ hr hrπ hsep _)

end NLS.ZakharovShabat
