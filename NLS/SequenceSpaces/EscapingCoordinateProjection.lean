import NLS.SequenceSpaces.Truncation
import NLS.SequenceSpaces.FiniteExponentTail

/-! A single positive coordinate projection vanishes in full l2 norm
when its index escapes, also for a norm-convergent moving input. -/
noncomputable section
open Filter Topology
open scoped ENNReal Classical
namespace NLS.Coeff

theorem tendsto_escaping_singleton_projection
    (n : ℕ → ℕ+) (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop) (a : Coeff 2) :
    Tendsto (fun j => truncate {((n j:ℕ):ℤ)} a) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := exists_natAbs_norm_lt (by norm_num : 0 < (2:ℝ≥0∞).toReal) a hε
  filter_upwards [hn.eventually (eventually_ge_atTop N)] with j hj
  rw [dist_zero_right,truncate,Finset.sum_singleton,lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2)]
  exact hN _ (by simpa only [Int.natAbs_natCast] using hj)

theorem tendsto_moving_escaping_singleton_projection
    (n : ℕ → ℕ+) (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop)
    (a : ℕ → Coeff 2) (a₀ : Coeff 2) (ha : Tendsto a atTop (𝓝 a₀)) :
    Tendsto (fun j => truncate {((n j:ℕ):ℤ)} (a j)) atTop (𝓝 0) := by
  have hfixed := tendsto_escaping_singleton_projection n hn a₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ha' := Metric.tendsto_nhds.mp ha (ε/2) (half_pos hε)
  have hf := Metric.tendsto_nhds.mp hfixed (ε/2) (half_pos hε)
  filter_upwards [ha',hf] with j hj hf
  rw [dist_zero_right] at hf ⊢
  rw [dist_eq_norm] at hj
  have he : truncate {((n j:ℕ):ℤ)} (a j) =
      truncate {((n j:ℕ):ℤ)} (a j-a₀)+truncate {((n j:ℕ):ℤ)} a₀ := by
    rw [← truncate_add,sub_add_cancel]
  rw [he]
  exact (norm_add_le _ _).trans_lt (by
    have hb := norm_truncate_le (by norm_num : (2:ℝ≥0∞) ≠ 0) {((n j:ℕ):ℤ)} (a j-a₀)
    linarith)

theorem tendsto_remove_moving_escaping_coordinate
    (n : ℕ → ℕ+) (hn : Tendsto (fun j => (n j:ℕ)) atTop atTop)
    (a : ℕ → Coeff 2) (a₀ : Coeff 2) (ha : Tendsto a atTop (𝓝 a₀)) :
    Tendsto (fun j => a j-truncate {((n j:ℕ):ℤ)} (a j)) atTop (𝓝 a₀) := by
  simpa only [sub_zero] using ha.sub (tendsto_moving_escaping_singleton_projection n hn a a₀ ha)

end NLS.Coeff
