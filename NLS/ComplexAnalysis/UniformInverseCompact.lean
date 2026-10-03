import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Analysis.Complex.Basic

/-! # Uniform inversion near a compact nonzero scalar family -/
noncomputable section
open Set Filter Topology Metric
namespace NLS.ComplexAnalysis

/-- Uniform convergence to a continuous nonzero function on a compact set
persists under inversion. Approximants need not be nonzero before the
uniform estimate takes effect. -/
theorem tendstoUniformlyOn_inv_of_compact_nonzero
    {X α : Type*} [TopologicalSpace X] {l : Filter α}
    {F : α → X → ℂ} {f : X → ℂ} {K : Set X}
    (h : TendstoUniformlyOn F f l K) (hK : IsCompact K)
    (hf : ContinuousOn f K) (hne : ∀ z ∈ K, f z ≠ 0) :
    TendstoUniformlyOn (fun k z => (F k z)⁻¹) (fun z => (f z)⁻¹) l K := by
  obtain ⟨δ,hδ,hb⟩ := hK.exists_forall_le' hf.norm (fun z hz => norm_pos_iff.mpr (hne z hz))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h
    (min (δ/2) (ε*δ^2/2)) (by positivity)] with k hk z hz
  have hd := hk z hz
  have hdδ : dist (f z) (F k z) < δ/2 := hd.trans_le (min_le_left _ _)
  have hlow : δ/2 < ‖F k z‖ := by
    have ht := norm_sub_norm_le (f z) (F k z)
    rw [← dist_eq_norm] at ht
    linarith [hb z hz]
  have hFk : F k z ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [dist_inv_inv₀ (hne z hz) hFk]
  apply (div_lt_iff₀ (mul_pos (norm_pos_iff.mpr (hne z hz)) (norm_pos_iff.mpr hFk))).mpr
  apply (hd.trans_le (min_le_right _ _)).trans_le
  have hprod : δ^2/2 ≤ ‖f z‖*‖F k z‖ := by
    nlinarith [hb z hz,norm_nonneg (f z),norm_nonneg (F k z)]
  nlinarith

end NLS.ComplexAnalysis
