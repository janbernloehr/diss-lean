import NLS.SequenceSpaces.LocallyBoundedAnalyticSummation
import NLS.SequenceSpaces.HolderEmbedding
import NLS.SequenceSpaces.SandwichMajorant

/-! # Native Hilbert analytic series controlled by two Hilbert factors

A source-dependent Hilbert majorant and a fixed Hilbert factor suffice
for absolute Bochner convergence and native analyticity of the sum.
No common coordinatewise summable majorant is assumed.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analytic_tsum_of_hilbert_control (f : ℤ → E → Coeff 2) (a : E → Coeff 2)
    (b : Coeff 2) {U : Set E} (hU : IsOpen U)
    (hf : ∀ j : ℤ, AnalyticOnNhd ℂ (f j) U)
    (C M : ℝ) (hC : 0 ≤ C) (ha : ∀ u ∈ U, ‖a u‖ ≤ M)
    (hbound : ∀ u ∈ U, ∀ j : ℤ, ‖f j u‖ ≤ C*‖a u j‖*‖b j‖) :
    (∀ u ∈ U, Summable (fun j : ℤ => ‖f j u‖)) ∧
      AnalyticOnNhd ℂ (fun u => ∑' j : ℤ, f j u) U ∧
      ∀ u ∈ U, ‖∑' j : ℤ, f j u‖ ≤ C*M*‖b‖ := by
  let g : E → Coeff 1 := fun u => (C : ℂ) •
    holderProduct (q := 1) (magnitude (a u)) (magnitude b)
  have hg (u : E) (j : ℤ) : ‖g u j‖ = C*‖a u j‖*‖b j‖ := by
    simp only [g,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,holderProduct_apply,magnitude_apply,
      norm_mul,Complex.norm_real,Real.norm_of_nonneg hC,norm_norm]
    ring
  have hgnorm (u : E) (hu : u ∈ U) : ‖g u‖ ≤ C*M*‖b‖ := by
    rw [show ‖g u‖ = ‖(C : ℂ)‖*‖holderProduct (q := 1) (magnitude (a u)) (magnitude b)‖ from norm_smul _ _,
      Complex.norm_real,Real.norm_of_nonneg hC]
    apply (mul_le_mul_of_nonneg_left (norm_holderProduct_le _ _) hC).trans
    simpa only [norm_magnitude,mul_assoc] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ha u hu) hC) (norm_nonneg b)
  have hgSum (u : E) : Summable (fun j : ℤ => ‖g u j‖) := by
    simpa only [ENNReal.toReal_one,Real.rpow_one] using
      (lp.memℓp (g u)).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  have hgSumEq (u : E) : (∑' j : ℤ, ‖g u j‖) = ‖g u‖ := by
    simpa only [ENNReal.toReal_one,Real.rpow_one,one_div_one] using
      (lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) (g u)).symm
  have hdom (u : E) (hu : u ∈ U) (j : ℤ) : ‖f j u‖ ≤ ‖g u j‖ := (hbound u hu j).trans_eq (hg u j).symm
  have hs (u : E) (hu : u ∈ U) : Summable (fun j : ℤ => ‖f j u‖) :=
    (hgSum u).of_nonneg_of_le (fun _ => norm_nonneg _) (hdom u hu)
  have hsumBound (u : E) (hu : u ∈ U) : ‖∑' j : ℤ, f j u‖ ≤ C*M*‖b‖ := by
    apply (norm_tsum_le_tsum_norm (hs u hu)).trans
    exact ((hs u hu).tsum_le_tsum (hdom u hu) (hgSum u)).trans ((hgSumEq u).le.trans (hgnorm u hu))
  have hcoord (n : ℤ) : AnalyticOnNhd ℂ (fun u => (∑' j : ℤ, f j u) n) U := by
    have hscalar (j : ℤ) : AnalyticOnNhd ℂ (fun u => f j u n) U := fun u hu =>
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).analyticAt _).comp (hf j u hu)
    have hlocal : ∀ u ∈ U, ∃ V : Set E, IsOpen V ∧ u ∈ V ∧ V ⊆ U ∧
        ∃ D : ℝ, ∀ v ∈ V, ∃ c : Coeff 1, (∀ j, c j = f j v n) ∧ ‖c‖ ≤ D := by
      intro u hu
      refine ⟨U,hU,hu,Subset.rfl,C*M*‖b‖,?_⟩
      intro v hv
      have hb (j : ℤ) : ‖f j v n‖ ≤ ‖g v j‖ :=
        (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (f j v) n).trans (hdom v hv j)
      have hm : Memℓp (fun j : ℤ => f j v n) 1 := (lp.memℓp (g v)).mono' hb
      let c : Coeff 1 := ⟨fun j => f j v n,hm⟩
      refine ⟨c,fun _ => rfl,?_⟩
      exact (lp.norm_mono (by norm_num : (1 : ℝ≥0∞) ≠ 0) hb).trans (hgnorm v hv)
    have hsa := (analytic_tsum_of_local_one_bounds (fun u j => f j u n) hU hscalar hlocal).2.1
    intro u hu
    apply (hsa u hu).congr
    filter_upwards [hU.mem_nhds hu] with v hv
    exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).map_tsum (hs v hv).of_norm).symm
  exact ⟨hs,analyticOnNhd_of_bounded_coordinatewise _ hU hcoord _ hsumBound,hsumBound⟩

end NLS.Coeff
