import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Finiteness of compact-operator spectra away from zero

The Riesz-lemma argument needed for discreteness of a compact-resolvent
operator. Distinct eigenvalues give strictly growing invariant finite-dimensional
spans; Riesz vectors in these spans have compact images separated by a fixed
positive distance if the eigenvalues stay away from zero.
-/

noncomputable section
open Module Module.End Filter Topology

namespace NLS.CompactSpectrum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A compact complex operator has only finitely many eigenvalues outside any
positive-radius ball about zero. No self-adjointness is required. -/
theorem finite_eigenvalues_norm_ge (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    {ε : ℝ} (hε : 0 < ε) :
    Set.Finite {μ : ℂ | Module.End.HasEigenvalue (T : Module.End ℂ E) μ ∧ ε ≤ ‖μ‖} := by
  classical
  by_contra hs
  let e := Set.Infinite.natEmbedding _ hs
  let μ : ℕ → ℂ := fun n => (e n).val
  have hμ : Function.Injective μ := Subtype.val_injective.comp e.injective
  have hεμ : ∀ n, ε ≤ ‖μ n‖ := fun n => (e n).property.2
  obtain ⟨v, hv⟩ := Classical.axiomOfChoice fun n => (e n).property.1.exists_hasEigenvector
  have hvind : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (T : Module.End ℂ E) μ hμ v hv
  have heigen (n : ℕ) : T (v n) = μ n • v n := (hv n).apply_eq_smul
  let V : ℕ → Submodule ℂ E := fun n => Submodule.span ℂ (v '' Set.Iio n)
  have hVfin (n : ℕ) : FiniteDimensional ℂ (V n) :=
    FiniteDimensional.span_of_finite ℂ ((Set.finite_Iio n).image v)
  have hVclosed (n : ℕ) : IsClosed (V n : Set E) := by
    let : FiniteDimensional ℂ (V n) := hVfin n
    exact (V n).closed_of_finiteDimensional
  have hVmono : Monotone V := fun _ _ h =>
    Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))
  have hv_mem {k n : ℕ} (h : k < n) : v k ∈ V n :=
    Submodule.subset_span ⟨k, h, rfl⟩
  have hchoice (n : ℕ) : ∃ x : V (n + 1), ‖x‖ = 1 ∧
      ∀ y : E, y ∈ V n → (1 / 2 : ℝ) ≤ ‖(x : E) - y‖ := by
    let W := (V n).comap (V (n + 1)).subtype
    have hWclosed : IsClosed (W : Set (V (n + 1))) :=
      (hVclosed n).preimage continuous_subtype_val
    have hproper : ∃ x : V (n + 1), x ∉ W :=
      ⟨⟨v n, hv_mem (Nat.lt_succ_self n)⟩, hvind.notMem_span_image (by simp)⟩
    obtain ⟨x, _, hnorm, hdist⟩ := riesz_lemma_of_lt_one hWclosed hproper
      (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨x, hnorm, fun y hy => ?_⟩
    exact hdist ⟨y, hVmono (Nat.le_succ n) hy⟩ hy
  choose x hxnorm hxdist using hchoice
  have hTinvariant (n : ℕ) : ∀ y ∈ V n, T y ∈ V n := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      rw [heigen k]
      exact (V n).smul_mem _ (hv_mem hk)
    | zero => simp
    | add y z _ _ hy hz => simpa using (V n).add_mem hy hz
    | smul c y _ hy => simpa using (V n).smul_mem c hy
  have hshift (n : ℕ) : ∀ y ∈ V (n + 1), T y - μ n • y ∈ V n := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      rw [heigen k, ← sub_smul]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact (V n).smul_mem _ (hv_mem hk)
      · simp
    | zero => simp
    | add y z _ _ hy hz =>
      simpa only [map_add, smul_add, add_sub_add_comm] using (V n).add_mem hy hz
    | smul c y _ hy =>
      simpa only [map_smul, smul_sub, smul_comm (μ n) c] using (V n).smul_mem c hy
  have hsep : Pairwise fun m n : ℕ => ε / 2 ≤ ‖T (x m) - T (x n)‖ := by
    have : Std.Symm (fun m n : ℕ => ε / 2 ≤ ‖T (x m) - T (x n)‖) :=
      ⟨fun _ _ h => by simpa only [norm_sub_rev] using h⟩
    apply Pairwise.of_lt
    intro m n hmn
    have hμn : μ n ≠ 0 := norm_pos_iff.mp (hε.trans_le (hεμ n))
    let u : E := (μ n)⁻¹ • (T (x m) - (T (x n) - μ n • (x n : E)))
    have hu : u ∈ V n := (V n).smul_mem _ ((V n).sub_mem
      (hVmono hmn (hTinvariant (m + 1) (x m) (x m).property))
      (hshift n (x n) (x n).property))
    have heq : μ n • ((x n : E) - u) = T (x n) - T (x m) := by
      dsimp [u]
      rw [smul_sub, smul_inv_smul₀ hμn]
      abel
    calc
      ε / 2 ≤ ‖μ n‖ * ‖(x n : E) - u‖ := by
        have hd := hxdist n u hu
        nlinarith [hεμ n, norm_nonneg ((x n : E) - u)]
      _ = ‖T (x n) - T (x m)‖ := by rw [← norm_smul, heq]
      _ = _ := norm_sub_rev _ _
  obtain ⟨K, hK, hKT⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y, _, ψ, hψ, hψy⟩ := hK.tendsto_subseq
    (fun n => hKT ⟨(x n : E), by simpa using (hxnorm n).le, rfl⟩)
  have hc := hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hc
  obtain ⟨N, hN⟩ := hc (ε / 2) (by positivity)
  have hlt : ‖T (x (ψ (N + 1))) - T (x (ψ N))‖ < ε / 2 := by
    simpa only [dist_eq_norm_sub, Function.comp_apply, ContinuousLinearMap.coe_coe] using hN (N + 1) (by omega)
  exact hlt.not_ge (hsep (hψ.injective.ne (by omega)))

/-- The nonzero spectrum of a compact operator is finite away from zero. -/
theorem finite_spectrum_norm_ge [CompleteSpace E] (T : E →L[ℂ] E)
    (hT : IsCompactOperator T) {ε : ℝ} (hε : 0 < ε) :
    Set.Finite {μ : ℂ | μ ∈ spectrum ℂ T ∧ ε ≤ ‖μ‖} := by
  apply (finite_eigenvalues_norm_ge T hT hε).subset
  intro μ hμ
  exact ⟨(hT.hasEigenvalue_iff_mem_spectrum
    (norm_pos_iff.mp (hε.trans_le hμ.2))).mpr hμ.1, hμ.2⟩

/-- Every nonzero eigenspace of a compact operator is finite dimensional. -/
theorem finiteDimensional_eigenspace (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    {μ : ℂ} (hμ : μ ≠ 0) :
    FiniteDimensional ℂ (Module.End.eigenspace (T : Module.End ℂ E) μ) := by
  let W := Module.End.eigenspace (T : Module.End ℂ E) μ
  have heigen (v : E) (hv : v ∈ W) : T v = μ • v :=
    Module.End.mem_eigenspace_iff.mp hv
  have hclosed : IsClosed (W : Set E) := by
    have heq : (W : Set E) = {v | T v = μ • v} := by
      ext v
      exact Module.End.mem_eigenspace_iff
    rw [heq]
    exact isClosed_eq T.continuous (continuous_id.const_smul μ)
  have hpres : ∀ v ∈ W, (T : Module.End ℂ E) v ∈ W := by
    intro v hv
    change T v ∈ W
    rw [heigen v hv]
    exact W.smul_mem μ hv
  have hc := hT.restrict (f := (T : Module.End ℂ E)) hpres hclosed
  have heq : (μ⁻¹ • ((T : Module.End ℂ E).restrict hpres : W → W)) = id := by
    funext v
    apply Subtype.ext
    change μ⁻¹ • T (v : E) = (v : E)
    rw [heigen v v.property, inv_smul_smul₀ hμ]
  exact FiniteDimensional.of_isCompactOperator_id (𝕜 := ℂ) (heq ▸ hc.smul μ⁻¹)

end NLS.CompactSpectrum
