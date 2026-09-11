import NLS.FunctionalAnalysis.CompactSpectrum

/-!
# Generalized eigenspaces of compact operators

Nonzero generalized eigenspaces are finite dimensional and stabilize at a
finite exponent. The stabilization proof uses Riesz vectors in successive
kernels, while finite dimensionality follows by cancelling the constant term
in powers of the shifted operator.
-/

noncomputable section
open Module Module.End Filter Topology

namespace NLS.CompactSpectrum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Removing the constant term from a power of a compact operator plus a scalar
identity gives another compact operator. -/
theorem isCompactOperator_shift_pow_sub (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    (μ : ℂ) (n : ℕ) :
    IsCompactOperator (((T - μ • 1) ^ n - (-μ) ^ n • 1) : E →L[ℂ] E) := by
  induction n with
  | zero => simpa using (isCompactOperator_zero : IsCompactOperator (0 : E →L[ℂ] E))
  | succ n ih =>
    have heq : (T - μ • 1) ^ (n + 1) - (-μ) ^ (n + 1) • (1 : E →L[ℂ] E) =
        T.comp ((T - μ • 1) ^ n) - μ • ((T - μ • 1) ^ n - (-μ) ^ n • (1 : E →L[ℂ] E)) := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [pow_succ', mul_apply_eq_comp, sub_apply, smul_apply,
        one_apply_eq_self, ContinuousLinearMap.comp_apply]
      module
    rw [heq]
    exact (hT.comp_clm _).sub (ih.smul μ)

/-- Express the finite-level generalized eigenspace using a continuous power. -/
theorem genEigenspace_eq_ker_shift_pow (T : E →L[ℂ] E) (μ : ℂ) (n : ℕ) :
    Module.End.genEigenspace T.toLinearMap μ n = ((T - μ • 1) ^ n).toLinearMap.ker := by
  simp only [Module.End.genEigenspace_nat, ContinuousLinearMap.toLinearMap_pow,
    ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.toLinearMap_one]

/-- Every finite-level nonzero generalized eigenspace of a compact operator is
finite dimensional. -/
theorem finiteDimensional_genEigenspace (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    {μ : ℂ} (hμ : μ ≠ 0) (n : ℕ) :
    FiniteDimensional ℂ (Module.End.genEigenspace T.toLinearMap μ n) := by
  let C := (T - μ • 1) ^ n - (-μ) ^ n • (1 : E →L[ℂ] E)
  have heq : Module.End.genEigenspace T.toLinearMap μ n =
      Module.End.eigenspace C.toLinearMap (-(-μ) ^ n) := by
    ext x
    rw [genEigenspace_eq_ker_shift_pow, LinearMap.mem_ker, Module.End.mem_eigenspace_iff]
    change ((T - μ • 1) ^ n) x = 0 ↔
      ((T - μ • 1) ^ n) x - (-μ) ^ n • x = -(-μ) ^ n • x
    constructor
    · intro h
      rw [h, zero_sub, neg_smul]
    · intro h
      rw [neg_smul] at h
      exact sub_eq_neg_self.mp h
  rw [heq]
  exact finiteDimensional_eigenspace C (isCompactOperator_shift_pow_sub T hT μ n)
    (neg_ne_zero.mpr (pow_ne_zero n (neg_ne_zero.mpr hμ)))

/-- The increasing sequence of generalized eigenspaces must have two equal
successive terms at every nonzero spectral value. -/
theorem exists_genEigenspace_eq_succ (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    {μ : ℂ} (hμ : μ ≠ 0) :
    ∃ n : ℕ, Module.End.genEigenspace T.toLinearMap μ n =
      Module.End.genEigenspace T.toLinearMap μ (n + 1 : ℕ) := by
  classical
  by_contra! hn
  let S := T - μ • (1 : E →L[ℂ] E)
  let V : ℕ → Submodule ℂ E := fun n => Module.End.genEigenspace T.toLinearMap μ n
  have hVmono : Monotone V := fun n m h =>
    (Module.End.genEigenspace T.toLinearMap μ).monotone (by exact_mod_cast h)
  have hVclosed (n : ℕ) : IsClosed (V n : Set E) := by
    change IsClosed (Module.End.genEigenspace T.toLinearMap μ n : Set E)
    rw [genEigenspace_eq_ker_shift_pow]
    exact (S ^ n).isClosed_ker
  have hchoice (n : ℕ) : ∃ x : V (n + 1), ‖x‖ = 1 ∧
      ∀ y : E, y ∈ V n → (1 / 2 : ℝ) ≤ ‖(x : E) - y‖ := by
    let W := (V n).comap (V (n + 1)).subtype
    have hclosed : IsClosed (W : Set (V (n + 1))) :=
      (hVclosed n).preimage continuous_subtype_val
    obtain ⟨v, hv, hvn⟩ := SetLike.exists_of_lt (lt_of_le_of_ne (hVmono (Nat.le_succ n)) (hn n))
    have hproper : ∃ x : V (n + 1), x ∉ W := ⟨⟨v, hv⟩, hvn⟩
    obtain ⟨x, _, hnorm, hdist⟩ := riesz_lemma_of_lt_one hclosed hproper
      (show (1 / 2 : ℝ) < 1 by norm_num)
    exact ⟨x, hnorm, fun y hy => hdist ⟨y, hVmono (Nat.le_succ n) hy⟩ hy⟩
  choose x hxnorm hxdist using hchoice
  have hshift (n : ℕ) (y : E) (hy : y ∈ V (n + 1)) : S y ∈ V n := by
    change y ∈ Module.End.genEigenspace T.toLinearMap μ (n + 1 : ℕ) at hy
    change S y ∈ Module.End.genEigenspace T.toLinearMap μ n
    rw [genEigenspace_eq_ker_shift_pow, LinearMap.mem_ker] at hy ⊢
    change (S ^ (n + 1)) y = 0 at hy
    change (S ^ n) (S y) = 0
    simpa only [pow_succ, mul_apply_eq_comp] using hy
  have hpres (n : ℕ) (y : E) (hy : y ∈ V n) : T y ∈ V n := by
    have heq : T y = S y + μ • y := by dsimp [S]; simp
    rw [heq]
    exact (V n).add_mem (hshift n y (hVmono (Nat.le_succ n) hy)) ((V n).smul_mem μ hy)
  have hsep : Pairwise fun m n : ℕ => ‖μ‖ / 2 ≤ ‖T (x m) - T (x n)‖ := by
    have : Std.Symm (fun m n : ℕ => ‖μ‖ / 2 ≤ ‖T (x m) - T (x n)‖) :=
      ⟨fun _ _ h => by simpa only [norm_sub_rev] using h⟩
    apply Pairwise.of_lt
    intro m n hmn
    let u : E := μ⁻¹ • (T (x m) - S (x n))
    have hu : u ∈ V n := (V n).smul_mem _ ((V n).sub_mem
      (hVmono hmn (hpres (m + 1) (x m) (x m).property)) (hshift n (x n) (x n).property))
    have heq : μ • ((x n : E) - u) = T (x n) - T (x m) := by
      dsimp [u]
      rw [smul_sub, smul_inv_smul₀ hμ]
      dsimp [S]
      simp only [sub_apply, smul_apply, one_apply_eq_self]
      abel
    calc
      ‖μ‖ / 2 ≤ ‖μ‖ * ‖(x n : E) - u‖ := by
        have hd := hxdist n u hu
        nlinarith [norm_nonneg μ]
      _ = ‖T (x n) - T (x m)‖ := by rw [← norm_smul, heq]
      _ = _ := norm_sub_rev _ _
  obtain ⟨K, hK, hKT⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y, _, ψ, hψ, hψy⟩ := hK.tendsto_subseq
    (fun n => hKT ⟨(x n : E), by simpa using (hxnorm n).le, rfl⟩)
  have hc := hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hc
  obtain ⟨N, hN⟩ := hc (‖μ‖ / 2) (by positivity)
  have hlt : ‖T (x (ψ (N + 1))) - T (x (ψ N))‖ < ‖μ‖ / 2 := by
    simpa only [dist_eq_norm_sub, Function.comp_apply, ContinuousLinearMap.coe_coe]
      using hN (N + 1) (by omega)
  exact hlt.not_ge (hsep (hψ.injective.ne (by omega)))

/-- The full generalized eigenspace at a nonzero value is attained at a finite exponent. -/
theorem exists_genEigenspace_eq_top (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    {μ : ℂ} (hμ : μ ≠ 0) :
    ∃ n : ℕ, Module.End.genEigenspace T.toLinearMap μ n =
      Module.End.genEigenspace T.toLinearMap μ ⊤ := by
  obtain ⟨n, hn⟩ := exists_genEigenspace_eq_succ T hT hμ
  refine ⟨n, le_antisymm ((Module.End.genEigenspace T.toLinearMap μ).monotone le_top) ?_⟩
  rw [Module.End.genEigenspace_top]
  apply iSup_le
  intro m
  by_cases hmn : m ≤ n
  · exact (Module.End.genEigenspace T.toLinearMap μ).monotone (by exact_mod_cast hmn)
  · simp only [Module.End.genEigenspace_nat] at hn ⊢
    have hc := Module.End.ker_pow_constant hn (m - n)
    have hnm : n + (m - n) = m := Nat.add_sub_of_le (by omega)
    rw [hnm] at hc
    exact hc.ge

/-- The full nonzero generalized eigenspace is finite dimensional. -/
theorem finiteDimensional_genEigenspace_top (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    {μ : ℂ} (hμ : μ ≠ 0) :
    FiniteDimensional ℂ (Module.End.genEigenspace T.toLinearMap μ ⊤) := by
  obtain ⟨n, hn⟩ := exists_genEigenspace_eq_top T hT hμ
  rw [← hn]
  exact finiteDimensional_genEigenspace T hT hμ n

end NLS.CompactSpectrum
