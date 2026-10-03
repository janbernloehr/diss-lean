import NLS.FunctionalAnalysis.CompactDecomposition

/-! # Dense range for compact perturbations of identity

The compact spectral decomposition upgrades dense range to bijectivity.
This avoids imposing an adjoint or Hilbert-space structure on the source.
-/

noncomputable section
namespace NLS.CompactSpectrum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A compact perturbation of identity with dense range is a bounded isomorphism. -/
theorem bijective_of_denseRange_compact_sub_id (A : E →L[ℂ] E)
    (hA : IsCompactOperator (A - 1 : E →L[ℂ] E)) (hd : DenseRange A) :
    Function.Bijective A := by
  let T := A - 1
  have hshift : T - (-1 : ℂ) • 1 = A := by simp [T]
  obtain ⟨n, hn⟩ := exists_genEigenspace_eq_top T hA (neg_ne_zero.mpr one_ne_zero)
  have hc := isTopCompl_genEigenspace_range_pow T hA (neg_ne_zero.mpr one_ne_zero) n hn
  rw [hshift] at hc
  have hpow (k : ℕ) : DenseRange (A ^ k) := by
    induction k with
    | zero => simpa using (Function.surjective_id : Function.Surjective (id : E → E)).denseRange
    | succ k ih =>
      rw [pow_succ']
      exact hd.comp ih A.continuous
  have hrange : (A ^ n).range = ⊤ := by
    apply SetLike.coe_injective
    change Set.range (A ^ n) = Set.univ
    have hclosed : IsClosed (Set.range (A ^ n)) := hc.isClosed'
    rw [← hclosed.closure_eq]
    exact (hpow n).closure_eq
  have hinj : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro x hx
    have hxN : x ∈ Module.End.genEigenspace T.toLinearMap (-1 : ℂ) ⊤ := by
      apply (Module.End.genEigenspace T.toLinearMap (-1 : ℂ)).monotone (show (1 : ℕ∞) ≤ ⊤ from le_top)
      change x ∈ Module.End.genEigenspace T.toLinearMap (-1 : ℂ) (1 : ℕ)
      rw [genEigenspace_eq_ker_shift_pow, hshift, pow_one, LinearMap.mem_ker]
      exact hx
    exact Submodule.disjoint_def.mp hc.isCompl.disjoint x hxN (hrange ▸ Submodule.mem_top)
  exact bijective_of_injective_compact_sub_smul A one_ne_zero (by simpa using hA) hinj

end NLS.CompactSpectrum
