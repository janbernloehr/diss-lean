import NLS.FunctionalAnalysis.CompactDecomposition

/-! # An invertible complement for compact scalar perturbations -/
noncomputable section
namespace NLS.CompactSpectrum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A nonzero compact shift has a finite-dimensional invariant summand
and an invariant closed complement on which it is invertible. -/
theorem exists_invertible_complement_compact_shift
    (T : E →L[ℂ] E) (hT : IsCompactOperator T) {μ : ℂ} (hμ : μ ≠ 0) :
    ∃ N M : Submodule ℂ E, ∃ _ : Submodule.IsTopCompl N M,
      ∃ _ : FiniteDimensional ℂ N,
      ∃ _ : Set.MapsTo (T - μ • 1 : E →L[ℂ] E) N N,
      ∃ hM : Set.MapsTo (T - μ • 1 : E →L[ℂ] E) M M,
        Function.Bijective ((T - μ • 1 : E →L[ℂ] E).restrict hM) := by
  obtain ⟨n, hn⟩ := exists_genEigenspace_eq_top T hT hμ
  let S := T - μ • (1 : E →L[ℂ] E)
  let N := Module.End.genEigenspace T.toLinearMap μ ⊤
  let M := (S ^ n).range
  have h : Submodule.IsTopCompl N M := isTopCompl_genEigenspace_range_pow T hT hμ n hn
  let : FiniteDimensional ℂ N := finiteDimensional_genEigenspace_top T hT hμ
  let : CompleteSpace M := h.isClosed'.completeSpace_coe
  have hNker : N = (S ^ n).ker := by
    dsimp [N, S]
    rw [← hn, genEigenspace_eq_ker_shift_pow]
  have hcomm (x : E) : S ((S ^ n) x) = (S ^ n) (S x) :=
    DFunLike.congr_fun (Commute.self_pow S n).eq x
  have hN : Set.MapsTo S N N := by
    intro x hx
    rw [hNker] at hx ⊢
    change (S ^ n) (S x) = 0
    rw [← hcomm, show (S ^ n) x = 0 from hx, map_zero]
  have hM : Set.MapsTo S M M := by
    rintro x ⟨y, rfl⟩
    exact ⟨S y, (hcomm y).symm⟩
  let A := S.restrict hM
  have hinj : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro x hx
    have hsx : S x = 0 := congrArg Subtype.val hx
    have hx1 : x.val ∈ Module.End.genEigenspace T.toLinearMap μ (1 : ℕ) := by
      rw [genEigenspace_eq_ker_shift_pow, pow_one]
      exact hsx
    have hxN : x.val ∈ N := (Module.End.genEigenspace T.toLinearMap μ).monotone le_top hx1
    exact Subtype.ext (Submodule.disjoint_def.mp h.isCompl.disjoint x.val hxN x.property)
  let Q := M.projectionOntoL N h.symm
  have hcompact : IsCompactOperator (A - (-μ) • 1 : M →L[ℂ] M) := by
    have he : A - (-μ) • 1 = Q.comp (T.comp M.subtypeL) := by
      apply ContinuousLinearMap.ext
      intro x
      apply Subtype.ext
      have hqx : Q x = x := Submodule.projectionOntoL_apply_left h.symm x
      have hqa : Q (S x) = A x := Submodule.projectionOntoL_apply_left h.symm (A x)
      have ht : T x = S x + μ • (x : E) := by dsimp [S]; simp
      change S x - (-μ) • (x : E) = (Q (T x) : E)
      rw [ht, map_add, map_smul, hqa, hqx]
      simp only [neg_smul, sub_neg_eq_add]
      rfl
    rw [he]
    exact (hT.comp_clm M.subtypeL).clm_comp Q
  exact ⟨N,M,h,inferInstance,hN,hM,
    bijective_of_injective_compact_sub_smul A (neg_ne_zero.mpr hμ) hcompact hinj⟩

end NLS.CompactSpectrum
