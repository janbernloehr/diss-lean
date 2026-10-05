import NLS.FunctionalAnalysis.CompactDecomposition
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Fredholm operators with a finite-dimensional invariant summand -/
noncomputable section
namespace NLS.CompactSpectrum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An invariant finite-dimensional summand and an invertible complementary
restriction give a Fredholm operator with equal kernel and cokernel dimensions. -/
theorem fredholm_index_zero_of_isTopCompl (A : E →L[ℂ] E)
    {N M : Submodule ℂ E} (h : Submodule.IsTopCompl N M)
    [FiniteDimensional ℂ N] (hN : Set.MapsTo A N N) (hM : Set.MapsTo A M M)
    (hbij : Function.Bijective (A.restrict hM)) :
    A.IsFredholm ∧ Module.finrank ℂ A.ker = Module.finrank ℂ (E ⧸ A.range) := by
  let : CompleteSpace M := h.isClosed'.completeSpace_coe
  let : M.CoFG := Submodule.FG.cofg_of_isCompl h.isCompl
    ((Submodule.fg_iff_finiteDimensional N).mpr inferInstance)
  let e := ContinuousLinearEquiv.ofBijective (A.restrict hM)
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have hFred : A.IsFredholm := .of_isInvertible_restrict h.isClosed' h.isClosed' hM ⟨e, rfl⟩
  refine ⟨hFred, ?_⟩
  let a := A.restrict hN
  let P := N.projectionOntoL M h
  have hP (x : N) : P x = x := Submodule.projectionOntoL_apply_left h x
  have hPM (x : M) : P x = 0 := Submodule.projectionOntoL_apply_right h x
  have hcomm (x : E) : P (A x) = a (P x) := by
    apply Subtype.ext
    exact (DFunLike.congr_fun (commute_projectionL_of_invariant h A hN hM).eq x).symm
  have hkerN (x : E) (hx : A x = 0) : x ∈ N := by
    obtain ⟨u, v, huv, _⟩ := Submodule.existsUnique_add_of_isCompl h.isCompl x
    have hu : A u = 0 := by
      have hpz := congrArg P hx
      rw [hcomm, ← huv, map_add, hP, hPM, add_zero, map_zero] at hpz
      exact congrArg Subtype.val hpz
    have hv : A v = 0 := by simpa [← huv, map_add, hu] using hx
    have hv0 : v = 0 := hbij.1 (show (A.restrict hM) v = (A.restrict hM) 0 from
      Subtype.ext (by change A v = A 0; simpa using hv))
    simp [← huv, hv0]
  let k : a.ker →ₗ[ℂ] A.ker :=
    { toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hk : Function.Bijective k := by
    constructor
    · intro x y he
      exact Subtype.ext (Subtype.ext (congrArg (fun z : A.ker => z.val) he))
    · intro x
      refine ⟨⟨⟨x.val, hkerN x.val x.property⟩, ?_⟩, rfl⟩
      exact Subtype.ext x.property
  have hdimker := (LinearEquiv.ofBijective k hk).finrank_eq
  let L : E →ₗ[ℂ] N ⧸ a.range := a.range.mkQ.comp P.toLinearMap
  have hLsurj : Function.Surjective L := by
    intro z
    obtain ⟨x, rfl⟩ := a.range.mkQ_surjective z
    exact ⟨x.val, by change a.range.mkQ (P x) = a.range.mkQ x; rw [hP]⟩
  have hLker : L.ker = A.range := by
    ext x
    change a.range.mkQ (P x) = 0 ↔ x ∈ A.range
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨u, hu⟩
      have hm : x - A u ∈ M := by
        apply (Submodule.projectionOntoL_apply_eq_zero_iff h).mp
        rw [map_sub, hcomm, hP]
        exact sub_eq_zero.mpr hu.symm
      obtain ⟨v, hv⟩ := hbij.2 ⟨x - A u, hm⟩
      refine ⟨u.val + v.val, ?_⟩
      have hv' := congrArg Subtype.val hv
      change A v = x - A u at hv'
      change A (u.val + v.val) = x
      rw [map_add, hv']
      abel
    · rintro ⟨y, rfl⟩
      exact ⟨P y, (hcomm y).symm⟩
  have hdimcoker := ((Submodule.quotEquivOfEq A.range L.ker hLker.symm).trans
    (L.quotKerEquivOfSurjective hLsurj)).finrank_eq
  have hrank := a.toLinearMap.finrank_range_add_finrank_ker
  have hquot := a.range.finrank_quotient_add_finrank
  change Module.finrank ℂ a.range + Module.finrank ℂ a.ker = Module.finrank ℂ N at hrank
  omega

end NLS.CompactSpectrum
