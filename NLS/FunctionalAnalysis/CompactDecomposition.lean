import NLS.FunctionalAnalysis.CompactGeneralized
import Mathlib.Analysis.LocallyConvex.HahnBanach

/-!
# Decompositions at nonzero compact-operator spectral values

The stabilized kernel of a shifted compact operator has the range of the same
power as a topological complement. The proof compresses that power to an
arbitrary complement of its finite-dimensional kernel and applies the Fredholm
alternative there.
-/

noncomputable section
open Module Module.End

namespace NLS.CompactSpectrum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An injective compact perturbation of a nonzero scalar identity is bijective. -/
theorem bijective_of_injective_compact_sub_smul (A : E →L[ℂ] E) {c : ℂ} (hc : c ≠ 0)
    (hA : IsCompactOperator (A - c • 1 : E →L[ℂ] E))
    (hinj : Function.Injective A) : Function.Bijective A := by
  rcases hA.hasEigenvalue_or_mem_resolventSet (neg_ne_zero.mpr hc) with he | hr
  · obtain ⟨v, hv⟩ := he.exists_hasEigenvector
    have hvzero : A v = 0 := by
      have h := hv.apply_eq_smul
      change A v - c • v = -c • v at h
      rw [neg_smul] at h
      exact sub_eq_neg_self.mp h
    exact False.elim (hv.2 (hinj (hvzero.trans (map_zero A).symm)))
  · rw [spectrum.mem_resolventSet_iff] at hr
    have heq : algebraMap ℂ (E →L[ℂ] E) (-c) - (A - c • 1) = -A := by
      simp only [Algebra.algebraMap_eq_smul_one, neg_smul]
      abel
    rw [heq, IsUnit.neg_iff, ContinuousLinearMap.isUnit_iff_bijective] at hr
    exact hr

/-- Once a nonzero compact-operator root space stabilizes, it is topologically
complementary to the range of the same shifted power. -/
theorem isTopCompl_genEigenspace_range_pow (T : E →L[ℂ] E) (hT : IsCompactOperator T)
    {μ : ℂ} (hμ : μ ≠ 0) (n : ℕ)
    (hn : Module.End.genEigenspace T.toLinearMap μ n =
      Module.End.genEigenspace T.toLinearMap μ ⊤) :
    Submodule.IsTopCompl (Module.End.genEigenspace T.toLinearMap μ ⊤)
      ((T - μ • 1) ^ n).range := by
  let N := Module.End.genEigenspace T.toLinearMap μ ⊤
  let B := (T - μ • 1) ^ n
  have hN : N = B.ker := by
    dsimp [N, B]
    rw [← hn, genEigenspace_eq_ker_shift_pow]
  have hkill (x : E) (hx : x ∈ N) : B x = 0 := by
    exact LinearMap.mem_ker.mp (hN ▸ hx)
  have hreflect (x : E) (hx : B x ∈ N) : x ∈ N := by
    have hzero : ((T - μ • 1) ^ (n + n)) x = 0 := by
      simpa only [pow_add, mul_apply_eq_comp] using hkill (B x) hx
    have hx' : x ∈ Module.End.genEigenspace T.toLinearMap μ (n + n : ℕ) := by
      rw [genEigenspace_eq_ker_shift_pow, LinearMap.mem_ker]
      exact hzero
    exact (Module.End.genEigenspace T.toLinearMap μ).monotone le_top hx'
  let : FiniteDimensional ℂ N := finiteDimensional_genEigenspace_top T hT hμ
  obtain ⟨M, hNM⟩ := (Submodule.ClosedComplemented.of_finiteDimensional N).exists_isTopCompl
  let : CompleteSpace M := hNM.isClosed'.completeSpace_coe
  let q := M.projectionOntoL N hNM.symm
  have hq (x : E) : q x = 0 ↔ x ∈ N := Submodule.projectionOntoL_apply_eq_zero_iff hNM.symm
  have hqi (x : M) : q x = x := Submodule.projectionOntoL_apply_left hNM.symm x
  let A := q.comp (B.comp M.subtypeL)
  have hAc : IsCompactOperator (A - (-μ) ^ n • 1 : M →L[ℂ] M) := by
    have heq : A - (-μ) ^ n • 1 =
        q.comp ((B - (-μ) ^ n • 1).comp M.subtypeL) := by
      apply ContinuousLinearMap.ext
      intro x
      change q (B x) - (-μ) ^ n • x = q (B x - (-μ) ^ n • (x : E))
      rw [map_sub, map_smul, hqi]
    rw [heq]
    exact ((isCompactOperator_shift_pow_sub T hT μ n).comp_clm M.subtypeL).clm_comp q
  have hAi : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro x hx
    have hxN := hreflect x ((hq (B x)).mp hx)
    apply Subtype.ext
    exact (Submodule.disjoint_def.mp hNM.isCompl.disjoint) _ hxN x.property
  have hAb := bijective_of_injective_compact_sub_smul A
    (pow_ne_zero n (neg_ne_zero.mpr hμ)) hAc hAi
  let e := ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hAb.1)
    (LinearMap.range_eq_top.mpr hAb.2)
  let U := M.subtypeL.comp (e.symm.toContinuousLinearMap.comp q)
  have hBU (x : E) : q (B (U x)) = q x := e.apply_symm_apply (q x)
  let P := (1 : E →L[ℂ] E) - B.comp U
  have hPN (x : E) : P x ∈ N := by
    apply (hq _).mp
    change q (x - B (U x)) = 0
    rw [map_sub, hBU, sub_self]
  have hPid (x : N) : P x = x := by
    change (x : E) - B (U x) = x
    have hqx : q x = 0 := (hq x).mpr x.property
    simp [U, hqx]
  let P' := P.codRestrict N hPN
  have htop : Submodule.IsTopCompl N P'.ker :=
    ContinuousLinearMap.isTopCompl_of_proj (fun x => Subtype.ext (hPid x))
  have hker : P'.ker = B.range := by
    ext x
    constructor
    · intro hx
      have hpx : P x = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      exact ⟨U x, (sub_eq_zero.mp hpx).symm⟩
    · rintro ⟨y, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change B y - B (U (B y)) = 0
      rw [← map_sub]
      apply hkill
      apply hreflect
      simpa only [P, sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply,
        map_sub] using hPN (B y)
  rw [hker] at htop
  exact htop

omit [CompleteSpace E] in
/-- A map preserving both summands commutes with the associated projection. -/
theorem commute_projectionL_of_invariant {N M : Submodule ℂ E}
    (h : Submodule.IsTopCompl N M) (A : E →L[ℂ] E)
    (hN : ∀ x ∈ N, A x ∈ N) (hM : ∀ x ∈ M, A x ∈ M) :
    Commute A (N.projectionL M h) := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨u, v, hx, _⟩ := Submodule.existsUnique_add_of_isCompl h.isCompl x
  rw [← hx]
  change A (N.projectionL M h ((u : E) + v)) = N.projectionL M h (A ((u : E) + v))
  rw [map_add, Submodule.projectionL_apply_left h u,
    Submodule.projectionL_apply_right h v, add_zero, map_add, map_add]
  rw [Submodule.projectionL_apply_left h ⟨A u, hN u u.property⟩,
    Submodule.projectionL_apply_right h ⟨A v, hM v v.property⟩, add_zero]

omit [CompleteSpace E] in
/-- Commuting with an operator preserves its kernel/range decomposition. -/
theorem commute_projectionL_ker_range {A B : E →L[ℂ] E} (hAB : Commute A B)
    (h : Submodule.IsTopCompl B.ker B.range) :
    Commute A (B.ker.projectionL B.range h) := by
  have hab (x : E) : A (B x) = B (A x) := DFunLike.congr_fun hAB.eq x
  apply commute_projectionL_of_invariant h A
  · intro x hx
    change B (A x) = 0
    have hx0 : B x = 0 := hx
    rw [← hab, hx0, map_zero]
  · rintro x ⟨y, rfl⟩
    exact ⟨A y, (hab y).symm⟩

end NLS.CompactSpectrum
