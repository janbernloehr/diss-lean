import NLS.FunctionalAnalysis.AnalyticSchurComplement
import NLS.FunctionalAnalysis.CompactInvertibleComplement

/-! # Local analytic determinants for compact scalar perturbations

At every parameter, including a singular one, a finite-dimensional Schur
determinant detects the invertible members of an analytic operator family.
-/
noncomputable section
open Set Filter Topology
namespace NLS.CompactSpectrum
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- An invariant complement invertible at the center yields a local analytic
determinant, even if nearby operators do not preserve the decomposition. -/
theorem exists_local_determinant_of_invertible_complement
    {A : X → E →L[ℂ] E} {x : X} (hA : AnalyticAt ℂ A x)
    {N M : Submodule ℂ E} (h : Submodule.IsTopCompl N M)
    [FiniteDimensional ℂ N] (hM : MapsTo (A x) M M)
    (hbij : Function.Bijective ((A x).restrict hM)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ d : X → ℂ,
      AnalyticOnNhd ℂ d U ∧ ∀ y ∈ U, IsUnit (A y) ↔ d y ≠ 0 := by
  let : CompleteSpace M := h.isClosed'.completeSpace_coe
  let P := N.projectionOntoL M h
  let Q := M.projectionOntoL N h.symm
  let a := fun y => P.comp ((A y).comp N.subtypeL)
  let b := fun y => P.comp ((A y).comp M.subtypeL)
  let c := fun y => Q.comp ((A y).comp N.subtypeL)
  let d := fun y => Q.comp ((A y).comp M.subtypeL)
  have ha : AnalyticAt ℂ a x := SchurComplement.analyticAt_compCLM analyticAt_const
    (SchurComplement.analyticAt_compCLM hA analyticAt_const)
  have hb : AnalyticAt ℂ b x := SchurComplement.analyticAt_compCLM analyticAt_const
    (SchurComplement.analyticAt_compCLM hA analyticAt_const)
  have hc : AnalyticAt ℂ c x := SchurComplement.analyticAt_compCLM analyticAt_const
    (SchurComplement.analyticAt_compCLM hA analyticAt_const)
  have hd : AnalyticAt ℂ d x := SchurComplement.analyticAt_compCLM analyticAt_const
    (SchurComplement.analyticAt_compCLM hA analyticAt_const)
  have hdx : d x = (A x).restrict hM := by
    ext z
    exact congrArg Subtype.val (Submodule.projectionOntoL_apply_left h.symm ((A x).restrict hM z))
  obtain ⟨U,hU,hx,δ,hδ,hcrit⟩ := SchurComplement.exists_local_analytic_determinant ha hb hc hd
    (by rw [hdx]; exact ContinuousLinearMap.isUnit_iff_bijective.mpr hbij)
  refine ⟨U,hU,hx,δ,hδ,?_⟩
  intro y hy
  rw [← hcrit y hy,ContinuousLinearMap.isUnit_iff_bijective,ContinuousLinearMap.isUnit_iff_bijective]
  let e := N.prodEquivOfIsTopCompl M h
  have he : SchurComplement.block (a y) (b y) (c y) (d y) =
      e.symm.toContinuousLinearMap.comp ((A y).comp e.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    rintro ⟨z,w⟩
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [SchurComplement.block_apply,a,b,c,d,e,P,Q,
        Submodule.prodEquivOfIsTopCompl_apply,Submodule.prodEquivOfIsTopCompl_symm_apply,map_add]
  rw [he]
  change Function.Bijective (A y) ↔ Function.Bijective (e.symm ∘ A y ∘ e)
  constructor
  · intro hAy
    exact e.symm.bijective.comp (hAy.comp e.bijective)
  · intro hh
    have hh' := e.bijective.comp (hh.comp e.symm.bijective)
    simpa only [Function.comp_def,e.apply_symm_apply,e.symm_apply_apply] using hh'

/-- Every analytic family which is a nonzero scalar plus a compact operator
at the center admits an exact local analytic determinant criterion. -/
theorem exists_local_analytic_determinant
    {A : X → E →L[ℂ] E} {x : X} (hA : AnalyticAt ℂ A x)
    {c : ℂ} (hc : c ≠ 0) (hcompact : IsCompactOperator (A x - c • 1 : E →L[ℂ] E)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ d : X → ℂ,
      AnalyticOnNhd ℂ d U ∧ ∀ y ∈ U, IsUnit (A y) ↔ d y ≠ 0 := by
  obtain ⟨N,M,h,hfinite,hN,hM,hbij⟩ :=
    exists_invertible_complement_compact_shift (A x - c • 1) hcompact (neg_ne_zero.mpr hc)
  have he : A x - c • 1 - (-c) • 1 = A x := by rw [neg_smul]; abel
  simp only [he] at hN hM hbij
  let _ := hfinite
  exact exists_local_determinant_of_invertible_complement hA h hM hbij

end NLS.CompactSpectrum
