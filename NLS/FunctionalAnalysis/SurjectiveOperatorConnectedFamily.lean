import NLS.FunctionalAnalysis.SurjectiveKernelPersistence

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.FunctionalAnalysis

/-- Bijectivity of bounded Banach operators persists under small norm
perturbations, using the verified composition Neumann bound. -/
theorem eventually_bijective_of_bijective
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (T : E →L[ℝ] Y) (hT : Function.Bijective T) :
    ∀ᶠ S : E →L[ℝ] Y in 𝓝 T, Function.Bijective S := by
  let V := ContinuousLinearEquiv.ofBijective T (LinearMap.ker_eq_bot.mpr hT.1) (LinearMap.range_eq_top.mpr hT.2)
  let R := V.symm.toContinuousLinearMap
  have hRT : R.comp T = ContinuousLinearMap.id ℝ E := by ext x; exact V.symm_apply_apply x
  have hc : Continuous (fun S : E →L[ℝ] Y => ‖R.comp (T-S)‖) := by fun_prop
  have he : ∀ᶠ S : E →L[ℝ] Y in 𝓝 T, ‖R.comp (T-S)‖ < 1/2 :=
    hc.continuousAt.tendsto.eventually (gt_mem_nhds (by simp : ‖R.comp (T-T)‖ < (1/2 : ℝ)))
  filter_upwards [he] with S hS
  have hnear : ‖(ContinuousLinearMap.id ℝ E).comp
      (ContinuousLinearMap.id ℝ E-R.comp S)‖ ≤ (1/2 : ℝ) := by
    rw [ContinuousLinearMap.id_comp,←hRT,←ContinuousLinearMap.comp_sub]
    exact hS.le
  obtain ⟨Q,hQ,hQ',_⟩ := exists_inverse_norm_le_two_mul_of_composition_near
    (R.comp S) (ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E)
    (by ext x; rfl) (by ext x; rfl) hnear
  have hleft (x : E) : Q (R (S x)) = x :=
    congrArg (fun A : E →L[ℝ] E => A x) hQ'
  have hright (x : E) : R (S (Q x)) = x :=
    congrArg (fun A : E →L[ℝ] E => A x) hQ
  constructor
  · intro x y hxy
    rw [←hleft x,←hleft y,hxy]
  · intro y
    refine ⟨Q (R y),?_⟩
    apply V.symm.injective
    exact hright (R y)

/-- In a continuous connected family of SURJECTIVE Hilbert operators,
one bijective member forces every member to be bijective. The proof uses
persistence of a nonzero kernel vector, rather than an assumed index. -/
theorem bijective_connected_family_of_surjective
    {X E Y : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → E →L[ℝ] Y) (hF : Continuous F)
    (hs : ∀ x, Function.Surjective (F x)) (x₀ : X) (h₀ : Function.Injective (F x₀)) :
    ∀ x, Function.Bijective (F x) := by
  let A : Set X := {x | Function.Injective (F x)}
  have ho : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact (hF.continuousAt.tendsto.eventually
      (eventually_bijective_of_bijective (F x) ⟨hx,hs x⟩)).mono (fun _ h => h.1)
  have hn : IsOpen Aᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact hF.continuousAt.tendsto.eventually
      (eventually_not_injective_of_surjective (F x) (hs x) hx)
  have ha : A = univ := (show IsClopen A from ⟨isOpen_compl_iff.mp hn,ho⟩).eq_univ ⟨x₀,h₀⟩
  intro x
  refine ⟨?_,hs x⟩
  have hx : x ∈ A := by rw [ha]; exact mem_univ _
  exact hx

end NLS.FunctionalAnalysis
