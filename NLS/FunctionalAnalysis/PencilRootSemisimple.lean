import NLS.FunctionalAnalysis.LinearPMapRootSpace

/-!
# Semisimple pencils on an unchanged domain

An injective domain inclusion identifies the original pencil kernel with the
first base-space root level. Excluding length-two associated vectors collapses
every actual finite domain chain, and hence the full root space, to this level.
-/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {D E : Type*} [AddCommGroup D] [Module ℂ D] [AddCommGroup E] [Module ℂ E]

/-- The original domain kernel is exactly the first base-space root level. -/
def pencilKerRootEquiv (J P : D →ₗ[ℂ] E) (hJ : Function.Injective J) :
    LinearMap.ker P ≃ₗ[ℂ] pencilRootSpace J P 1 :=
  LinearEquiv.ofBijective
    { toFun := fun f => ⟨J f.val, (mem_pencilRootSpace_succ J P 0 _).mpr
        ⟨f.val, rfl, f.property⟩⟩
      map_add' := by intro f g; apply Subtype.ext; exact J.map_add _ _
      map_smul' := by intro c f; apply Subtype.ext; exact J.map_smul c _ }
    ⟨by
      intro f g h
      exact Subtype.ext (hJ (congrArg Subtype.val h)), by
      intro x
      obtain ⟨f, hf, hP⟩ := (mem_pencilRootSpace_succ J P 0 x.val).mp x.property
      exact ⟨⟨f, hP⟩, Subtype.ext hf⟩⟩

/-- If a pencil has no nonzero associated eigenvector, all its finite domain
chains lie in the actual first root level. -/
theorem pencilRootSpace_le_one_of_no_associated (J P : D →ₗ[ℂ] E)
    (h : ∀ f g : D, P f = 0 → P g = J f → f = 0) (n : ℕ) :
    pencilRootSpace J P n ≤ pencilRootSpace J P 1 := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    intro x hx
    obtain ⟨f, hf, hprev⟩ := (mem_pencilRootSpace_succ J P n x).mp hx
    obtain ⟨g, hg, hPg⟩ := (mem_pencilRootSpace_succ J P 0 (P f)).mp (ih hprev)
    have hg0 : g = 0 := h g f hPg hg.symm
    apply (mem_pencilRootSpace_succ J P 0 x).mpr
    refine ⟨f, hf, ?_⟩
    change P f = 0
    rw [← hg, hg0, map_zero]

/-- No nonzero associated eigenvector implies equality of the full algebraic
root space with the actual eigenspace in the base space. -/
theorem pencilRootSpaceTop_eq_one_of_no_associated (J P : D →ₗ[ℂ] E)
    (h : ∀ f g : D, P f = 0 → P g = J f → f = 0) :
    pencilRootSpaceTop J P = pencilRootSpace J P 1 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := (mem_pencilRootSpaceTop J P x).mp hx
    exact pencilRootSpace_le_one_of_no_associated J P h n hn
  · exact le_iSup (pencilRootSpace J P) 1

end NLS.FunctionalAnalysis
