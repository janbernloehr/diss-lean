import Mathlib.Analysis.InnerProductSpace.PiL2

/-! An actual unit vector can be prescribed as the first member of an
orthonormal basis of a two-dimensional complex inner-product space. -/
noncomputable section
open Set
namespace NLS.FunctionalAnalysis

/-- A rank-two Hilbert space has an orthonormal basis starting with any
specified unit vector. No orthogonal-complement vector is assumed. -/
theorem exists_orthonormalBasis_fin_two_first {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (hd : Module.finrank ℂ E = 2) (x : E) (hx : ‖x‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 2) ℂ E, b 0 = x := by
  have ho : Orthonormal ℂ (({0}:Set (Fin 2)).domRestrict (fun _ => x)) := by
    rw [orthonormal_subsingleton_iff]
    exact fun _ => hx
  obtain ⟨b,hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simpa using hd)
  exact ⟨b,hb 0 (by simp)⟩

end NLS.FunctionalAnalysis
