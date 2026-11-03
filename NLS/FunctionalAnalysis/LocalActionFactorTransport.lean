import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear

/-! # Transporting local holomorphic factors through linear coordinates -/
noncomputable section
open Set
namespace NLS

variable {E E' X F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']

/-- Transport both the real coordinates and the complex action norm. The
action map itself need only satisfy the exact commuting identity. -/
theorem local_action_factor_transport
    (R : E ≃L[ℝ] E') (J : E' →L[ℝ] X) (A : F ≃L[ℂ] F')
    (Q : X → F') (I : E → F) (hI : ∀ z, A (I z) = Q (J (R z)))
    (f : E → ℂ) (z₀ : E)
    (hf : ∃ Z : Set X, ∃ T : Set F', ∃ g : F' → ℂ,
      IsOpen Z ∧ J (R z₀) ∈ Z ∧ IsOpen T ∧ Q '' Z = T ∧ AnalyticOnNhd ℂ g T ∧
      ∀ y : E', J y ∈ Z → g (Q (J y)) = f (R.symm y)) :
    ∃ V : Set E, ∃ T : Set F, ∃ H : F → ℂ,
      IsOpen V ∧ z₀ ∈ V ∧ IsOpen T ∧ MapsTo I V T ∧
      AnalyticOnNhd ℂ H T ∧ ∀ z ∈ V, H (I z) = f z := by
  obtain ⟨Z,T,g,hZ,hbase,hT,himage,hg,hrec⟩ := hf
  let V := (fun z => J (R z)) ⁻¹' Z
  refine ⟨V,A ⁻¹' T,fun a => g (A a),hZ.preimage (J.continuous.comp R.continuous),hbase,
    hT.preimage A.continuous,?_,?_,?_⟩
  · intro z hz
    change A (I z) ∈ T
    rw [hI,← himage]
    exact ⟨J (R z),hz,rfl⟩
  · intro a ha
    exact (hg _ ha).comp (A.analyticAt a)
  · intro z hz
    change g (A (I z)) = _
    rw [hI]
    exact (hrec (R z) hz).trans (congrArg f (R.symm_apply_apply z))

end NLS
