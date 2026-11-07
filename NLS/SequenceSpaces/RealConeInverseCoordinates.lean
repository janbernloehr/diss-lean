import NLS.SequenceSpaces.RealCoefficientCoordinates
import NLS.SequenceSpaces.NonnegativeActions

/-! Transport a relatively open dense REAL inverse locus to the original
Banach coordinates. Both inverse identities hold on full real neighborhoods. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem exists_original_real_inverse_locus
    {E S : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace S]
    (L : E ≃L[ℂ] Coeff 1) (e : S ≃ₜ nonnegativeLocus 1) (i : S → E)
    (hi : ∀ x, L (i x)=(e x).val) (x₀ : S) (hx₀ : i x₀=0)
    (U : Set (Coeff 1)) (F : Coeff 1 → Coeff 1)
    (hU : IsOpen U) (hCU : nonnegativeLocus 1⊆U) (hF : AnalyticOnNhd ℂ F U)
    (O : Set (nonnegativeLocus 1)) (hO : IsOpen O) (hdO : Dense O)
    (hzero : (⟨0,zero_mem_nonnegativeLocus 1⟩ : nonnegativeLocus 1)∈O)
    (hinv : ∀ x∈O, ComplexAnalysis.HasAnalyticInverse (𝕜 := ℝ)
      (realRestriction F) (reCLM 1 x.val)) :
    ∃ V : Set E, ∃ f : E → E, IsOpen V ∧ (∀ x, i x∈V) ∧ AnalyticOnNhd ℂ f V ∧
      (∀ a, f a=L.symm (F (L a))) ∧
      ∃ P : Set S, IsOpen P ∧ Dense P ∧ x₀∈P ∧
        ∀ x∈P, AnalyticAt ℝ (coordinateRestriction L f) (coordinateReCLM L (i x)) ∧
          ComplexAnalysis.HasAnalyticInverse (𝕜 := ℝ)
            (coordinateRestriction L f) (coordinateReCLM L (i x)) := by
  let V := L ⁻¹' U
  let f := fun a => L.symm (F (L a))
  have hf : AnalyticOnNhd ℂ f V := by
    intro a ha
    exact (L.symm.analyticAt _).comp ((hF (L a) ha).comp (L.analyticAt a))
  have hconj : (fun z => L (f (L.symm z)))=F := by
    funext z
    simp only [f,L.apply_symm_apply]
  refine ⟨V,f,hU.preimage L.continuous,(fun x => ?_),hf,(fun _ => rfl),
    e ⁻¹' O,hO.preimage e.continuous,?_,?_,?_⟩
  · change L (i x)∈U
    rw [hi]
    exact hCU (e x).property
  · intro x
    rw [←e.preimage_closure]
    exact hdO (e x)
  · have he : e x₀=⟨0,zero_mem_nonnegativeLocus 1⟩ := by
      apply Subtype.ext
      rw [←hi,hx₀,map_zero]
    change e x₀∈O
    rwa [he]
  · intro x hx
    have hr : L (i x)∈realLocus 1 := by
      rw [hi]
      exact fun n => ((e x).property n).1
    have hval := val_coordinateReCLM L (i x) hr
    constructor
    · apply analyticAt_coordinateRestriction L
      rw [hval]
      apply hf
      change L (i x)∈U
      rw [hi]
      exact hCU (e x).property
    · apply (hasAnalyticInverse_coordinateRestriction_iff L).mp
      rw [hconj,coordinateRealEquiv_coordinateReCLM,hi]
      exact hinv (e x) hx

end NLS.Coeff
