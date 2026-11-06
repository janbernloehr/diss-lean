import NLS.ComplexAnalysis.RealAnalyticNativeInverseNeighborhoods

/-! # Transfer of a native analytic inverse to the unique weaker-space preimage -/
noncomputable section
open Set
namespace NLS.ComplexAnalysis
variable {E F A B : Type*} [TopologicalSpace F] [Zero F]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Compatibility with bounded inclusions identifies a stronger analytic
inverse with every weaker-space preimage near a globally unique fiber. -/
theorem exists_analytic_inverse_regularity_neighborhood
    (f : E → F) (fA : A → B) (J : A → E) (K : B → F)
    (hK : Continuous K) (hK0 : K 0 = 0) (hc : ∀ a, K (fA a) = f (J a))
    {V : Set B} (hV : IsOpen V) (h0V : (0 : B) ∈ V) (G : B → A)
    (hGA : AnalyticOnNhd ℝ G V) (hr : ∀ z ∈ V, fA (G z) = z)
    {W : Set F} (hW : IsOpen W) (h0W : (0 : F) ∈ W) (hu : ∀ y ∈ W, ∃! a, f a = y) :
    ∃ T : Set B, IsOpen T ∧ (0 : B) ∈ T ∧ AnalyticOnNhd ℝ G T ∧
      ∀ z ∈ T, fA (G z) = z ∧ ∀ a, f a = K z ↔ a = J (G z) := by
  let T := V ∩ K ⁻¹' W
  have h0T : (0 : B) ∈ T := ⟨h0V,by simpa only [mem_preimage,hK0] using h0W⟩
  refine ⟨T,hV.inter (hW.preimage hK),h0T,fun z hz => hGA z hz.1,?_⟩
  intro z hz
  have hGz := hr z hz.1
  refine ⟨hGz,?_⟩
  have hL : f (J (G z)) = K z := (hc (G z)).symm.trans (congrArg K hGz)
  obtain ⟨b,_,hb⟩ := hu _ hz.2
  intro a
  constructor
  · intro ha
    exact (hb a ha).trans (hb _ hL).symm
  · rintro rfl
    exact hL

end NLS.ComplexAnalysis
