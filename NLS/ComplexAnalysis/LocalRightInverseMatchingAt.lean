import NLS.ComplexAnalysis.LocalRightInverseMatching

/-! # Matching the SAME actual inverse at arbitrary local target bases -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.ComplexAnalysis

/-- A genuine strong analytic inverse germ matches the GIVEN weak
continuous inverse near ANY target base where both actual sources lie
in the same weak injectivity domain. The base need not be zero. -/
theorem exists_local_rightInverse_matching_at
    {E F P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (iE : E →L[ℂ] P) (iF : F →L[ℂ] Q) (f : P → Q)
    (U : Set P) (hU : IsOpen U) (hi : InjOn f U)
    (W : Set Q) (hW : IsOpen W) (R : Q → P) (hRc : ContinuousOn R W)
    (hRsolve : ∀ b∈W, f (R b)=b)
    (V : Set F) (hV : IsOpen V) (g : F → E) (hga : AnalyticOnNhd ℂ g V)
    (hgsolve : ∀ b∈V, f (iE (g b))=iF b)
    (b : F) (hbV : b∈V) (hbW : iF b∈W)
    (hnew : iE (g b)∈U) (hold : R (iF b)∈U) :
    ∃ T : Set F, IsOpen T ∧ b∈T ∧ T⊆V ∧ AnalyticOnNhd ℂ g T ∧
      ∀ c∈T, iF c∈W ∧ iE (g c)=R (iF c) := by
  let T0 := V∩iF ⁻¹' W
  have hT0 : IsOpen T0 := hV.inter (hW.preimage iF.continuous)
  have hNew : ContinuousOn (fun c => iE (g c)) T0 :=
    iE.continuous.comp_continuousOn (hga.continuousOn.mono inter_subset_left)
  have hOld : ContinuousOn (fun c => R (iF c)) T0 :=
    hRc.comp iF.continuous.continuousOn (fun _ hc => hc.2)
  let T1 := T0∩(fun c => iE (g c)) ⁻¹' U
  have hT1 : IsOpen T1 := hNew.isOpen_inter_preimage hT0 hU
  let T := T1∩(fun c => R (iF c)) ⁻¹' U
  have hT : IsOpen T := (hOld.mono inter_subset_left).isOpen_inter_preimage hT1 hU
  have hbT : b∈T := ⟨⟨⟨hbV,hbW⟩,hnew⟩,hold⟩
  have hTV : T⊆V := fun _ hc => hc.1.1.1
  refine ⟨T,hT,hbT,hTV,hga.mono hTV,?_⟩
  intro c hc
  exact ⟨hc.1.1.2,hi hc.1.2 hc.2 ((hgsolve c (hTV hc)).trans (hRsolve _ hc.1.1.2).symm)⟩

end NLS.ComplexAnalysis
