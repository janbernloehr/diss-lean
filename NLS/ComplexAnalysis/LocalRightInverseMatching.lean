import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic

/-! # Matching local analytic right inverses by weak uniqueness

Only the actual local right-inverse identities are required. In particular,
commutation of a stronger extension outside its analytic neighborhood is
not assumed. Continuity puts both branches in one weak injectivity domain.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.ComplexAnalysis

/-- A strong analytic right inverse agrees near zero with a GIVEN weak
continuous right inverse whenever both solve the same weak local problem. -/
theorem exists_local_rightInverse_matching
    {E F P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (iE : E →L[ℂ] P) (iF : F →L[ℂ] Q) (f : P → Q)
    (U : Set P) (hU : IsOpen U) (h0U : (0 : P)∈U) (hi : InjOn f U)
    (W : Set Q) (hW : IsOpen W) (h0W : (0 : Q)∈W)
    (R : Q → P) (hRc : ContinuousOn R W) (hR0 : R 0=0)
    (hRsolve : ∀ b∈W, f (R b)=b)
    (V : Set F) (hV : IsOpen V) (h0V : (0 : F)∈V)
    (g : F → E) (hga : AnalyticOnNhd ℂ g V) (hg0 : g 0=0)
    (hgsolve : ∀ b∈V, f (iE (g b))=iF b) :
    ∃ T : Set F, IsOpen T ∧ 0∈T ∧ T⊆V ∧ AnalyticOnNhd ℂ g T ∧
      ∀ b∈T, iF b∈W ∧ iE (g b)=R (iF b) := by
  let T0 := V∩iF ⁻¹' W
  have hT0 : IsOpen T0 := hV.inter (hW.preimage iF.continuous)
  have h0T0 : (0 : F)∈T0 := ⟨h0V,by simpa only [mem_preimage,map_zero] using h0W⟩
  have hNew : ContinuousOn (fun b => iE (g b)) T0 :=
    iE.continuous.comp_continuousOn (hga.continuousOn.mono inter_subset_left)
  have hOld : ContinuousOn (fun b => R (iF b)) T0 :=
    hRc.comp iF.continuous.continuousOn (fun _ hb => hb.2)
  let T1 := T0∩(fun b => iE (g b)) ⁻¹' U
  have hT1 : IsOpen T1 := hNew.isOpen_inter_preimage hT0 hU
  let T := T1∩(fun b => R (iF b)) ⁻¹' U
  have hT : IsOpen T := (hOld.mono inter_subset_left).isOpen_inter_preimage hT1 hU
  have h0T : (0 : F)∈T := by
    refine ⟨⟨h0T0,?_⟩,?_⟩
    · change iE (g 0)∈U
      simpa only [hg0,map_zero] using h0U
    · change R (iF 0)∈U
      simpa only [map_zero,hR0] using h0U
  have hsub : T⊆V := fun _ hb => hb.1.1.1
  refine ⟨T,hT,h0T,hsub,hga.mono hsub,?_⟩
  intro b hb
  exact ⟨hb.1.1.2,hi hb.1.2 hb.2 ((hgsolve b (hsub hb)).trans (hRsolve _ hb.1.1.2).symm)⟩

end NLS.ComplexAnalysis
