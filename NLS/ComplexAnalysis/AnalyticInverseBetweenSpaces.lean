import NLS.ComplexAnalysis.AnalyticOpenInverse

/-! # Analytic inverse branches between different native Banach spaces

A bounded derivative equivalence gives actual open source and target
neighborhoods, analytic inverse and both exact inverse identities. The
source and target need not be the same Sobolev space.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- An actual analytic inverse between possibly different Banach spaces,
on explicit open sets inside the original analytic domain. -/
theorem exists_analytic_inverse_between_open_sets
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    {x : E} (hx : x∈U) (i : E ≃L[ℂ] F)
    (hd : HasStrictFDerivAt f i.toContinuousLinearMap x) :
    ∃ V : Set E, ∃ W : Set F,
      IsOpen V ∧ IsOpen W ∧ x∈V ∧ f x∈W ∧ V⊆U ∧ f '' V=W ∧ Set.BijOn f V W ∧
      ∃ g : F → E, AnalyticOnNhd ℂ f V ∧ AnalyticOnNhd ℂ g W ∧
        (∀ y∈V, g (f y)=y) ∧ (∀ z∈W, g z∈V ∧ f (g z)=z) := by
  let P := hd.toOpenPartialHomeomorph f
  have hP : (P : E → F)=f := hd.toOpenPartialHomeomorph_coe
  have hxP : x∈P.source := hd.mem_toOpenPartialHomeomorph_source
  have hg : AnalyticAt ℂ P.symm (f x) := by
    have H := P.analyticAt_symm' hxP (by rw [hP];exact hf x hx)
      (i := i) (by rw [hP];exact hd.hasFDerivAt.fderiv)
    rwa [hP] at H
  let A : Set F := {y | AnalyticAt ℂ P.symm y}
  have hA : IsOpen A := isOpen_analyticAt ℂ P.symm
  let V := U ∩ (P.source ∩ P ⁻¹' A)
  have hV : IsOpen V := hU.inter (P.continuousOn.isOpen_inter_preimage P.open_source hA)
  let R := P.restrOpen V hV
  have hR : (R : E → F)=f := hP
  have hxR : x∈R.source :=
    ⟨hxP,hx,hxP,by simpa only [mem_preimage,mem_ofPred_eq,A,hP] using hg⟩
  have hsub : R.source⊆U := fun _ h => h.2.1
  have hgr : AnalyticOnNhd ℂ R.symm R.target := by
    intro y hy
    have hr : R.symm y∈R.source := R.map_target hy
    have ha : P (R.symm y)∈A := hr.2.2.2
    have he : P (R.symm y)=y := R.right_inv hy
    rw [he] at ha
    exact ha
  refine ⟨R.source,R.target,R.open_source,R.open_target,hxR,?_,hsub,?_,?_,
    R.symm,hf.mono hsub,hgr,?_,?_⟩
  · rw [←hR]
    exact R.map_source hxR
  · rw [←hR]
    exact R.image_source_eq_target
  · rw [←hR]
    exact R.bijOn
  · intro y hy
    rw [←hR]
    exact R.left_inv hy
  · intro z hz
    refine ⟨R.map_target hz,?_⟩
    rw [←hR]
    exact R.right_inv hz

section Matching
variable {E1 E0 F1 F0 : Type*}
  [NormedAddCommGroup E1] [NormedSpace ℂ E1]
  [NormedAddCommGroup E0] [NormedSpace ℂ E0]
  [NormedAddCommGroup F1] [NormedSpace ℂ F1]
  [NormedAddCommGroup F0] [NormedSpace ℂ F0]

/-- Match an analytic inverse in stronger spaces to a GIVEN continuous
rough branch, using actual local uniqueness in the weaker spaces. -/
theorem exists_strong_analytic_branch_of_local_inverses
    (f : E1 → F1) (f0 : E0 → F0) (iE : E1 →L[ℂ] E0) (iF : F1 →L[ℂ] F0)
    (hcomm : ∀ a, f0 (iE a)=iF (f a))
    (U : Set F0) (hU : IsOpen U) (G : F0 → E0) (hGc : ContinuousOn G U)
    (hsolve : ∀ p∈U, f0 (G p)=p)
    (WS : Set F1) (hWS : IsOpen WS) (g : F1 → E1) (hga : AnalyticOnNhd ℂ g WS)
    (hright : ∀ p∈WS, f (g p)=p)
    (VW : Set E0) (hVW : IsOpen VW) (gw : F0 → E0) (hleftw : ∀ v∈VW, gw (f0 v)=v)
    (q : F1) (hqWS : q∈WS) (hqU : iF q∈U)
    (hbase : iE (g q)=G (iF q)) (hvVW : G (iF q)∈VW) :
    ∃ V : Set F1, IsOpen V ∧ q∈V ∧ AnalyticOnNhd ℂ g V ∧
      ∀ p∈V, iF p∈U ∧ iE (g p)=G (iF p) ∧ f (g p)=p := by
  let T : Set F1 := WS ∩ iF ⁻¹' U
  have hT : IsOpen T := hWS.inter (hU.preimage iF.continuous)
  have hNew : ContinuousOn (fun p => iE (g p)) T :=
    iE.continuous.comp_continuousOn (hga.continuousOn.mono inter_subset_left)
  have hOld : ContinuousOn (fun p => G (iF p)) T :=
    hGc.comp iF.continuous.continuousOn (fun _ hp => hp.2)
  let T1 := T ∩ (fun p => iE (g p)) ⁻¹' VW
  have hT1 : IsOpen T1 := hNew.isOpen_inter_preimage hT hVW
  let V := T1 ∩ (fun p => G (iF p)) ⁻¹' VW
  have hV : IsOpen V := (hOld.mono inter_subset_left).isOpen_inter_preimage hT1 hVW
  have hqV : q∈V := ⟨⟨⟨hqWS,hqU⟩,by change iE (g q)∈VW;rw [hbase];exact hvVW⟩,hvVW⟩
  refine ⟨V,hV,hqV,hga.mono (fun _ hp => hp.1.1.1),?_⟩
  intro p hp
  have hpWS : p∈WS := hp.1.1.1
  have hpU : iF p∈U := hp.1.1.2
  have hn := hleftw (iE (g p)) hp.1.2
  have ho := hleftw (G (iF p)) hp.2
  rw [hcomm,hright p hpWS] at hn
  rw [hsolve (iF p) hpU] at ho
  exact ⟨hpU,hn.symm.trans ho,hright p hpWS⟩

end Matching
end NLS.ComplexAnalysis
