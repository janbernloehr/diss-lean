import NLS.SequenceSpaces.CompactSobolevInclusion
import NLS.SequenceSpaces.NonnegativeActionIdentity
import NLS.SequenceSpaces.AnalyticLinearPacketTransport

/-! Compact derivatives survive exact bounded linear changes of Banach
coordinates. A local cone calibration identifies the corrected derivative
in the full positive-frequency model, including boundary actions. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS

theorem isCompactOperator_fderiv_linear_transport
    {E X Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (J : E →L[ℂ] X) (K : Y →L[ℂ] Z) (f : X → Y) (a : E)
    (hf : DifferentiableAt ℂ f (J a)) (hc : IsCompactOperator (fderiv ℂ f (J a))) :
    IsCompactOperator (fderiv ℂ (fun b => K (f (J b))) a) := by
  have hd := K.hasFDerivAt.comp a (hf.hasFDerivAt.comp a J.hasFDerivAt)
  change IsCompactOperator (fderiv ℂ (K ∘ f ∘ J) a)
  rw [hd.fderiv]
  exact (hc.comp_clm J).clm_comp K

theorem exists_analytic_compact_linear_transport
    {E X Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (J : E →L[ℂ] X) (K : Y →L[ℂ] Z) (U : Set X) (f : X → Y)
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hc : ∀ x∈U, IsCompactOperator (fderiv ℂ f x))
    (a0 : E) (ha0 : J a0∈U) :
    ∃ V : Set E, ∃ g : E → Z, IsOpen V ∧ a0∈V ∧ AnalyticOnNhd ℂ g V ∧
      (∀ a∈V, J a∈U) ∧ (∀ a∈V, g a=K (f (J a))) ∧
      ∀ a∈V, IsCompactOperator (fderiv ℂ g a) := by
  obtain ⟨V,g,hV,hcenter,hg,hVU,he⟩ := exists_analytic_linear_packet_transport J K U f hU hf {a0}
    (by intro a ha;rcases Set.mem_singleton_iff.mp ha with rfl;exact ha0)
  refine ⟨V,g,hV,hcenter (mem_singleton a0),hg,hVU,he,?_⟩
  intro a ha
  have heN : g=ᶠ[𝓝 a] (fun b => K (f (J b))) := by
    filter_upwards [hV.mem_nhds ha] with b hb
    exact he b hb
  rw [heN.fderiv_eq]
  exact isCompactOperator_fderiv_linear_transport J K f a (hf _ (hVU a ha)).differentiableAt (hc _ (hVU a ha))

namespace Coeff

theorem isCompactOperator_corrected_fderiv_of_local_cone_calibration
    (U V : Set (Coeff 1)) (hV : IsOpen V) (hVU : V⊆U)
    (f g : Coeff 1 → Coeff 1) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g V)
    (c : ℂ) (a : Coeff 1) (ha : a∈V) (hapos : a∈nonnegativeLocus 1)
    (hc : IsCompactOperator (fderiv ℂ g a))
    (he : ∀ b∈V, b∈nonnegativeLocus 1 → f b+c • b=g b) :
    IsCompactOperator (fderiv ℂ f a+c • ContinuousLinearMap.id ℂ (Coeff 1)) := by
  have hfa : AnalyticOnNhd ℂ (fun b => f b+c • b) V :=
    (hf.mono hVU).add (analyticOnNhd_const.smul analyticOnNhd_id)
  have heN := eventuallyEq_of_nonnegativeActions_agreement (p := 2) (q := 1) (by norm_num)
    (fun b => f b+c • b) g V hV a ha hapos hfa.differentiableOn hg.differentiableOn he
  have hd : HasFDerivAt (fun b => f b+c • b)
      (fderiv ℂ f a+c • ContinuousLinearMap.id ℂ (Coeff 1)) a :=
    (hf a (hVU ha)).differentiableAt.hasFDerivAt.add ((hasFDerivAt_id a).const_smul c)
  rw [←hd.fderiv,heN.fderiv_eq]
  exact hc

end Coeff
end NLS
