import NLS.ComplexAnalysis.HolomorphicCircleIntegral

/-! # The Cauchy formula for a Banach-space Fréchet derivative

Differentiate the affine-line Cauchy formula in the base point. This gives
an operator-valued Cauchy identity using only complex differentiability of
the original map, without assuming differentiability of its derivative.
-/
noncomputable section
open Set Metric Filter Topology Complex
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The Fréchet derivative satisfies the Cauchy identity along affine lines.
A common neighborhood of base points keeps the closed scalar disc in the domain. -/
theorem circleIntegral_fderiv_affineLine
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (a v : E) (R : ℝ) (hR : 0 < R) (V : Set E) (hV : IsOpen V) (ha : a ∈ V)
    (hinto : ∀ b ∈ V, ∀ z ∈ closedBall (0 : ℂ) R, b+z • v ∈ U)
    (w : ℂ) (hw : w ∈ ball 0 R) :
    (∮ z in C(0,R), (z-w)⁻¹ • fderiv ℂ f (a+z • v)) =
      (2*Real.pi*Complex.I : ℂ) • fderiv ℂ f (a+w • v) := by
  let K : ℂ × E → F := fun p => (p.1-w)⁻¹ • f (p.2+p.1 • v)
  let D : Set (ℂ × E) := {p | p.1 ≠ w ∧ p.2+p.1 • v ∈ U}
  have hD : IsOpen D :=
    (isOpen_ne.preimage continuous_fst).inter
      (hU.preimage (continuous_snd.add (continuous_fst.smul continuous_const)))
  have hK : DifferentiableOn ℂ K D := by
    intro p hp
    have hfp := (hf _ hp.2).differentiableAt (hU.mem_nhds hp.2)
    exact (((differentiableAt_fst.sub_const w).inv (sub_ne_zero.mpr hp.1)).smul
      (hfp.comp p (differentiableAt_snd.add (differentiableAt_fst.smul_const v)))).differentiableWithinAt
  have hcircle (z : ℂ) (hz : z ∈ sphere 0 R) : (z,a) ∈ D := by
    refine ⟨?_,hinto a ha z (sphere_subset_closedBall hz)⟩
    intro he
    change z = w at he
    subst z
    exact (ne_of_lt hw) hz
  have hmain := hasFDerivAt_circleIntegral_of_jointDifferentiable K D hD hK 0 R hR.le a hcircle
  have hsection (z : ℂ) (hz : z ∈ sphere 0 R) :
      (fderiv ℂ K (z,a)).comp (ContinuousLinearMap.inr ℂ ℂ E) =
        (z-w)⁻¹ • fderiv ℂ f (a+z • v) := by
    rw [← fderiv_source_section_eq_joint K z a
      ((hK _ (hcircle z hz)).differentiableAt (hD.mem_nhds (hcircle z hz)))]
    have hfa := (hf _ (hinto a ha z (sphere_subset_closedBall hz))).differentiableAt
      (hU.mem_nhds (hinto a ha z (sphere_subset_closedBall hz)))
    exact ((hasFDerivAt_comp_add_right (z • v)).mpr hfa.hasFDerivAt).const_smul (z-w)⁻¹ |>.fderiv
  have hderEq :
      (∮ z in C(0,R), (fderiv ℂ K (z,a)).comp (ContinuousLinearMap.inr ℂ ℂ E)) =
      (∮ z in C(0,R), (z-w)⁻¹ • fderiv ℂ f (a+z • v)) :=
    circleIntegral.integral_congr hR.le hsection
  rw [hderEq] at hmain
  have hline (b : E) (hb : b ∈ V) :
      DifferentiableOn ℂ (fun z : ℂ => f (b+z • v)) (closedBall 0 R) := by
    intro z hz
    exact (((hf _ (hinto b hb z hz)).differentiableAt (hU.mem_nhds (hinto b hb z hz))).comp z
      ((differentiableAt_const b).add (differentiableAt_id.smul_const v))).differentiableWithinAt
  have heq : (fun b => (2*Real.pi*Complex.I : ℂ) • f (b+w • v)) =ᶠ[𝓝 a]
      (fun b => ∮ z in C(0,R), K (z,b)) := by
    filter_upwards [hV.mem_nhds ha] with b hb
    exact ((hline b hb).circleIntegral_sub_inv_smul hw).symm
  have hfa := (hf _ (hinto a ha w (ball_subset_closedBall hw))).differentiableAt
    (hU.mem_nhds (hinto a ha w (ball_subset_closedBall hw)))
  have hrhs := ((hasFDerivAt_comp_add_right (w • v)).mpr hfa.hasFDerivAt).const_smul
    (2*Real.pi*Complex.I : ℂ)
  exact (hmain.congr_of_eventuallyEq heq).unique hrhs

end NLS.ComplexAnalysis
