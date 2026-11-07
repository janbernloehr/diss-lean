import NLS.SequenceSpaces.CompactSobolevInclusion
import NLS.SequenceSpaces.AnalyticLinearPacketTransport

/-! Pull a stronger normalized packet back to an original action
Banach model. Exact raw coordinates and compact derivatives are retained. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

theorem exists_compact_weighted_packet_pullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (β ε : ℝ) (hε : 0<ε) (α : ℝ) (hα : -β=α)
    (N : E →L[ℂ] Coeff 1) (V : Set (Coeff 1)) (g : Coeff 1 → Coeff 1)
    (hV : IsOpen V) (hg : AnalyticOnNhd ℂ g V) (a0 : E) (ha0 : N a0∈V) :
    ∃ U : Set E, ∃ G : E → WeightedCoeff (Weight.sobolev α) 1,
      IsOpen U ∧ a0∈U ∧ (∀ a∈U, N a∈V) ∧ AnalyticOnNhd ℂ G U ∧
      (∀ a∈U, ∀ j : ℤ, (G a).val j=g (N a) j/(Weight.sobolev (-(β-ε)) j : ℂ)) ∧
      ∀ a∈U, IsCompactOperator (fderiv ℂ G a) := by
  subst α
  let K := (WeightedCoeff.weightIsometry (Weight.sobolev (-(β-ε))) 1).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let J := WeightedCoeff.sobolevInclusion (p := 1) (by linarith : -β≤-(β-ε))
  obtain ⟨U,P,hU,hC,hP,hUV,hPV⟩ := exists_analytic_linear_packet_transport N K V g hV hg
    {a0} (by intro a ha;rcases Set.mem_singleton_iff.mp ha with rfl;exact ha0)
  let G := fun a => J (P a)
  have hG : AnalyticOnNhd ℂ G U := analyticOnNhd_postcompose_clm J P U hP
  refine ⟨U,G,hU,hC (mem_singleton a0),hUV,hG,?_,?_⟩
  · intro a ha j
    change (J (P a)).val j=_
    rw [WeightedCoeff.sobolevInclusion_apply,hPV a ha]
    rfl
  · intro a ha
    exact isCompactOperator_fderiv_compact_clm J
      (WeightedCoeff.isCompactOperator_sobolevInclusion_strict (by linarith : -β < -(β-ε)))
      P a (hP a ha).differentiableAt

end NLS
