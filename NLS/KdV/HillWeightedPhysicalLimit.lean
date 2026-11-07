import NLS.KdV.HillPeriodOneRestrictionInverse
import NLS.KdV.HillLocallyUniformActionTails
import NLS.SequenceSpaces.WeightedCoefficientLimit

/-! Physical L² limits of bounded original weighted potentials retain their
weight. Membership is concluded, rather than assumed of the limit. -/
noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS.KdV

theorem hillRealWeightedEmbedding_coefficient (w : SpectralWeight)
    (p : RealHillWeightedPotential w) (k : ℤ) :
    (hillRealWeightedEmbedding w p).val.val (2*k) = p.val.val k := by
  have h := congrArg (fun a : Coeff 2 => a (2*k)) (toCoeff_hillPeriodOneUnitPotential w p.val)
  simpa only [hillRealWeightedEmbedding,SpectralWeight.toCoeff_apply,hillPeriodOnePotential_even] using h

/-- A uniform weighted bound and physical L² convergence imply weighted
membership of the actual physical limit, with the same bound. -/
theorem exists_hillRealWeighted_of_bounded_tendsto
    {α : Type*} {l : Filter α} [NeBot l] (w : SpectralWeight)
    (p : α → RealHillWeightedPotential w) (q : RealPeriodOneHillPotential)
    (C : ℝ) (hb : ∀ i, ‖(p i).val‖ ≤ C)
    (ht : Tendsto (fun i => hillRealWeightedEmbedding w (p i)) l (𝓝 q)) :
    ∃ b : RealHillWeightedPotential w, hillRealWeightedEmbedding w b = q ∧ ‖b.val‖ ≤ C := by
  have hc (k : ℤ) : Tendsto (fun i => (p i).val.val k) l (𝓝 (q.val.val (2*k))) := by
    have h := (((WeightedCoeff.evalCLM SpectralWeight.one.toWeight 2 (2*k)).continuous.comp
      continuous_subtype_val).continuousAt.tendsto.comp ht)
    simpa only [Function.comp_def,WeightedCoeff.evalCLM_apply,hillRealWeightedEmbedding_coefficient] using h
  obtain ⟨b,hbq,hbn⟩ := WeightedCoeff.exists_of_bounded_coefficientwise_tendsto
    w.doubleIndex.toWeight (fun i => (p i).val) (fun k => q.val.val (2*k)) C hb hc
  have hr : IsRealHillPotential (w.doubleIndex.toCoeff b) := by
    intro k
    simpa only [SpectralWeight.toCoeff_apply,hbq,mul_neg] using q.property.2 (2*k)
  refine ⟨⟨b,hr⟩,?_,hbn⟩
  apply Subtype.ext
  apply Subtype.ext
  funext k
  by_cases hk : k%2=0
  · have he : k=2*(k/2) := by omega
    rw [he,hillRealWeightedEmbedding_coefficient,hbq]
  · have hleft := (Coeff.mem_paritySubspace 0 _).mp
      (hillRealWeightedEmbedding w ⟨b,hr⟩).property.1 k hk
    have hright := (Coeff.mem_paritySubspace 0 _).mp q.property.1 k hk
    simpa only [SpectralWeight.toCoeff_apply] using hleft.trans hright.symm

end NLS.KdV
