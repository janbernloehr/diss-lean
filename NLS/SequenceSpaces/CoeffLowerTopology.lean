import NLS.SequenceSpaces.WeightedWeakStarLowerTopology
import NLS.SequenceSpaces.ExponentEmbedding

/-! Raw coefficient-preserving lower-norm embeddings from any Banach
coefficient exponent. Uniform coefficient boundedness, available from a
source norm bound, turns coordinate limits into lower Sobolev norm limits. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

def endpointOfCoefficients : Coeff p →L[ℂ] WeightedCoeff (Weight.sobolev 0) ⊤ :=
  (weightIsometry (Weight.sobolev 0) ⊤).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (Coeff.exponentInclusion (le_top : p ≤ ⊤))

theorem endpointOfCoefficients_apply (a : Coeff p) (n : ℤ) :
    (endpointOfCoefficients a).val n=a n := by
  change Coeff.exponentInclusion le_top a n/(Weight.sobolev 0 n:ℂ)= _
  rw [Coeff.exponentInclusion_apply]
  simp only [Weight.sobolev_apply,Real.rpow_zero,Complex.ofReal_one,div_one]

theorem norm_endpointOfCoefficients_le (a : Coeff p) :
    ‖endpointOfCoefficients a‖ ≤ ‖a‖ := by
  change ‖(weightIsometry (Weight.sobolev 0) ⊤).symm (Coeff.exponentInclusion le_top a)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact Coeff.norm_exponentInclusion_le le_top a

def lowerOfCoefficients (t : ℝ) (hq : q ≠ ⊤) (h : 1 < (0-t)*q.toReal) :
    Coeff p →L[ℂ] WeightedCoeff (Weight.sobolev t) q :=
  (endpointLowerInclusion 0 t hq h).comp endpointOfCoefficients

theorem lowerOfCoefficients_apply (t : ℝ) (hq : q ≠ ⊤) (h : 1 < (0-t)*q.toReal)
    (a : Coeff p) (n : ℤ) : (lowerOfCoefficients t hq h a).val n=a n := by
  change (endpointLowerInclusion 0 t hq h (endpointOfCoefficients a)).val n= _
  rw [endpointLowerInclusion_apply,endpointOfCoefficients_apply]

theorem tendsto_lowerOfCoefficients_of_bounded_coefficients
    (t : ℝ) (hq : q ≠ ⊤) (h : 1 < (0-t)*q.toReal)
    {α : Type*} {l : Filter α} (a : α → Coeff p) (b : Coeff p)
    (hb : Bornology.IsBounded (range a))
    (ht : ∀ n : ℤ, Tendsto (fun k => a k n) l (𝓝 (b n))) :
    Tendsto (fun k => lowerOfCoefficients t hq h (a k)) l (𝓝 (lowerOfCoefficients t hq h b)) := by
  have hb' : Bornology.IsBounded (range (fun k => endpointOfCoefficients (a k))) := by
    obtain ⟨C,hC⟩ := hb.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨C,?_⟩
    rintro _ ⟨k,rfl⟩
    exact (norm_endpointOfCoefficients_le _).trans (hC _ ⟨k,rfl⟩)
  exact tendsto_lowerInclusion_of_bounded_coefficients 0 t hq h
    (fun k => endpointOfCoefficients (a k)) (endpointOfCoefficients b) hb'
    (fun n => by simpa only [endpointOfCoefficients_apply] using ht n)

end NLS.WeightedCoeff
