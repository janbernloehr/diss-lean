import NLS.KdV.HillInfiniteNormingGardner
import NLS.Fourier.ACPeriodicUnitCoefficients

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- Both actual endpoints vanish for the complete absolutely convergent
physical norming cotangent; no finite replacement of the series is used. -/
theorem hillInfiniteNormingGradient_endpoints
    (q : RealPeriodOneHillPotential) (c : ℕ → ℂ) (hc : Summable (fun j => ‖c j‖)) :
    hillInfiniteNormingGradient q c ⟨0,by norm_num⟩=0 ∧
      hillInfiniteNormingGradient q c ⟨1,by norm_num⟩=0 := by
  have hs := (hillNormingGradientSeries_norm_summable h0q h0r q c hc).1.of_norm
  have he (t : Icc (0 : ℝ) 1)
      (ht : ∀ j : ℕ, hillLogNormingGradientCurve q (j+1) (by omega) t=0) :
      hillInfiniteNormingGradient q c t=0 := by
    change (ContinuousMap.evalCLM ℂ t) (∑' j : ℕ,c j • hillLogNormingGradientCurve q (j+1) (by omega))=0
    rw [(ContinuousMap.evalCLM ℂ t).map_tsum hs]
    simp only [map_smul,ContinuousMap.evalCLM_apply,ht,smul_zero,tsum_zero]
  exact ⟨he _ (fun j => (hillLogNormingGradientCurve_endpoints q (j+1) (by omega)).1),
    he _ (fun j => (hillLogNormingGradientCurve_endpoints q (j+1) (by omega)).2)⟩

/-- The genuine unit-period weighted H1 Fourier cotangent of the full
physical infinite norming combination, with literal original unit integrals. -/
def hillInfiniteNormingUnitCotangent
    (q : RealPeriodOneHillPotential) (c : ℕ → ℂ) (hc : Summable (fun j => ‖c j‖)) :
    WeightedCoeff (Weight.sobolev 1) 2 :=
  Fourier.acPeriodicUnitCoefficients
    (extend (hillInfiniteNormingGradient q c)) (extend (hillInfiniteNormingGradientSpatial q c))
    (continuous_extend _) (hillInfiniteNormingGradient_H1 h0q h0r q c hc).1 (continuous_extend _)
    (ae_hasDerivAt_hillInfiniteNormingGradient h0q h0r q c hc) (by
      have he := hillInfiniteNormingGradient_endpoints h0q h0r q c hc
      rw [show extend (hillInfiniteNormingGradient q c) 1=hillInfiniteNormingGradient q c ⟨1,by norm_num⟩ from extend_coe _ ⟨1,by norm_num⟩,
        show extend (hillInfiniteNormingGradient q c) 0=hillInfiniteNormingGradient q c ⟨0,by norm_num⟩ from extend_coe _ ⟨0,by norm_num⟩,he.1,he.2])

/-- Each actual cotangent coefficient is the literal unit Fourier integral,
with no potential-dependent rescaling or chosen representative. -/
theorem hillInfiniteNormingUnitCotangent_apply
    (q : RealPeriodOneHillPotential) (c : ℕ → ℂ) (hc : Summable (fun j => ‖c j‖)) (k : ℤ) :
    (hillInfiniteNormingUnitCotangent h0q h0r q c hc).val k=
      Fourier.unitFourierCoefficient (extend (hillInfiniteNormingGradient q c)) k := rfl

/-- The actual bounded scalar Gardner bivector on these full H1 Fourier
cotangents equals the original physical derivative integral and vanishes. -/
theorem hillInfiniteNormingUnitCotangent_Gardner_eq_zero
    (q : RealPeriodOneHillPotential) (c d : ℕ → ℂ)
    (hc : Summable (fun j => ‖c j‖)) (hd : Summable (fun j => ‖d j‖)) :
    NLS.Poisson.gardnerBivector (hillInfiniteNormingUnitCotangent h0q h0r q c hc)
      (hillInfiniteNormingUnitCotangent h0q h0r q d hd)=0 := by
  have he := hillInfiniteNormingGradient_endpoints h0q h0r q d hd
  rw [Fourier.gardnerBivector_eq_integral_of_ac_coefficients _ _
    (extend (hillInfiniteNormingGradient q c)) (extend (hillInfiniteNormingGradient q d))
    (extend (hillInfiniteNormingGradientSpatial q d)) (continuous_extend _) (continuous_extend _)
    (continuous_extend _) (hillInfiniteNormingGradient_H1 h0q h0r q d hd).1
    (ae_hasDerivAt_hillInfiniteNormingGradient h0q h0r q d hd) (by
      rw [show extend (hillInfiniteNormingGradient q d) 1=hillInfiniteNormingGradient q d ⟨1,by norm_num⟩ from extend_coe _ ⟨1,by norm_num⟩,
        show extend (hillInfiniteNormingGradient q d) 0=hillInfiniteNormingGradient q d ⟨0,by norm_num⟩ from extend_coe _ ⟨0,by norm_num⟩,he.1,he.2])
    (fun _ => rfl) (fun _ => rfl)]
  have hi : (∫ x in (0 : ℝ)..1,extend (hillInfiniteNormingGradient q c) x*
      extend (hillInfiniteNormingGradientSpatial q d) x)=
      ∫ x in (0 : ℝ)..1,extend (hillInfiniteNormingGradient q c) x*deriv (extend (hillInfiniteNormingGradient q d)) x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
    filter_upwards [ae_hasDerivAt_hillInfiniteNormingGradient h0q h0r q d hd] with x hx
    rw [hx.deriv]
  exact hi.trans (hillInfiniteNormingGradient_GardnerBracket_eq_zero h0q h0r q c d hc hd)

end NLS.KdV
