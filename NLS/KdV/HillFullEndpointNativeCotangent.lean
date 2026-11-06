import NLS.KdV.HillFullEndpointPhase
import NLS.KdV.HillInfiniteNativeCotangents
import NLS.KdV.HillNativeCotangentExtension
import NLS.KdV.HillUnitWeightLift

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



/-- The complete actual physical endpoint phase has an H-minus-one
cotangent extension of its original Hilbert differential. Its H1 Fourier
gradient is the literal unit coefficient sequence of the proved infinite
physical cotangent, with every phase and endpoint normalization retained. -/
theorem exists_hillFullPhysicalPhase_endpoint_native_cotangent
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0)
    (hterminal : ∀ k : ℕ, ∀ hk : 1≤k,
      hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0) :
    ∃ Θ ε : Coeff 2 → ℂ, ∃ c : ℕ → ℂ, ∃ a : WeightedCoeff (Weight.sobolev 1) 2,
      AnalyticAt ℂ Θ (SpectralWeight.one.toCoeff q.val) ∧
      AnalyticAt ℂ ε (SpectralWeight.one.toCoeff q.val) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        hillRealGapHalfLength p.val p.property.1 p.property.2 n≠0 ∧
        (ε (SpectralWeight.one.toCoeff p.val)).im=0 ∧
        cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 n)
          (hillRealGapHalfLength p.val p.property.1 p.property.2 n) (ε (SpectralWeight.one.toCoeff p.val))=
            (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ) ∧
        Complex.sin (ε (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine p.val p.property.1 p.property.2 n hn ∧
        Θ (SpectralWeight.one.toCoeff p.val)=hillSummedRegularAbelianCorrection
          p.val p.property.1 p.property.2 n hn+ε (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ)) ∧
      Summable (fun j : ℕ => ‖c j‖) ∧
      (∀ k : ℤ, a.val k=Fourier.unitFourierCoefficient (extend (hillInfiniteNormingGradient q c)) k) ∧
      (fderiv ℂ Θ (SpectralWeight.one.toCoeff q.val)).comp hillNativeHilbertDirection=
        (WeightedCoeff.sobolevBilinearPairing 1 a).comp NLS.Poisson.hilbertToHminus ∧
      ∀ d : ℕ → ℂ, ∀ hd : Summable (fun j => ‖d j‖),
        NLS.Poisson.gardnerBivector a (hillInfiniteNormingUnitCotangent h0q h0r q d hd)=0 := by
  obtain ⟨Θ,ε,c,hΘ,hε,hphysical,hc,hD⟩ :=
    exists_hillFullPhysicalPhase_endpoint_cotangent h0q h0r q n hn hgap hterminal
  let a := hillInfiniteNormingUnitCotangent h0q h0r q c hc
  refine ⟨Θ,ε,c,a,hΘ,hε,hphysical,hc,(fun _ => rfl),?_,?_⟩
  swap
  · intro d hd
    exact hillInfiniteNormingUnitCotangent_Gardner_eq_zero h0q h0r q c d hc hd
  apply hillPhysicalDifferential_eq_hminusRestriction _ (hillInfiniteNormingGradient q c) a (fun _ => rfl)
  intro k
  have heven : SpectralWeight.one.toCoeff (hillUnitWeightLift 2 (lp.single 2 (2*k) 1))∈Coeff.paritySubspace 0 := by
    rw [toCoeff_hillUnitWeightLift]
    apply Coeff.single_mem_paritySubspace
    omega
  simpa only [toCoeff_hillUnitWeightLift] using hD (hillUnitWeightLift 2 (lp.single 2 (2*k) 1)) heven

end NLS.KdV
