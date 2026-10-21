import NLS.Fourier.AbelSobolevStripCharacterization
import NLS.Fourier.UnitIntervalL2Equiv
import NLS.SequenceSpaces.ShiftedWeight

noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- The exact Sobolev weight for physical period-one Fourier coefficients. -/
def physicalUnitSobolevWeight (s : ℝ) (hs : 0 ≤ s) : SpectralWeight :=
  SpectralWeight.scaledSobolev (2*Real.pi) s (by positivity) hs

@[simp] theorem physicalUnitSobolevWeight_apply (s : ℝ) (hs : 0 ≤ s) (n : ℤ) :
    physicalUnitSobolevWeight s hs n = (1+|((2*n:ℤ):ℝ)*Real.pi|)^s := by
  rw [physicalUnitSobolevWeight,SpectralWeight.scaledSobolev_apply]
  congr 2
  simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos Real.pi_pos,
    abs_of_pos (by norm_num : (0:ℝ)<2)]
  ring

/-- Remove the exact Sobolev weight and synthesize the physical unit-interval L2 class. -/
def physicalSobolevTraceSynthesis (s : ℝ) (hs : 0 ≤ s) :
    Coeff 2 →L[ℂ] NLS.ZakharovShabat.IntervalL2 :=
  unitL2SynthesisEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((SpectralWeight.toCoeff (physicalUnitSobolevWeight s hs)).comp
      (WeightedCoeff.weightIsometry (physicalUnitSobolevWeight s hs).toWeight 2).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The synthesized physical trace has the exact unweighted Fourier coefficients. -/
theorem physicalSobolevTraceSynthesis_coefficient (s : ℝ) (hs : 0 ≤ s) (b : Coeff 2) (n : ℤ) :
    intervalFourierCoefficient 1 (physicalSobolevTraceSynthesis s hs b) n =
      b n/((physicalUnitSobolevWeight s hs n:ℝ):ℂ) := by
  change intervalFourierCoefficient 1 (unitL2SynthesisLinear
    (SpectralWeight.toCoeff (physicalUnitSobolevWeight s hs)
      ((WeightedCoeff.weightIsometry (physicalUnitSobolevWeight s hs).toWeight 2).symm b))) n = _
  rw [unitL2SynthesisLinear_coefficient,SpectralWeight.toCoeff_apply]
  rfl

/-- Applying the physical Sobolev multiplier recovers the input l2 sequence. -/
theorem physicalSobolevTraceSynthesis_weighted_coefficient
    (s : ℝ) (hs : 0 ≤ s) (b : Coeff 2) (n : ℤ) :
    (((1+|((2*n:ℤ):ℝ)*Real.pi|)^s:ℝ):ℂ)*
      intervalFourierCoefficient 1 (physicalSobolevTraceSynthesis s hs b) n = b n := by
  rw [physicalSobolevTraceSynthesis_coefficient,← physicalUnitSobolevWeight_apply s hs n]
  exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt ((physicalUnitSobolevWeight s hs).positive n)))

/-- A holomorphic interior trace is a continuous physical function on the entire real line. -/
theorem continuous_horizontal_of_analytic_strip (a : ℝ) (f : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ f {z : ℂ | |z.im| < a/Real.pi})
    (y : ℝ) (hy : |y| < a/Real.pi) :
    Continuous (fun x : ℝ => f ((x:ℂ)+y*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (han _ (by simpa using hy)).continuousAt.comp (by fun_prop)

/-- Continuous Sobolev coefficient traces are actual continuous L2 trace curves,
with the prescribed weighted Fourier integrals and the correct interior representatives. -/
theorem exists_physical_sobolev_strip_traces (s a : ℝ) (hs : 0 ≤ s) (f : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ f {z : ℂ | |z.im| < a/Real.pi})
    (g : ℝ → Coeff 2) (hg : Continuous g)
    (hcoeff : ∀ y : ℝ, |y| < a/Real.pi → ∀ n : ℤ,
      g y n = sobolevHorizontalCoefficient s f y n) :
    ∃ u : ℝ → NLS.ZakharovShabat.IntervalL2, Continuous u ∧
      (∀ y : ℝ, ∀ n : ℤ, (((1+|((2*n:ℤ):ℝ)*Real.pi|)^s:ℝ):ℂ)*
        intervalFourierCoefficient 1 (u y) n = g y n) ∧
      ∀ y : ℝ, |y| < a/Real.pi →
        (u y : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 1)] (fun x : ℝ => f ((x:ℂ)+y*I)) := by
  let u := fun y => physicalSobolevTraceSynthesis s hs (g y)
  refine ⟨u,(physicalSobolevTraceSynthesis s hs).continuous.comp hg,
    fun y n => physicalSobolevTraceSynthesis_weighted_coefficient s hs (g y) n,?_⟩
  intro y hy
  let fy : ℝ → ℂ := fun x => f ((x:ℂ)+y*I)
  have hfy : MemLp fy 2 (volume.restrict (Ioc 0 1)) :=
    memLp_two_interval (continuous_horizontal_of_analytic_strip a f han y hy) 0 1 (by norm_num)
  have he : u y = unitL2SynthesisEquiv (unitIntervalMemLpCoefficients fy hfy) := by
    apply unitL2_ext_coefficients
    intro n
    change intervalFourierCoefficient 1 (physicalSobolevTraceSynthesis s hs (g y)) n = _
    rw [physicalSobolevTraceSynthesis_coefficient,hcoeff y hy n,
      sobolevHorizontalCoefficient,physicalUnitSobolevWeight_apply]
    have hright := unitL2SynthesisLinear_coefficient (unitIntervalMemLpCoefficients fy hfy) n
    change intervalFourierCoefficient 1 (unitL2SynthesisEquiv (unitIntervalMemLpCoefficients fy hfy)) n = _ at hright
    rw [hright,unitIntervalMemLpCoefficients_apply,
      intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num)]
    change (((1+|((2*n:ℤ):ℝ)*Real.pi|)^s:ℝ):ℂ)*periodOneCoefficient fy n/
      (((1+|((2*n:ℤ):ℝ)*Real.pi|)^s:ℝ):ℂ) = periodOneCoefficient fy n
    exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.rpow_pos_of_pos (by positivity) s)))
  rw [he,unitL2SynthesisEquiv_memLpCoefficients]
  exact hfy.coeFn_toLp

/-- The norm-trace condition is equivalent to actual physical L2 trace curves
whose exact Sobolev-weighted Fourier coefficients form a continuous l2 curve. -/
theorem hasSobolevNormStripTraces_iff_physical (s a : ℝ) (hs : 0 ≤ s) (f : ℂ → ℂ)
    (han : AnalyticOnNhd ℂ f {z : ℂ | |z.im| < a/Real.pi}) :
    HasSobolevNormStripTraces s a f ↔
      ∃ g : ℝ → Coeff 2, ∃ u : ℝ → NLS.ZakharovShabat.IntervalL2,
        Continuous g ∧ Continuous u ∧
        (∀ y : ℝ, ∀ n : ℤ, (((1+|((2*n:ℤ):ℝ)*Real.pi|)^s:ℝ):ℂ)*
          intervalFourierCoefficient 1 (u y) n = g y n) ∧
        ∀ y : ℝ, |y| < a/Real.pi →
          (u y : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 1)] (fun x : ℝ => f ((x:ℂ)+y*I)) := by
  constructor
  · rintro ⟨g,hg,hcoeff⟩
    obtain ⟨u,hu,hw,hphys⟩ := exists_physical_sobolev_strip_traces s a hs f han g hg hcoeff
    exact ⟨g,u,hg,hu,hw,hphys⟩
  · rintro ⟨g,u,hg,_,hw,hphys⟩
    refine ⟨g,hg,fun y hy n => ?_⟩
    rw [← hw y n,sobolevHorizontalCoefficient,
      intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num),periodOneCoefficient]
    congr 1
    exact congrFun (fourierCoeffOn_congr_ae (by norm_num) (hphys y hy)) n

end NLS.Fourier
