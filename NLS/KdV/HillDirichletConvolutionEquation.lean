import NLS.KdV.HillDirichletFourierSequence
import NLS.Fourier.ZeroExtensionConvolution

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.Fourier NLS.ZakharovShabat
open scoped ENNReal Classical

namespace NLS.KdV



/-- The actual scalar representative is the negative lower first-order
Fourier representative; no pointwise quotient linearity is presumed. -/
theorem hillL2ScalarRepresentative_eq_neg_lower_ae (q : Coeff 2) :
    hillL2ScalarRepresentative q =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun x => -circlePullback (l2Synthesis (-q)) x) := by
  filter_upwards [physicalRestrictionL2_representative (hillFirstOrderPotential q)] with x hx
  dsimp only [hillL2ScalarRepresentative]
  rw [hx]
  rfl

/-- The product in the actual rough Dirichlet equation is exactly the
existing discrete Fourier convolution with its summable coefficient sequence. -/
theorem hillL2Dirichlet_product_coefficient_eq_convolution (q : Coeff 2) (energy : ℂ)
    (hzero : hillL2DirichletCharacteristic q energy = 0) (k : ℤ) :
    halfCoefficient (fun x => hillL2ScalarRepresentative q x*hillL2DirichletPosition q energy x) k =
      Coeff.convolution q (hillL2DirichletHalfSequence q energy) k := by
  have hf2 := memLp_two_interval
    (NLS.LinearVolterra.continuous_extend
      (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1))).fst 0 1 (by norm_num)
  have hc := convolution_halfCoefficients_eq_physical_product (-q)
    (hillL2DirichletPosition q energy) hf2 (hillL2DirichletHalfSequence q energy)
      (hillL2DirichletHalfSequence_apply q energy hzero) k
  have hp : halfCoefficient (fun x => hillL2ScalarRepresentative q x*hillL2DirichletPosition q energy x) k =
      halfCoefficient (fun x => -(circlePullback (l2Synthesis (-q)) x*
        hillL2DirichletPosition q energy x)) k := by
    unfold halfCoefficient
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    filter_upwards [hillL2ScalarRepresentative_eq_neg_lower_ae q] with x hx
    rw [hx]
    ring
  rw [hp]
  have hneg : halfCoefficient (fun x => -(circlePullback (l2Synthesis (-q)) x*
        hillL2DirichletPosition q energy x)) k =
      -halfCoefficient (fun x => circlePullback (l2Synthesis (-q)) x*
        hillL2DirichletPosition q energy x) k := by
    simp only [halfCoefficient,neg_mul,intervalIntegral.integral_neg,mul_neg]
  rw [hneg,← hc]
  have hn := map_neg (Coeff.convolutionCLM.flip (hillL2DirichletHalfSequence q energy)) q
  change Coeff.convolution (-q) (hillL2DirichletHalfSequence q energy) =
    -Coeff.convolution q (hillL2DirichletHalfSequence q energy) at hn
  rw [hn]
  simp

/-- The actual Dirichlet eigenfunction, zero extended to the second half of
the period, solves the full convolution equation with two endpoint sources. -/
theorem hillL2DirichletHalfSequence_convolution_equation (q : Coeff 2) (energy : ℂ)
    (hzero : hillL2DirichletCharacteristic q energy = 0) (k : ℤ) :
    (energy-(freeHillValue k : ℂ))*hillL2DirichletHalfSequence q energy k =
      Coeff.convolution q (hillL2DirichletHalfSequence q energy) k -
        (hillL2DirichletSlope q energy*wave (-k) 1-1)/2 := by
  rw [hillL2DirichletHalfSequence_forced_equation q energy hzero,
    hillL2Dirichlet_product_coefficient_eq_convolution q energy hzero]

/-- The two resonant equations have exactly the same endpoint forcing, so
subtracting them cancels it without imposing a periodic derivative. -/
theorem hillL2DirichletHalfSequence_resonant_difference (q : Coeff 2) (energy : ℂ)
    (hzero : hillL2DirichletCharacteristic q energy = 0) (n : ℤ) :
    (energy-(freeHillValue n : ℂ))*(hillL2DirichletHalfSequence q energy n-
      hillL2DirichletHalfSequence q energy (-n)) =
      Coeff.convolution q (hillL2DirichletHalfSequence q energy) n-
        Coeff.convolution q (hillL2DirichletHalfSequence q energy) (-n) := by
  have hp := hillL2DirichletHalfSequence_convolution_equation q energy hzero n
  have hm := hillL2DirichletHalfSequence_convolution_equation q energy hzero (-n)
  have hw : wave (-n) 1 = wave n 1 := by
    simpa only [show (2 : ℝ)-1=1 by norm_num,neg_neg] using wave_reflect (-n) 1
  rw [freeHillValue_neg,neg_neg,← hw] at hm
  linear_combination hp-hm

end NLS.KdV
