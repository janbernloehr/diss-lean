import NLS.Fourier.PeriodOneACCoefficients
import NLS.FunctionalAnalysis.UnitCurveLpBounds
import NLS.SequenceSpaces.SobolevDerivative
import NLS.ZakharovShabat.SobolevHierarchyOperations

/-! # Coefficient-preserving native Sobolev lifts of periodic interval curves

Actual unit-interval Fourier integrals define both lifts. The derivative
graph recovers H¹ and then H² from the actual a.e. derivatives, with
periodic value and first-derivative traces. No smooth approximation or
changed Fourier normalization enters the construction.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Fourier

theorem memlp_periodOne_H1_of_curve_derivative (f : Curve ℂ) (g : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval (extend f) 0 1)
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend f) (g x) x)
    (hend : f ⟨1,by norm_num⟩ = f ⟨0,by norm_num⟩) :
    Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*periodOneCoefficient (extend f) n) 2 := by
  have he : extend f 1 = extend f 0 := by
    simpa only [NLS.LinearVolterra.extend,
      projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 by norm_num),
      projIcc_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 by norm_num)] using hend
  apply memlp_sobolev_weight_of_derivative (memlp_periodOneCoefficient (memLp_unitCurve_extend 2 f))
  convert! (memlp_periodOneCoefficient hg).const_mul (1/2 : ℂ) using 1
  funext n
  rw [periodOneCoefficient_of_ac_derivative hf hg hd he n]
  ring

def periodOneH1CurveCoefficients (f : Curve ℂ) (g : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval (extend f) 0 1)
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend f) (g x) x)
    (hend : f ⟨1,by norm_num⟩ = f ⟨0,by norm_num⟩) : ScalarDomain 2 :=
  ⟨periodOneCoefficient (extend f),memlp_periodOne_H1_of_curve_derivative f g hf hg hd hend⟩

def periodOneH2CurveCoefficients (f df : Curve ℂ) (ddf : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval (extend f) 0 1)
    (hdf : AbsolutelyContinuousOnInterval (extend df) 0 1)
    (hddf : MemLp ddf 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend f) (extend df x) x)
    (hdd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend df) (ddf x) x)
    (hend : f ⟨1,by norm_num⟩ = f ⟨0,by norm_num⟩)
    (hdend : df ⟨1,by norm_num⟩ = df ⟨0,by norm_num⟩) : ScalarSobolev 2 := by
  have hbase := memlp_periodOne_H1_of_curve_derivative f (extend df) hf
    (memLp_unitCurve_extend 2 df) hd hend
  have hprime := memlp_periodOne_H1_of_curve_derivative df ddf hdf hddf hdd hdend
  have he : extend f 1 = extend f 0 := by
    simpa only [NLS.LinearVolterra.extend,
      projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 by norm_num),
      projIcc_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 by norm_num)] using hend
  have hder : Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*
      (I*(Real.pi : ℂ)*n*periodOneCoefficient (extend f) n)) 2 := by
    convert! hprime.const_mul (1/2 : ℂ) using 1
    funext n
    rw [periodOneCoefficient_of_ac_derivative hf (memLp_unitCurve_extend 2 df) hd he n]
    ring
  refine ⟨periodOneCoefficient (extend f),?_⟩
  change Memℓp (fun n => (Weight.sobolev (2 : ℝ) n : ℂ)*periodOneCoefficient (extend f) n) 2
  simpa only [one_add_one_eq_two] using WeightedCoeff.memlp_sobolev_succ_of_derivative 1 hbase hder

end NLS.Fourier
