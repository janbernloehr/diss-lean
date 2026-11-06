import NLS.KdV.HillDiscriminantQuadraticSystem
import NLS.ComplexAnalysis.QuadraticHillSystemPairing
import NLS.KdV.HillDirichletLagrange

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



def hillDiscriminantGardnerBracket (q : Coeff 2) (z w : ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillDiscriminantGradientCurve q z) x*
    deriv (NLS.LinearVolterra.extend (hillDiscriminantGradientCurve q w)) x

theorem hillDiscriminantGardnerBracket_eq_curveIntegral (q : Coeff 2) (z w : ℂ) :
    hillDiscriminantGardnerBracket q z w=unitComplexCurveIntegral
      (hillDiscriminantGradientCurve q z*hillDiscriminantGradientSpatialCurve q w) := by
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [ae_hasDerivAt_hillDiscriminantGradientCurve q w] with x hx
  change NLS.LinearVolterra.extend (hillDiscriminantGradientCurve q z) x*
    deriv (NLS.LinearVolterra.extend (hillDiscriminantGradientCurve q w)) x=
    NLS.LinearVolterra.extend (hillDiscriminantGradientCurve q z) x*
      NLS.LinearVolterra.extend (hillDiscriminantGradientSpatialCurve q w) x
  rw [hx.deriv]

theorem hillDiscriminantGardnerBracket_eq_zero_of_energy_ne
    (q : Coeff 2) (z w : ℂ) (hne : z^2≠w^2) :
    hillDiscriminantGardnerBracket q z w=0 := by
  rw [hillDiscriminantGardnerBracket_eq_curveIntegral]
  have hza := absolutelyContinuousOnInterval_hillDiscriminantQuadraticSystem q z
  have hwa := absolutelyContinuousOnInterval_hillDiscriminantQuadraticSystem q w
  have hzg := hillDiscriminantGradientCurve_endpoints q z
  have hzh := hillDiscriminantGradientSpatialCurve_endpoints q z
  have hzr := hillDiscriminantQuadraticMomentumCurve_endpoints q z
  have hwg := hillDiscriminantGradientCurve_endpoints q w
  have hwh := hillDiscriminantGradientSpatialCurve_endpoints q w
  have hwr := hillDiscriminantQuadraticMomentumCurve_endpoints q w
  exact quadraticHillSystem_pairing_eq_zero (z^2) (w^2) hne (hillL2ScalarRepresentative q)
    (hillDiscriminantGradientCurve q z) (hillDiscriminantGradientSpatialCurve q z) (hillDiscriminantQuadraticMomentumCurve q z)
    (hillDiscriminantGradientCurve q w) (hillDiscriminantGradientSpatialCurve q w) (hillDiscriminantQuadraticMomentumCurve q w)
    (absolutelyContinuousOnInterval_hillDiscriminantGradientCurve q z) hza.1 hza.2
    (absolutelyContinuousOnInterval_hillDiscriminantGradientCurve q w) hwa.1 hwa.2
    (ae_hasDerivAt_hillDiscriminantQuadraticSystem q z) (ae_hasDerivAt_hillDiscriminantQuadraticSystem q w)
    (hzg.2.trans hzg.1.symm) (hzh.2.trans hzh.1.symm) (hzr.2.trans hzr.1.symm)
    (hwg.2.trans hwg.1.symm) (hwh.2.trans hwh.1.symm) (hwr.2.trans hwr.1.symm)

theorem continuous_hillDiscriminantGradientSpatialCurve_spectral (q : Coeff 2) :
    Continuous (hillDiscriminantGradientSpatialCurve q) := by
  have hC := continuous_hillL2FrequencyStateCurve_frequency q (1,0)
  have hS := continuous_hillL2FrequencyStateCurve_frequency q (0,1)
  have hc := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hC
  have hd := (ContinuousMap.snd : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hC
  have hs := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hS
  have ht := (ContinuousMap.snd : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hS
  have hC1 := (continuous_eval_const (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).comp hC
  have hS1 := (continuous_eval_const (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).comp hS
  exact (((hS1.fst.const_mul 2).smul (hc.mul hd)).add
    ((hS1.snd.sub hC1.fst).smul ((hd.mul hs).add (hc.mul ht)))).sub
      ((hC1.snd.const_mul 2).smul (hs.mul ht))

theorem continuous_hillDiscriminantGardnerBracket_right (q : Coeff 2) (z : ℂ) :
    Continuous (hillDiscriminantGardnerBracket q z) := by
  have he : hillDiscriminantGardnerBracket q z=
      fun w => unitComplexCurveIntegral (hillDiscriminantGradientCurve q z*hillDiscriminantGradientSpatialCurve q w) :=
    funext (hillDiscriminantGardnerBracket_eq_curveIntegral q z)
  rw [he]
  exact unitComplexCurveIntegral.continuous.comp
    (continuous_const.mul (continuous_hillDiscriminantGradientSpatialCurve_spectral q))

/-- The actual Hill discriminants commute for every pair of frequencies,
including coinciding energies, at every complex rough L2 potential. -/
theorem hillDiscriminantGardnerBracket_eq_zero (q : Coeff 2) (z w : ℂ) :
    hillDiscriminantGardnerBracket q z w=0 := by
  let S : Set ℂ := {z}ᶜ ∩ {-z}ᶜ
  have hS : Dense S := (dense_compl_singleton z).inter_of_isOpen_right
    (dense_compl_singleton (-z)) isOpen_compl_singleton
  have hzero : S⊆{v : ℂ | hillDiscriminantGardnerBracket q z v=0} := by
    intro v hv
    apply hillDiscriminantGardnerBracket_eq_zero_of_energy_ne
    intro he
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he.symm with hh | hh
    · exact hv.1 (by simpa only [mem_singleton_iff] using hh)
    · exact hv.2 (by simpa only [mem_singleton_iff] using hh)
  have hc : IsClosed {v : ℂ | hillDiscriminantGardnerBracket q z v=0} :=
    isClosed_eq (continuous_hillDiscriminantGardnerBracket_right q z) continuous_const
  have hw : w∈closure S := by rw [hS.closure_eq];exact mem_univ w
  exact closure_minimal hzero hc hw

end NLS.KdV
