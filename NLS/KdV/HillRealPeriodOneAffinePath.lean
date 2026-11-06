import NLS.KdV.HillLabelContinuity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem real_affine (q r : Coeff 2) (hq : IsRealHillPotential q) (hr : IsRealHillPotential r) (t : ℝ) :
    IsRealHillPotential ((t : ℂ) • (r-q)+q) := by
  intro k
  simp only [lp.coeFn_add,lp.coeFn_sub,lp.coeFn_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    map_add,map_sub,map_mul,Complex.conj_ofReal,hq k,hr k]

/-- The affine path stays in the original real period-one Hilbert source space. -/
def hillRealPeriodOneAffinePath (q r : RealPeriodOneHillPotential) (t : ℝ) : RealPeriodOneHillPotential :=
  ⟨(t : ℂ) • (r.val-q.val)+q.val,by
    constructor
    · simpa only [map_add,map_smul,map_sub] using
        (Coeff.paritySubspace 0).add_mem
          ((Coeff.paritySubspace 0).smul_mem (t : ℂ) ((Coeff.paritySubspace 0).sub_mem r.property.1 q.property.1)) q.property.1
    · simpa only [map_add,map_smul,map_sub] using
        real_affine (SpectralWeight.one.toCoeff q.val) (SpectralWeight.one.toCoeff r.val) q.property.2 r.property.2 t⟩

theorem hillRealPeriodOneAffinePath_coeff (q r : RealPeriodOneHillPotential) (t : ℝ) :
    SpectralWeight.one.toCoeff (hillRealPeriodOneAffinePath q r t).val=
      (t : ℂ) • (SpectralWeight.one.toCoeff r.val-SpectralWeight.one.toCoeff q.val)+SpectralWeight.one.toCoeff q.val := by
  simp only [hillRealPeriodOneAffinePath,map_add,map_smul,map_sub]

theorem continuous_hillRealPeriodOneAffinePath (q r : RealPeriodOneHillPotential) :
    Continuous (hillRealPeriodOneAffinePath q r) :=
  ((continuous_ofReal.smul continuous_const).add continuous_const).subtype_mk _

theorem hillRealPeriodOneAffinePath_zero (q r : RealPeriodOneHillPotential) :
    hillRealPeriodOneAffinePath q r 0=q := by
  apply Subtype.ext
  change (0 : ℂ) • (r.val-q.val)+q.val=q.val
  rw [zero_smul,zero_add]

theorem hillRealPeriodOneAffinePath_one (q r : RealPeriodOneHillPotential) :
    hillRealPeriodOneAffinePath q r 1=r := by
  apply Subtype.ext
  change (1 : ℂ) • (r.val-q.val)+q.val=r.val
  rw [one_smul,sub_add_cancel]

end NLS.KdV
