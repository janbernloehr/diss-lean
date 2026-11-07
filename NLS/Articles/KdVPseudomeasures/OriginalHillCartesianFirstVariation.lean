import NLS.Articles.KdVPseudomeasures.OriginalHillNativeSpectralFirstVariation
import NLS.KdV.HillNativeCartesianFirstVariation

/-! The actual native Cartesian map has its exact full Banach differential
at zero on the original mean-zero source. Positive and negative original
Fourier modes are retained. Canonicality and global bijectivity remain open. -/
noncomputable section
open Complex NLS.KdV NLS.Fourier NLS.Fourier.SmoothPeriodicTest
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_free_deleted_multiplier (P : HillProductEquationPatch)
    (h0 : (0 : PeriodOneHminusOne) ∈ P.source) (n : ℕ+) :
    P.abelianGapRootMultiplier n (P.physicalDirichletFrequency ((n:ℕ):ℤ) 0,0)=
      2*I*(-1:ℂ)^(n:ℕ)*P.parent.parent.miuraBall.freeFrequencyMidpoint n/((Real.pi:ℂ)*n) :=
  P.abelianGapRootMultiplier_zero_divisor h0 n

theorem original_Hill_native_Cartesian_differential (n : ℕ+) (h : PeriodOneHminusOne)
    (hh : h.val 0=0) :
    ((fderiv ℂ hillHminusNativeCartesianMap 0) h).fst.val ((n:ℕ):ℤ)=
      (h.val (-(n:ℤ))+h.val (n:ℤ))/(2*((Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)) ∧
    ((fderiv ℂ hillHminusNativeCartesianMap 0) h).snd.val ((n:ℕ):ℤ)=
      (h.val (-(n:ℤ))-h.val (n:ℤ))/((2*I)*((Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)) :=
  fderiv_hillHminusNativeCartesianMap_positive_mean_zero n h hh

theorem original_Hill_Cartesian_differential_even_modes (n : ℕ+) (h : OriginalHminusOnePotential) :
    ((fderiv ℂ hillHminusNativeCartesianMap 0) (originalPeriodOneCoefficients h)).fst.val ((n:ℕ):ℤ)=
      (h.val.val (mode (2*(n:ℤ)))+h.val.val (mode (-(2*(n:ℤ)))))/
        (2*((Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)) ∧
    ((fderiv ℂ hillHminusNativeCartesianMap 0) (originalPeriodOneCoefficients h)).snd.val ((n:ℕ):ℤ)=
      (h.val.val (mode (2*(n:ℤ)))-h.val.val (mode (-(2*(n:ℤ)))))/
        ((2*I)*((Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)) := by
  simpa only [originalPeriodOneCoefficients,periodOneOriginalExtract_apply,mul_neg,neg_neg] using
    original_Hill_native_Cartesian_differential n (originalPeriodOneCoefficients h)
      (originalPeriodOneCoefficients_mean_zero h)

theorem original_Hill_Cartesian_differential_nonpositive (h : PeriodOneHminusOne)
    (k : ℤ) (hk : k ≤ 0) :
    ((fderiv ℂ hillHminusNativeCartesianMap 0) h).fst.val k=0 ∧
      ((fderiv ℂ hillHminusNativeCartesianMap 0) h).snd.val k=0 :=
  fderiv_hillHminusNativeCartesianMap_nonpositive h k hk

end NLS.Articles.KdVPseudomeasures
