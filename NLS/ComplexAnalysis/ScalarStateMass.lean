import NLS.FunctionalAnalysis.UnitCurveIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # Continuity and strict positivity of scalar-state position mass. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory Matrix
open scoped ComplexConjugate ENNReal
open NLS.LinearVolterra
namespace NLS.ComplexAnalysis

def scalarStateMass (Y : Curve (ℂ × ℂ)) : ℝ :=
  NLS.FunctionalAnalysis.unitCurveIntegral
    ((⟨fun v : ℂ × ℂ => normSq v.1,continuous_normSq.comp continuous_fst⟩ : C(ℂ × ℂ,ℝ)).comp Y)

theorem continuous_scalarStateMass : Continuous scalarStateMass :=
  NLS.FunctionalAnalysis.unitCurveIntegral.continuous.comp
    (ContinuousMap.continuous_postcomp (⟨fun v : ℂ × ℂ => normSq v.1,continuous_normSq.comp continuous_fst⟩ : C(ℂ × ℂ,ℝ)))

theorem scalarStateMass_eq_integral (Y : Curve (ℂ × ℂ)) :
    scalarStateMass Y = ∫ x in (0 : ℝ)..1, normSq (NLS.LinearVolterra.extend Y x).1 := rfl


theorem scalarStateMass_pos_of_first_derivative (Y : Curve (ℂ × ℂ))
    (hne : ∀ t, Y t≠0)
    (hderiv : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (fun x : ℝ => (NLS.LinearVolterra.extend Y x).1) (NLS.LinearVolterra.extend Y s).2 s) :
    0<scalarStateMass Y := by
  have hex : ∃ x ∈ Ioo (0 : ℝ) 1, (NLS.LinearVolterra.extend Y x).1≠0 := by
    by_contra! hz
    have : NeZero (volume.restrict (Ioc (0 : ℝ) 1)) := by
      refine ⟨?_⟩
      intro he
      have hh := congrArg (fun μ : Measure ℝ => μ univ) he
      norm_num [Measure.restrict_apply] at hh
    have hmem : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), s∈Ioc (0 : ℝ) 1 :=
      ae_restrict_mem measurableSet_Ioc
    have hlast : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), s≠1 :=
      ae_restrict_of_ae (by simp [ae_iff])
    obtain ⟨s,hd,hm,hl⟩ := (hderiv.and (hmem.and hlast)).exists
    have hs : s∈Ioo (0 : ℝ) 1 := ⟨hm.1,lt_of_le_of_ne hm.2 hl⟩
    have hzero : HasDerivAt (fun x : ℝ => (NLS.LinearVolterra.extend Y x).1) 0 s := by
      apply (hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
      exact hz x hx
    have hg : (NLS.LinearVolterra.extend Y s).2=0 := hd.unique hzero
    have hf : (NLS.LinearVolterra.extend Y s).1=0 := hz s hs
    have hh : NLS.LinearVolterra.extend Y s=0 := Prod.ext hf hg
    have hh' : Y ⟨s,hs.1.le,hs.2.le⟩=0 := by simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ (Ioo_subset_Icc_self hs)] using hh
    exact hne _ hh'
  obtain ⟨x,hx,hxne⟩ := hex
  have hc : Continuous (fun x : ℝ => normSq (NLS.LinearVolterra.extend Y x).1) :=
    continuous_normSq.comp (continuous_extend Y).fst
  have hh := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (0 : ℝ)<1) continuous_const.continuousOn hc.continuousOn
    (fun x _ => normSq_nonneg _) ⟨x,Ioo_subset_Icc_self hx,normSq_pos.mpr hxne⟩
  simpa only [scalarStateMass_eq_integral,intervalIntegral.integral_zero] using hh

end NLS.ComplexAnalysis
