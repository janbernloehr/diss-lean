import NLS.KdV.HillHminusOnePhysicalQuasi
import NLS.MKdV.SobolevMiuraWeakForm
import NLS.MKdV.SobolevMiuraPhysicalClass

/-! # The weak Hill forms agree across all H^-1 Miura charts

The comparison is proved on actual L2 potentials by H1 lift regularity
and physical integration by parts, then extended to arbitrary complex
H^-1 inputs by density and norm continuity. The product of the two H1
curves needs matching endpoint values, including periodic, antiperiodic
and reciprocal Floquet pairs.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV.HillHminusMiuraChart

theorem analyticAt_weakForm (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (y φ : Curve ℂ)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    AnalyticAt ℂ (fun p => shiftedMiuraWeakForm (C.physicalProfile p) C.energyShift y φ) q := by
  have hu : AnalyticAt ℂ C.physicalProfile q :=
    (unitL2SynthesisEquiv.toContinuousLinearEquiv.analyticAt (C.lift q)).comp (C.lift_analytic q hq)
  exact (analyticOnNhd_shiftedMiuraWeakForm y φ hy₂ hφ₂ _ (mem_univ _)).comp
    (f := fun p : PeriodOneHminusOne => (C.energyShift,C.physicalProfile p)) (analyticAt_const.prod hu)

/-- Every chart has the same physical L2 Hill form on its L2 inputs. -/
theorem weakForm_eq_physicalL2 (C : HillHminusMiuraChart) (p : Coeff 2)
    (hp : periodOneL2Inclusion p ∈ C.domain) (y φ : Curve ℂ)
    (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hend : extend y 1*extend φ 1 = extend y 0*extend φ 0) :
    shiftedMiuraWeakForm (C.physicalProfile (periodOneL2Inclusion p)) C.energyShift y φ =
      physicalL2HillWeakForm (unitL2SynthesisEquiv p) y φ := by
  have hm : periodOneMiura (C.lift (periodOneL2Inclusion p)) =
      periodOneL2Inclusion (p+lp.single 2 0 C.energyShift) := by
    rw [map_add]
    exact C.image _ hp
  obtain ⟨a,_,hprofile,himage⟩ := exists_physical_H1_Miura_lift _ p C.energyShift hm
  exact shiftedMiuraWeakForm_eq_physicalL2_of_H1 _ _ C.energyShift _
    (absolutelyContinuous_periodOneSobolevSynthesis a) (continuous_periodOneSobolevSynthesis a)
    (memLp_deriv_periodOneSobolevSynthesis a) hprofile himage
    (by simpa only [zero_add] using periodOneSobolevSynthesis_periodic a 0)
    y φ hy hφ hy₂ hφ₂ hend

/-- Physical L2 agreement determines the actual weak form on every
complex chart overlap, with no reality restriction on the potential. -/
theorem weakForm_eqOn_overlap (C D : HillHminusMiuraChart) (y φ : Curve ℂ)
    (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hend : extend y 1*extend φ 1 = extend y 0*extend φ 0) :
    EqOn (fun q => shiftedMiuraWeakForm (C.physicalProfile q) C.energyShift y φ)
      (fun q => shiftedMiuraWeakForm (D.physicalProfile q) D.energyShift y φ) (C.domain ∩ D.domain) := by
  apply eqOn_of_eqOn_periodOneL2Inclusion (C.domain_open.inter D.domain_open)
  · intro q hq
    exact (C.analyticAt_weakForm q hq.1 y φ hy₂ hφ₂).continuousAt.continuousWithinAt
  · intro q hq
    exact (D.analyticAt_weakForm q hq.2 y φ hy₂ hφ₂).continuousAt.continuousWithinAt
  · intro p hp
    rw [C.weakForm_eq_physicalL2 p hp.1 y φ hy hφ hy₂ hφ₂ hend,
      D.weakForm_eq_physicalL2 p hp.2 y φ hy hφ hy₂ hφ₂ hend]

end NLS.KdV.HillHminusMiuraChart
