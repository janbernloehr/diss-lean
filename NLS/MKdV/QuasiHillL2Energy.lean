import NLS.MKdV.QuasiHillEnergyEmbedding
import NLS.ZakharovShabat.SourcePhysicalL2Equiv
import NLS.SequenceSpaces.SourceCotangent
import NLS.ZakharovShabat.L2FundamentalAnalytic

/-! Analytic L2 quasi-Hill solution curves from the fixed energy realization.
The initial scalar state is retained exactly, at every complex energy. -/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

/-- Original source coefficients for the fixed-state energy realization. -/
def quasiHillEnergySource (u : Coeff 2) (lambda : ℂ) : CoeffPair 2 :=
  CoeffPair.inlCLM ((-I) • u+lp.single 2 0 ((lambda-1)/2))+
    CoeffPair.inrCLM (I • u+lp.single 2 0 ((lambda-1)/2))

/-- The energy-dependent source is an actual affine analytic coefficient map. -/
theorem analyticOnNhd_quasiHillEnergySource_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => quasiHillEnergySource p.2 p.1) univ := by
  intro p _
  have hc : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => (t.1-1)/2) p :=
    (analyticAt_fst.sub analyticAt_const).div_const
  have hsingle : AnalyticAt ℂ (fun t : ℂ × Coeff 2 =>
      (lp.single 2 0 ((t.1-1)/2) : Coeff 2)) p :=
    ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 0).analyticAt _).comp hc
  have hleft : AnalyticAt ℂ (fun t : ℂ × Coeff 2 =>
      (-I) • t.2+(lp.single 2 0 ((t.1-1)/2) : Coeff 2)) p :=
    (analyticAt_snd.const_smul (c := -I)).add hsingle
  have hright : AnalyticAt ℂ (fun t : ℂ × Coeff 2 =>
      I • t.2+(lp.single 2 0 ((t.1-1)/2) : Coeff 2)) p :=
    (analyticAt_snd.const_smul (c := I)).add hsingle
  have hl : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => CoeffPair.inlCLM
      ((-I) • t.2+(lp.single 2 0 ((t.1-1)/2) : Coeff 2))) p :=
    ((CoeffPair.inlCLM (p := 2)).analyticAt _).comp hleft
  have hr : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => CoeffPair.inrCLM
      (I • t.2+(lp.single 2 0 ((t.1-1)/2) : Coeff 2))) p :=
    ((CoeffPair.inrCLM (p := 2)).analyticAt _).comp hright
  exact hl.add hr

/-- Full continuous scalar state curve at an arbitrary complex L2 Miura input. -/
def quasiHillL2SolutionCurve (u : Coeff 2) (lambda : ℂ) (v : ℂ × ℂ) : Curve (ℂ × ℂ) :=
  ContinuousLinearMap.compLeftContinuous ℂ (Icc (0:ℝ) 1) quasiHillEnergyStateMap
    (l2SolutionCurve (sourcePhysicalL2 (quasiHillEnergySource u lambda)) (-(lambda+1)/2)
      (quasiHillEnergyInitialVector v))

/-- The actual scalar initial position and quasi-derivative are unchanged. -/
theorem quasiHillL2SolutionCurve_zero (u : Coeff 2) (lambda : ℂ) (v : ℂ × ℂ) :
    quasiHillL2SolutionCurve u lambda v ⟨0,by constructor <;> norm_num⟩ = v := by
  change quasiHillEnergyStateMap (l2SolutionCurve _ _ _ ⟨0,by constructor <;> norm_num⟩) = v
  rw [l2SolutionCurve_zero,quasiHillEnergyStateMap_initialVector]

/-- Joint analyticity in energy and L2 input holds in the full uniform curve norm. -/
theorem analyticOnNhd_quasiHillL2SolutionCurve_joint (v : ℂ × ℂ) :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => quasiHillL2SolutionCurve p.2 p.1 v) univ := by
  intro p _
  have hphi := analyticOnNhd_quasiHillEnergySource_joint p (mem_univ _)
  have hu := (sourcePhysicalL2.analyticAt _).comp hphi
  have hz : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => -(t.1+1)/2) p :=
    (analyticAt_fst.add analyticAt_const).neg.div_const
  have hs := (analyticOnNhd_l2SolutionCurve_joint (quasiHillEnergyInitialVector v)
    (-(p.1+1)/2,sourcePhysicalL2 (quasiHillEnergySource p.2 p.1)) (mem_univ _)).comp
      (f := fun t : ℂ × Coeff 2 => (-(t.1+1)/2,sourcePhysicalL2 (quasiHillEnergySource t.2 t.1)))
      (hz.prod hu)
  exact ((ContinuousLinearMap.compLeftContinuous ℂ (Icc (0:ℝ) 1)
    quasiHillEnergyStateMap).analyticAt _).comp hs

/-- A compatible continuous physical representative recovers the independent
quasi-Hill IVP, rather than merely its trace or zero set. -/
theorem quasiHillL2SolutionCurve_eq_continuous (u : Coeff 2) (U : Curve ℂ) (lambda : ℂ)
    (hU : sourcePhysicalL2 (quasiHillEnergySource u lambda) =
      continuousPotentialL2Class (quasiHillEnergyCurve U lambda))
    (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    quasiHillL2SolutionCurve u lambda v t = quasiHillSolution U lambda v t := by
  change quasiHillEnergyStateMap (l2SolutionCurve _ _ _ t) = _
  rw [hU,l2SolutionCurve_of_continuous,classicalSolutionCurve_apply,
    ← quasiHillSolution_eq_energyZS,quasiHillEnergyStateMap_initialVector]

/-- The actual L2 scalar Dirichlet characteristic in the energy variable. -/
def quasiHillL2Dirichlet (u : Coeff 2) (lambda : ℂ) : ℂ :=
  (quasiHillL2SolutionCurve u lambda (0,1) ⟨1,by constructor <;> norm_num⟩).1

/-- The L2 Dirichlet family is jointly entire, including zero energy. -/
theorem analyticOnNhd_quasiHillL2Dirichlet_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => quasiHillL2Dirichlet p.2 p.1) univ := by
  intro p _
  have hs := analyticOnNhd_quasiHillL2SolutionCurve_joint (0,1) p (mem_univ _)
  have he : AnalyticAt ℂ (fun t : ℂ × Coeff 2 =>
      quasiHillL2SolutionCurve t.2 t.1 (0,1) ⟨1,by constructor <;> norm_num⟩) p :=
    ((ContinuousMap.evalCLM ℂ (⟨1,by constructor <;> norm_num⟩ : Icc (0:ℝ) 1) :
      Curve (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)).analyticAt _).comp hs
  exact analyticAt_fst.comp he

/-- Exact scalar normalization on every compatible continuous representative. -/
theorem quasiHillL2Dirichlet_eq_continuous (u : Coeff 2) (U : Curve ℂ) (lambda : ℂ)
    (hU : sourcePhysicalL2 (quasiHillEnergySource u lambda) =
      continuousPotentialL2Class (quasiHillEnergyCurve U lambda)) :
    quasiHillL2Dirichlet u lambda = quasiHillDirichlet U lambda :=
  congrArg Prod.fst (quasiHillL2SolutionCurve_eq_continuous u U lambda hU (0,1)
    ⟨1,by constructor <;> norm_num⟩)

end NLS.MKdV
