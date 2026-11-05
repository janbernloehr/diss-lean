import NLS.KdV.HillDirichletNormingData
import NLS.ComplexAnalysis.RealEnergySquareRoot

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ComplexConjugate ENNReal

namespace NLS.KdV

theorem continuous_hillL2FrequencyStateCurve_joint (v : ℂ × ℂ) :
    Continuous (fun p : ℂ × Coeff 2 => hillL2FrequencyStateCurve p.2 p.1 v) := by
  let U (q : Coeff 2) := physicalRestrictionL2 (hillFirstOrderPotential q)
  have hU : Continuous U := physicalRestrictionL2CLM.continuous.comp (continuous_const.prodMk continuous_id.neg)
  have hsol (x : ℂ × ℂ) : Continuous (fun p : (ℂ × Coeff 2) × Icc (0 : ℝ) 1 =>
      l2SolutionCurve (U p.1.2) p.1.1 x p.2) := by
    have hm : Continuous (fun p : (ℂ × Coeff 2) × Icc (0 : ℝ) 1 => ((p.1.1,U p.1.2),p.2)) :=
      ((continuous_fst.fst).prodMk (hU.comp continuous_fst.snd)).prodMk continuous_snd
    convert! (continuous_l2SolutionCurve_time_joint x).comp hm using 1
  let F : (ℂ × Coeff 2) × Icc (0 : ℝ) 1 → ℂ × ℂ := fun p =>
    v.1 • l2SolutionCurve (U p.1.2) p.1.1 (1,0) p.2+
      (I*v.2-p.1.1*v.1) • l2SolutionCurve (U p.1.2) p.1.1 (0,1) p.2
  have hF : Continuous F := ((hsol (1,0)).const_smul v.1).add
    ((by fun_prop : Continuous (fun p : (ℂ × Coeff 2) × Icc (0 : ℝ) 1 => I*v.2-p.1.1*v.1)).smul (hsol (0,1)))
  have hG : Continuous (fun p : (ℂ × Coeff 2) × Icc (0 : ℝ) 1 =>
      ((F p).1,(-I*p.1.1)*(F p).1+(-I)*(F p).2)) :=
    hF.fst.prodMk (((by fun_prop : Continuous (fun p : (ℂ × Coeff 2) × Icc (0 : ℝ) 1 => -I*p.1.1)).mul hF.fst).add
      (hF.snd.const_mul (-I)))
  apply ContinuousMap.continuous_of_continuous_uncurry
  convert! hG using 1
  funext p
  have he := congrArg (fun Y : Curve (ℂ × ℂ) => Y p.2)
    (l2SolutionCurve_linearCombination (U p.1.2) p.1.1 (constantUpperInitialVector p.1.1 v))
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,constantUpperInitialVector] at he
  simp only [hillL2FrequencyStateCurve_apply]
  change constantUpperStateMap p.1.1 (l2SolutionCurve (U p.1.2) p.1.1 (constantUpperInitialVector p.1.1 v) p.2)=_
  dsimp only [constantUpperInitialVector]
  rw [he]
  rfl

def hillDirichletStateCurve (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) : Curve (ℂ × ℂ) :=
  hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff q.val)
    (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (0,1)

theorem continuous_hillDirichletStateCurve (n : ℕ) (hn : 1≤n) :
    Continuous (fun q : RealPeriodOneHillPotential => hillDirichletStateCurve q n hn) := by
  have hm : Continuous (fun q : RealPeriodOneHillPotential =>
      (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ),SpectralWeight.one.toCoeff q.val)) :=
    (continuous_complex_sqrt_real.comp (continuous_hillDirichletEnergy n hn)).prodMk
      (SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val)
  convert! (continuous_hillL2FrequencyStateCurve_joint (0,1)).comp hm using 1

end NLS.KdV
