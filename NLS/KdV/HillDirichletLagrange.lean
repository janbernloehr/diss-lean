import NLS.KdV.HillDirichletBands
import NLS.ComplexAnalysis.ScalarStateCrossMass

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ComplexConjugate ENNReal

namespace NLS.KdV

theorem classicalHillFlow_lagrange_identity (q : Curve ℂ) (a b : ℂ) :
    (a-b)*(∫ x in (0 : ℝ)..1,
      (classicalHillFlow q a (0,1) x).1*(classicalHillFlow q b (0,1) x).1) =
      (classicalHillFlow q a (0,1) 1).1*(classicalHillFlow q b (0,1) 1).2-
        (classicalHillFlow q a (0,1) 1).2*(classicalHillFlow q b (0,1) 1).1 := by
  let A := classicalHillFlow q a (0,1)
  let B := classicalHillFlow q b (0,1)
  have hA : Continuous A := continuous_classicalHillFlow q a (0,1)
  have hB : Continuous B := continuous_classicalHillFlow q b (0,1)
  have hd (t : Icc (0 : ℝ) 1) : HasDerivAt
      (fun x : ℝ => (A x).1*(B x).2-(A x).2*(B x).1)
      ((a-b)*((A t).1*(B t).1)) t.val := by
    have hAf : HasDerivAt (fun x : ℝ => (A x).1) (A t).2 t.val := by
      simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q a (0,1) t).fst
    have hAg : HasDerivAt (fun x : ℝ => (A x).2) ((q t-a)*(A t).1) t.val := by
      simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q a (0,1) t).snd
    have hBf : HasDerivAt (fun x : ℝ => (B x).1) (B t).2 t.val := by
      simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (0,1) t).fst
    have hBg : HasDerivAt (fun x : ℝ => (B x).2) ((q t-b)*(B t).1) t.val := by
      simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (0,1) t).snd
    convert! (hAf.mul hBg).sub (hAg.mul hBf) using 1
    ring
  have hcont : Continuous (fun x : ℝ => (A x).1*(B x).2-(A x).2*(B x).1) :=
    (hA.fst.mul hB.snd).sub (hA.snd.mul hB.fst)
  have hprod : Continuous (fun x : ℝ => (a-b)*((A x).1*(B x).1)) :=
    continuous_const.mul (hA.fst.mul hB.fst)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
    hcont.continuousOn (fun x (hx : x∈Ioo (0 : ℝ) 1) => hd ⟨x,hx.1.le,hx.2.le⟩)
    (hprod.intervalIntegrable 0 1)
  simpa only [intervalIntegral.integral_const_mul,A,B,classicalHillFlow_zero,zero_mul,mul_zero,
    sub_self,sub_zero] using h

theorem continuous_hillL2FrequencyStateCurve_frequency (q : Coeff 2) (v : ℂ × ℂ) :
    Continuous (fun z : ℂ => hillL2FrequencyStateCurve q z v) := by
  let u := physicalRestrictionL2 (hillFirstOrderPotential q)
  have hA : Continuous (fun p : ℂ × Icc (0 : ℝ) 1 => l2SolutionCurve u p.1 (1,0) p.2) := by
    have hp : Continuous (fun p : ℂ × Icc (0 : ℝ) 1 => ((p.1,u),p.2)) := by fun_prop
    simpa only [Function.comp_def] using (continuous_l2SolutionCurve_time_joint (1,0)).comp hp
  have hB : Continuous (fun p : ℂ × Icc (0 : ℝ) 1 => l2SolutionCurve u p.1 (0,1) p.2) := by
    have hp : Continuous (fun p : ℂ × Icc (0 : ℝ) 1 => ((p.1,u),p.2)) := by fun_prop
    simpa only [Function.comp_def] using (continuous_l2SolutionCurve_time_joint (0,1)).comp hp
  let F : ℂ × Icc (0 : ℝ) 1 → ℂ × ℂ := fun p =>
    v.1 • l2SolutionCurve u p.1 (1,0) p.2+(I*v.2-p.1*v.1) • l2SolutionCurve u p.1 (0,1) p.2
  have hF : Continuous F := (hA.const_smul v.1).add ((by fun_prop : Continuous (fun p : ℂ × Icc (0 : ℝ) 1 => I*v.2-p.1*v.1)).smul hB)
  have hG : Continuous (fun p : ℂ × Icc (0 : ℝ) 1 => ((F p).1,(-I*p.1)*(F p).1+(-I)*(F p).2)) :=
    hF.fst.prodMk (((by fun_prop : Continuous (fun p : ℂ × Icc (0 : ℝ) 1 => -I*p.1)).mul hF.fst).add (hF.snd.const_mul (-I)))
  apply ContinuousMap.continuous_of_continuous_uncurry
  convert! hG using 1
  funext p
  have he := congrArg (fun Y : Curve (ℂ × ℂ) => Y p.2)
    (l2SolutionCurve_linearCombination u p.1 (constantUpperInitialVector p.1 v))
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,constantUpperInitialVector] at he
  simp only [hillL2FrequencyStateCurve_apply]
  change constantUpperStateMap p.1 (l2SolutionCurve u p.1 (constantUpperInitialVector p.1 v) p.2)=_
  dsimp only [constantUpperInitialVector]
  rw [he]
  rfl

theorem scalarStateCrossMass_hill_eq_classical (Q : C(AddCircle (2 : ℝ),ℂ)) (z w : ℂ) :
    scalarStateCrossMass
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z (0,1))
      (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) w (0,1)) =
      ∫ x in (0 : ℝ)..1, (classicalHillFlow (hillUnitPotentialCurve Q) (z^2) (0,1) x).1*
        (classicalHillFlow (hillUnitPotentialCurve Q) (w^2) (0,1) x).1 := by
  rw [scalarStateCrossMass_eq_integral]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x∈Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
  simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hx',hillL2FrequencyStateCurve_eq_classical]

theorem hillL2FrequencyStateCurve_lagrange_identity (q : Coeff 2) (z w : ℂ) :
    (z^2-w^2)*scalarStateCrossMass (hillL2FrequencyStateCurve q z (0,1)) (hillL2FrequencyStateCurve q w (0,1)) =
      (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).1*(hillL2FrequencyStateCurve q w (0,1) ⟨1,by norm_num⟩).2-
      (hillL2FrequencyStateCurve q z (0,1) ⟨1,by norm_num⟩).2*(hillL2FrequencyStateCurve q w (0,1) ⟨1,by norm_num⟩).1 := by
  let A : Coeff 2 → Curve (ℂ × ℂ) := fun a => hillL2FrequencyStateCurve a z (0,1)
  let B : Coeff 2 → Curve (ℂ × ℂ) := fun a => hillL2FrequencyStateCurve a w (0,1)
  have hA : Continuous A := continuous_hillL2FrequencyStateCurve z (0,1)
  have hB : Continuous B := continuous_hillL2FrequencyStateCurve w (0,1)
  have hC : Continuous (fun a : Coeff 2 => scalarStateCrossMass (A a) (B a)) := by
    convert! continuous_scalarStateCrossMass.comp (hA.prodMk hB) using 1
  have hL : Continuous (fun a : Coeff 2 => (z^2-w^2)*scalarStateCrossMass (A a) (B a)) :=
    continuous_const.mul hC
  have hAe : Continuous (fun a : Coeff 2 => A a ⟨1,by norm_num⟩) := (continuous_eval_const (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).comp hA
  have hBe : Continuous (fun a : Coeff 2 => B a ⟨1,by norm_num⟩) := (continuous_eval_const (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)).comp hB
  have hR : Continuous (fun a : Coeff 2 => (A a ⟨1,by norm_num⟩).1*(B a ⟨1,by norm_num⟩).2-
      (A a ⟨1,by norm_num⟩).2*(B a ⟨1,by norm_num⟩).1) :=
    (hAe.fst.mul hBe.snd).sub (hAe.snd.mul hBe.fst)
  have hfinite (a : ℤ →₀ ℂ) : (z^2-w^2)*scalarStateCrossMass (A (Coeff.ofFinsupp a)) (B (Coeff.ofFinsupp a)) =
      (A (Coeff.ofFinsupp a) ⟨1,by norm_num⟩).1*(B (Coeff.ofFinsupp a) ⟨1,by norm_num⟩).2-
      (A (Coeff.ofFinsupp a) ⟨1,by norm_num⟩).2*(B (Coeff.ofFinsupp a) ⟨1,by norm_num⟩).1 := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have he : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)=Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    dsimp only [A,B]
    rw [← he]
    simpa only [scalarStateCrossMass_hill_eq_classical,hillL2FrequencyStateCurve_eq_classical] using
      classicalHillFlow_lagrange_identity (hillUnitPotentialCurve Q) (z^2) (w^2)
  have he : (fun a : Coeff 2 => (z^2-w^2)*scalarStateCrossMass (A a) (B a)) =
      (fun a : Coeff 2 => (A a ⟨1,by norm_num⟩).1*(B a ⟨1,by norm_num⟩).2-
        (A a ⟨1,by norm_num⟩).2*(B a ⟨1,by norm_num⟩).1) :=
    (Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer hL hR (funext hfinite)
  exact congrFun he q

end NLS.KdV
