import NLS.KdV.HillMixedGardnerBrackets
import NLS.KdV.ClassicalHillLogNormingBrackets

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal

namespace NLS.KdV

def hillLogNormingGardnerBracket
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m) : ℂ :=
  ∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn) x*
    deriv (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q m hm)) x

theorem hillLogNormingGardnerBracket_diagonal
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    hillLogNormingGardnerBracket q n n hn hn=0 := by
  let f := NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn)
  have hH := hillLogNormingGradient_H1 q n hn
  have hi : IntervalIntegrable (deriv f) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mpr
      (hH.2.2.integrable (by norm_num))
  have hip := NLS.FunctionalAnalysis.integral_mul_deriv_eq_complex hH.1 hH.1 hi hi
  have h0 : f 0=0 := by
    simpa only [f,NLS.LinearVolterra.extend,projIcc_of_mem _ (show (0 : ℝ)∈Icc 0 1 by norm_num)] using
      (hillLogNormingGradientCurve_endpoints q n hn).1
  have h1 : f 1=0 := by
    simpa only [f,NLS.LinearVolterra.extend,projIcc_of_mem _ (show (1 : ℝ)∈Icc 0 1 by norm_num)] using
      (hillLogNormingGradientCurve_endpoints q n hn).2
  have hswap : (∫ x in (0 : ℝ)..1,deriv f x*f x)=(∫ x in (0 : ℝ)..1,f x*deriv f x) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact mul_comm _ _
  change (∫ x in (0 : ℝ)..1,f x*deriv f x)=0
  change (∫ x in (0 : ℝ)..1,f x*deriv f x)=f 1*f 1-f 0*f 0-(∫ x in (0 : ℝ)..1,deriv f x*f x) at hip
  rw [h0,h1,hswap,mul_zero,sub_self,zero_sub] at hip
  linear_combination hip/2

theorem hillLogNormingGardnerBracket_zero_of_ne
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m) (hne : n≠m) :
    hillLogNormingGardnerBracket q n m hn hm=0 := by
  let F (p : RealPeriodOneHillPotential) := NLS.FunctionalAnalysis.unitComplexCurveIntegral
    (hillLogNormingGradientCurve p n hn*hillLogNormingGradientSpatialCurve p m hm)
  have hF : Continuous F :=
    NLS.FunctionalAnalysis.unitComplexCurveIntegral.continuous.comp
      ((continuous_hillLogNormingGradientCurve n hn).mul (continuous_hillLogNormingGradientSpatialCurve m hm))
  have hfinite (N : ℕ) : F (hillRealPeriodOneTruncate N q)=0 := by
    let r := hillRealPeriodOneTruncate N q
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) (hillRealPeriodOneTruncationFinsupp N q))
    let a : ℝ := hillDirichletEnergy r.val r.property.1 r.property.2 n hn
    let b : ℝ := hillDirichletEnergy r.val r.property.1 r.property.2 m hm
    let alpha := hillLogNormingProjection r n hn
    let beta := hillLogNormingProjection r m hm
    let Ca := hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt (a : ℂ)) (1,0)
    let Sa := hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt (a : ℂ)) (0,1)
    let Cb := hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt (b : ℂ)) (1,0)
    let Sb := hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt (b : ℂ)) (0,1)
    have he : hillContinuousCoefficients Q=r.val := hillContinuousCoefficients_realPeriodOneTruncation N q
    have hza : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff r.val) a=0 :=
      hillDirichletEnergy_zero r.val r.property.1 r.property.2 n hn
    have hzb : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff r.val) b=0 :=
      hillDirichletEnergy_zero r.val r.property.1 r.property.2 m hm
    have hab : (a : ℂ)≠(b : ℂ) := hillDirichletEnergy_ne_of_ne r n m hn hm hne
    rw [← he,hillL2DirichletCharacteristic_eq_classical] at hza hzb
    have heval : F r=
        ∫ x in (0 : ℝ)..1,
          ((classicalHillFlow (hillUnitPotentialCurve Q) a (1,0) x).1*(classicalHillFlow (hillUnitPotentialCurve Q) a (0,1) x).1-
            alpha*(classicalHillFlow (hillUnitPotentialCurve Q) a (0,1) x).1^2)*
          ((classicalHillFlow (hillUnitPotentialCurve Q) b (1,0) x).2*(classicalHillFlow (hillUnitPotentialCurve Q) b (0,1) x).1+
            (classicalHillFlow (hillUnitPotentialCurve Q) b (1,0) x).1*(classicalHillFlow (hillUnitPotentialCurve Q) b (0,1) x).2-
            (2*beta)*((classicalHillFlow (hillUnitPotentialCurve Q) b (0,1) x).1*(classicalHillFlow (hillUnitPotentialCurve Q) b (0,1) x).2)) := by
      change (∫ x in (0 : ℝ)..1,
        ((NLS.LinearVolterra.extend Ca x).1*(NLS.LinearVolterra.extend Sa x).1-alpha*(NLS.LinearVolterra.extend Sa x).1^2)*
        ((NLS.LinearVolterra.extend Cb x).2*(NLS.LinearVolterra.extend Sb x).1+
          (NLS.LinearVolterra.extend Cb x).1*(NLS.LinearVolterra.extend Sb x).2-
          (2*beta)*((NLS.LinearVolterra.extend Sb x).1*(NLS.LinearVolterra.extend Sb x).2)))=_
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x∈Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
      have hstate (e : ℝ) (v : ℂ × ℂ) :
          NLS.LinearVolterra.extend (hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff r.val) (Complex.sqrt (e : ℂ)) v) x=
            classicalHillFlow (hillUnitPotentialCurve Q) e v x := by
        have hh := hillL2FrequencyStateCurve_eq_classical Q (Complex.sqrt (e : ℂ)) v ⟨x,hx'⟩
        rw [he,complex_sqrt_sq] at hh
        simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ hx'] using hh
      dsimp only [Ca,Sa,Cb,Sb]
      rw [hstate a (1,0),hstate a (0,1),hstate b (1,0),hstate b (0,1)]
    rw [heval]
    exact classicalHill_log_cotangent_pairing_zero_of_ne (hillUnitPotentialCurve Q) a b alpha beta hab hza hzb
  have ht := hF.continuousAt.tendsto.comp (tendsto_hillRealPeriodOneTruncate q)
  have heq : (fun N : ℕ => F (hillRealPeriodOneTruncate N q))=(fun _ : ℕ => (0 : ℂ)) := funext hfinite
  change Tendsto (fun N : ℕ => F (hillRealPeriodOneTruncate N q)) atTop (𝓝 (F q)) at ht
  rw [heq] at ht
  have hzero : F q=0 := tendsto_nhds_unique ht tendsto_const_nhds
  calc
    hillLogNormingGardnerBracket q n m hn hm=F q := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
      filter_upwards [ae_hasDerivAt_hillLogNormingGradientCurve q m hm] with x hx
      change NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn) x*
        deriv (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q m hm)) x=
          NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn) x*
            NLS.LinearVolterra.extend (hillLogNormingGradientSpatialCurve q m hm) x
      rw [hx.deriv]
    _ = 0 := hzero

theorem hillLogNormingGardnerBracket_eq_zero
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m) :
    hillLogNormingGardnerBracket q n m hn hm=0 := by
  by_cases hnm : n=m
  · subst m
    exact hillLogNormingGardnerBracket_diagonal q n hn
  · exact hillLogNormingGardnerBracket_zero_of_ne q n m hn hm hnm

end NLS.KdV
