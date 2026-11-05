import NLS.KdV.HillLogNormingCotangent

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem hillDirichletState_real (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (t : Icc (0 : ℝ) 1) :
    (hillDirichletStateCurve q n hn t).1.im=0 ∧ (hillDirichletStateCurve q n hn t).2.im=0 :=
  hillL2FrequencyStateCurve_real (SpectralWeight.one.toCoeff q.val) q.property.2 _
    (by rw [complex_sqrt_sq];rfl) (0,1) (by norm_num) t

theorem hillDirichletCosine_real (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (t : Icc (0 : ℝ) 1) :
    (hillDirichletCosineCurve q n hn t).1.im=0 ∧ (hillDirichletCosineCurve q n hn t).2.im=0 :=
  hillL2FrequencyStateCurve_real (SpectralWeight.one.toCoeff q.val) q.property.2 _
    (by rw [complex_sqrt_sq];rfl) (1,0) (by norm_num) t

theorem hillDirichletState_crossMass_self (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    scalarStateCrossMass (hillDirichletStateCurve q n hn) (hillDirichletStateCurve q n hn)=
      (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ) :=
  scalarStateCrossMass_self_real _ (fun t => (hillDirichletState_real q n hn t).1)

theorem hillLogNormingGradientCurve_endpoints
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    hillLogNormingGradientCurve q n hn ⟨0,by norm_num⟩=0 ∧
      hillLogNormingGradientCurve q n hn ⟨1,by norm_num⟩=0 := by
  let S := hillDirichletStateCurve q n hn
  let C := hillDirichletCosineCurve q n hn
  have h0 : (S ⟨0,by norm_num⟩).1=0 := by
    dsimp only [S,hillDirichletStateCurve]
    rw [hillL2FrequencyStateCurve_zero]
  have h1 : (S ⟨1,by norm_num⟩).1=0 := hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn
  constructor
  · change (C ⟨0,by norm_num⟩).1*(S ⟨0,by norm_num⟩).1-
      hillLogNormingProjection q n hn*(S ⟨0,by norm_num⟩).1^2=0
    rw [h0];ring
  · change (C ⟨1,by norm_num⟩).1*(S ⟨1,by norm_num⟩).1-
      hillLogNormingProjection q n hn*(S ⟨1,by norm_num⟩).1^2=0
    rw [h1];ring

theorem hillLogNormingGradient_H1
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn)) 0 1 ∧
      MemLp (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      MemLp (deriv (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hmem (w : Curve ℂ) : MemLp (NLS.LinearVolterra.extend w) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm (continuous_extend w).aestronglyMeasurable).mpr
      (((continuous_extend w).norm.pow 2).intervalIntegrable 0 1).1
  refine ⟨absolutelyContinuousOnInterval_hillLogNormingGradientCurve q n hn,hmem _,?_⟩
  apply (hmem (hillLogNormingGradientSpatialCurve q n hn)).ae_eq
  filter_upwards [ae_hasDerivAt_hillLogNormingGradientCurve q n hn] with x hx
  exact hx.deriv.symm

theorem continuous_hillLogNormingProjection (n : ℕ) (hn : 1≤n) :
    Continuous (fun q : RealPeriodOneHillPotential => hillLogNormingProjection q n hn) := by
  have hS := continuous_hillDirichletStateCurve n hn
  have hC := continuous_hillDirichletCosineCurve n hn
  have hcs : Continuous (fun q : RealPeriodOneHillPotential =>
      scalarStateCrossMass (hillDirichletCosineCurve q n hn) (hillDirichletStateCurve q n hn)) := by
    convert! continuous_scalarStateCrossMass.comp (hC.prodMk hS) using 1
  exact hcs.div (Complex.continuous_ofReal.comp (continuous_scalarStateMass.comp hS))
    (fun q => Complex.ofReal_ne_zero.mpr (hillDirichletState_mass_pos q n hn).ne')

theorem continuous_hillLogNormingGradientCurve (n : ℕ) (hn : 1≤n) :
    Continuous (fun q : RealPeriodOneHillPotential => hillLogNormingGradientCurve q n hn) := by
  have hS := continuous_hillDirichletStateCurve n hn
  have hC := continuous_hillDirichletCosineCurve n hn
  have hs := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hS
  have hc := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hC
  exact (hc.mul hs).sub ((continuous_hillLogNormingProjection n hn).smul (hs.pow 2))

theorem continuous_hillLogNormingGradientSpatialCurve (n : ℕ) (hn : 1≤n) :
    Continuous (fun q : RealPeriodOneHillPotential => hillLogNormingGradientSpatialCurve q n hn) := by
  have hS := continuous_hillDirichletStateCurve n hn
  have hC := continuous_hillDirichletCosineCurve n hn
  have hs := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hS
  have hc := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hC
  have hsd := (ContinuousMap.snd : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hS
  have hcd := (ContinuousMap.snd : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hC
  exact ((hcd.mul hs).add (hc.mul hsd)).sub
    ((continuous_const.mul (continuous_hillLogNormingProjection n hn)).smul (hs.mul hsd))

theorem hillLogNormingGradient_integral_eq_zero
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn) x)=0 := by
  let S := hillDirichletStateCurve q n hn
  let C := hillDirichletCosineCurve q n hn
  let M := scalarStateMass S
  let CS := scalarStateCrossMass C S
  have hcs : Continuous (fun x : ℝ => (NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend S x).1) :=
    (continuous_extend C).fst.mul (continuous_extend S).fst
  have hss : Continuous (fun x : ℝ => (NLS.LinearVolterra.extend S x).1^2) := (continuous_extend S).fst.pow 2
  have hsq : (∫ x in (0 : ℝ)..1,(NLS.LinearVolterra.extend S x).1^2)=(M : ℂ) := by
    have hh := hillDirichletState_crossMass_self q n hn
    rw [scalarStateCrossMass_eq_integral] at hh
    simpa only [pow_two] using hh
  change (∫ x in (0 : ℝ)..1,(NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend S x).1-
    (CS/(M : ℂ))*(NLS.LinearVolterra.extend S x).1^2)=0
  rw [intervalIntegral.integral_sub (hcs.intervalIntegrable 0 1) ((hss.const_mul _).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul,hsq,← scalarStateCrossMass_eq_integral]
  change CS-CS/(M : ℂ)*(M : ℂ)=0
  rw [div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hillDirichletState_mass_pos q n hn).ne'),sub_self]

theorem hillLogNormingProjection_real
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    (hillLogNormingProjection q n hn).im=0 := by
  let S := hillDirichletStateCurve q n hn
  let C := hillDirichletCosineCurve q n hn
  have he : scalarStateCrossMass C S=
      ((∫ x in (0 : ℝ)..1,(NLS.LinearVolterra.extend C x).1.re*(NLS.LinearVolterra.extend S x).1.re : ℝ) : ℂ) := by
    rw [scalarStateCrossMass_eq_integral,← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _
    have hc : (C (projIcc 0 1 (by norm_num) x)).1.im=0 := (hillDirichletCosine_real q n hn _).1
    have hs : (S (projIcc 0 1 (by norm_num) x)).1.im=0 := (hillDirichletState_real q n hn _).1
    apply Complex.ext <;> simp only [NLS.LinearVolterra.extend,mul_re,mul_im,ofReal_re,ofReal_im,hc,hs,
      mul_zero,zero_mul,add_zero,sub_zero]
  change (scalarStateCrossMass C S/(scalarStateMass S : ℂ)).im=0
  rw [he,← Complex.ofReal_div]
  rfl

theorem hillLogNormingGradientCurve_real
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (t : Icc (0 : ℝ) 1) :
    (hillLogNormingGradientCurve q n hn t).im=0 := by
  let S := hillDirichletStateCurve q n hn
  let C := hillDirichletCosineCurve q n hn
  have hs : (S t).1.im=0 := (hillDirichletState_real q n hn t).1
  have hc : (C t).1.im=0 := (hillDirichletCosine_real q n hn t).1
  have ha := hillLogNormingProjection_real q n hn
  change ((C t).1*(S t).1-hillLogNormingProjection q n hn*(S t).1^2).im=0
  simp only [pow_two,mul_im,sub_im,hs,hc,ha,mul_zero,zero_mul,add_zero,sub_zero]

end NLS.KdV
