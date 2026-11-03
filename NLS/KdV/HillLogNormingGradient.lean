import NLS.KdV.HillDirichletSlopeVariation
import NLS.KdV.HillDirichletSlopeShift

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem hillL2DirichletSlope_energy_integral (q : Coeff 2) (energy : ℂ) :
    deriv (hillL2DirichletSlope q) energy=
      (∫ x in (0 : ℝ)..1,(NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1)) x).1^2)*
        (hillL2FrequencyStateCurve q (Complex.sqrt energy) (1,0) ⟨1,by norm_num⟩).2-
      (∫ x in (0 : ℝ)..1,(NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q (Complex.sqrt energy) (1,0)) x).1*
          (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q (Complex.sqrt energy) (0,1)) x).1)*
        hillL2DirichletSlope q energy := by
  have hunit (f : ℝ → ℂ) :
      (∫ x in (0 : ℝ)..1,-(hillPhysicalDirection (lp.single 2 0 1)).ofLp.2 x*f x)=
      ∫ x in (0 : ℝ)..1,f x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
    filter_upwards [hillPhysicalDirection_one_lower_ae] with x hx
    rw [hx]
    ring
  rw [hillL2DirichletSlope_energy_deriv_eq_constant_direction,hillL2DirichletSlope_potential_integral]
  simp only [mul_assoc]
  rw [hunit,hunit]
  ring

theorem hillDirichlet_log_branch_fderiv_integral
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p)=0)
    (h : Coeff 2) :
    let p := SpectralWeight.one.toCoeff q.val
    let S := hillL2FrequencyStateCurve p (Complex.sqrt (a p)) (0,1)
    let C := hillL2FrequencyStateCurve p (Complex.sqrt (a p)) (1,0)
    (fderiv ℂ (fun r : Coeff 2 => log ((-1 : ℂ)^n*hillL2DirichletSlope r (a r))) p) h=
      (∫ x in (0 : ℝ)..1,-(hillPhysicalDirection h).ofLp.2 x*(NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend S x).1)-
      (scalarStateCrossMass C S/(scalarStateMass S : ℂ))*
        (∫ x in (0 : ℝ)..1,-(hillPhysicalDirection h).ofLp.2 x*(NLS.LinearVolterra.extend S x).1^2) := by
  dsimp only
  let p := SpectralWeight.one.toCoeff q.val
  let energy := a p
  let S := hillL2FrequencyStateCurve p (Complex.sqrt energy) (0,1)
  let C := hillL2FrequencyStateCurve p (Complex.sqrt energy) (1,0)
  let M := scalarStateMass S
  let CS := scalarStateCrossMass C S
  let Hss := ∫ x in (0 : ℝ)..1,-(hillPhysicalDirection h).ofLp.2 x*(NLS.LinearVolterra.extend S x).1^2
  let Hcs := ∫ x in (0 : ℝ)..1,-(hillPhysicalDirection h).ofLp.2 x*(NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend S x).1
  let g := hillL2DirichletSlope p energy
  let r := (C ⟨1,by norm_num⟩).2
  have hreal : energy.im=0 := by dsimp only [energy,p];rw [ha0];rfl
  have hSreal (t : Icc (0 : ℝ) 1) : (S t).1.im=0 :=
    (hillL2FrequencyStateCurve_real p q.property.2 _ (by rw [complex_sqrt_sq];exact hreal) (0,1) (by norm_num) t).1
  have hsq : (∫ x in (0 : ℝ)..1,(NLS.LinearVolterra.extend S x).1^2)=(M : ℂ) := by
    have hh := scalarStateCrossMass_self_real S hSreal
    rw [scalarStateCrossMass_eq_integral] at hh
    simpa only [pow_two] using hh
  have hcs : (∫ x in (0 : ℝ)..1,(NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend S x).1)=CS :=
    (scalarStateCrossMass_eq_integral C S).symm
  have hM : (M : ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (hillL2FrequencyStateCurve_mass_pos p (Complex.sqrt energy) (0,1)
      (by intro hh;have hh' := congrArg Prod.snd hh;norm_num at hh')).ne'
  have hzeq : (fun v : Coeff 2 => hillL2DirichletCharacteristic v (a v))=ᶠ[𝓝 p] (fun _ => (0 : ℂ)) := hz
  have hzero : hillL2DirichletCharacteristic p energy=0 := hzeq.eq_of_nhds
  have hg : g≠0 := hillL2DirichletSlope_ne_zero_at_dirichlet_zero p q.property.2 energy hzero
  have hpot : (fderiv ℂ (fun v : Coeff 2 => hillL2DirichletSlope v energy) p) h= -Hss*r+Hcs*g :=
    hillL2DirichletSlope_potential_integral p h energy
  have he : deriv (hillL2DirichletSlope p) energy=(M : ℂ)*r-CS*g := by
    have hh := hillL2DirichletSlope_energy_integral p energy
    change deriv (hillL2DirichletSlope p) energy=
      (∫ x in (0 : ℝ)..1,(NLS.LinearVolterra.extend S x).1^2)*r-
        (∫ x in (0 : ℝ)..1,(NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend S x).1)*g at hh
    rw [hsq,hcs] at hh
    exact hh
  have hroot : (fderiv ℂ a p) h=Hss/(M : ℂ) := hillDirichlet_branch_fderiv_integral p q.property.2 a ha hz h
  have hlog := hillDirichlet_log_branch_fderiv_apply q n hn a ha ha0 h
  change (fderiv ℂ (fun v : Coeff 2 => log ((-1 : ℂ)^n*hillL2DirichletSlope v (a v))) p) h=
    Hcs-CS/(M : ℂ)*Hss
  rw [hlog,hpot,he,hroot]
  change ((-Hss*r+Hcs*g)+((M : ℂ)*r-CS*g)*(Hss/(M : ℂ)))/g=Hcs-CS/(M : ℂ)*Hss
  field_simp
  ring

end NLS.KdV
