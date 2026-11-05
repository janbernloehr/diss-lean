import NLS.KdV.HillPhysicalDirectionPairing
import NLS.KdV.HillDirichletMixedPairings

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal

namespace NLS.KdV

def hillLogNormingProjection (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) : ℂ :=
  scalarStateCrossMass (hillDirichletCosineCurve q n hn) (hillDirichletStateCurve q n hn)/
    (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)

def hillLogNormingGradientCurve (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) : Curve ℂ :=
  ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillDirichletCosineCurve q n hn))*
      ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillDirichletStateCurve q n hn))-
    hillLogNormingProjection q n hn • (((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillDirichletStateCurve q n hn))^2)

def hillLogNormingGradientSpatialCurve (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) : Curve ℂ :=
  ((ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp (hillDirichletCosineCurve q n hn))*
      ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillDirichletStateCurve q n hn))+
    ((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillDirichletCosineCurve q n hn))*
      ((ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp (hillDirichletStateCurve q n hn))-
    (2*hillLogNormingProjection q n hn) •
      (((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillDirichletStateCurve q n hn))*
        ((ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp (hillDirichletStateCurve q n hn)))

theorem hillLogNormingGradient_represents_branch
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p)=0)
    (h : Coeff 2) :
    (fderiv ℂ (fun r : Coeff 2 => log ((-1 : ℂ)^n*hillL2DirichletSlope r (a r)))
      (SpectralWeight.one.toCoeff q.val)) h=
      ∫ x in (0 : ℝ)..1,-(hillPhysicalDirection h).ofLp.2 x*
        NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn) x := by
  let S := hillDirichletStateCurve q n hn
  let C := hillDirichletCosineCurve q n hn
  let Sf := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp S
  let Cf := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp C
  let T := hillPhysicalDirectionPairing h
  have hcs : T (Cf*Sf)=∫ x in (0 : ℝ)..1,-(hillPhysicalDirection h).ofLp.2 x*
      (NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend S x).1 := by
    rw [hillPhysicalDirectionPairing_apply]
    apply intervalIntegral.integral_congr
    intro x _
    change -(hillPhysicalDirection h).ofLp.2 x*((NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend S x).1)=_
    ring
  have hss : T (Sf^2)=∫ x in (0 : ℝ)..1,-(hillPhysicalDirection h).ofLp.2 x*
      (NLS.LinearVolterra.extend S x).1^2 := by rw [hillPhysicalDirectionPairing_apply];rfl
  have hf := hillDirichlet_log_branch_fderiv_integral q n hn a ha ha0 hz h
  dsimp only at hf
  rw [ha0] at hf
  rw [← hillPhysicalDirectionPairing_apply]
  change _=T (Cf*Sf-hillLogNormingProjection q n hn • Sf^2)
  rw [map_sub,map_smul,smul_eq_mul,hcs,hss]
  exact hf

theorem absolutelyContinuousOnInterval_hillLogNormingGradientCurve
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn)) 0 1 := by
  have hS := absolutelyContinuousOnInterval_hillStateCurve (SpectralWeight.one.toCoeff q.val)
    (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (0,1)
  have hC := absolutelyContinuousOnInterval_hillStateCurve (SpectralWeight.one.toCoeff q.val)
    (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (1,0)
  have hSf := NLS.FunctionalAnalysis.absolutelyContinuousOnInterval_clm hS (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hCf := NLS.FunctionalAnalysis.absolutelyContinuousOnInterval_clm hC (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hh := (hCf.smul hSf).sub ((hSf.smul hSf).const_smul (hillLogNormingProjection q n hn))
  convert! hh using 1
  funext x
  let S := hillDirichletStateCurve q n hn
  let C := hillDirichletCosineCurve q n hn
  change (NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend S x).1-
      hillLogNormingProjection q n hn*(NLS.LinearVolterra.extend S x).1^2=
    (NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend S x).1-
      hillLogNormingProjection q n hn*((NLS.LinearVolterra.extend S x).1*(NLS.LinearVolterra.extend S x).1)
  ring

theorem ae_hasDerivAt_hillLogNormingGradientCurve
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn))
        (NLS.LinearVolterra.extend (hillLogNormingGradientSpatialCurve q n hn) x) x := by
  have hs := ae_hasDerivAt_hillL2FrequencyStateCurve_fst (SpectralWeight.one.toCoeff q.val)
    (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (0,1)
  have hc := ae_hasDerivAt_hillL2FrequencyStateCurve_fst (SpectralWeight.one.toCoeff q.val)
    (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (1,0)
  filter_upwards [hs,hc] with x hS hC
  have hh := (hC.mul hS).sub ((hS.pow 2).const_mul (hillLogNormingProjection q n hn))
  convert! hh using 1
  let S := hillDirichletStateCurve q n hn
  let C := hillDirichletCosineCurve q n hn
  change ((NLS.LinearVolterra.extend C x).2*(NLS.LinearVolterra.extend S x).1+
      (NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend S x).2)-
      (2*hillLogNormingProjection q n hn)*((NLS.LinearVolterra.extend S x).1*(NLS.LinearVolterra.extend S x).2)=
    ((NLS.LinearVolterra.extend C x).2*(NLS.LinearVolterra.extend S x).1+
      (NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend S x).2)-
      hillLogNormingProjection q n hn*((2 : ℂ)*(NLS.LinearVolterra.extend S x).1^(2-1)*(NLS.LinearVolterra.extend S x).2)
  simp only [show 2-1=1 from rfl,pow_one]
  ring

end NLS.KdV
