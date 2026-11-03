import NLS.KdV.HillLogNormingRegularity

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal

namespace NLS.KdV

def hillDirichletLogGardnerBracket
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m) : ℂ :=
  ∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn) x*
    deriv (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q m hm)) x

theorem hillDirichletLogGardnerBracket_eq
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m) :
    hillDirichletLogGardnerBracket q n m hn hm=if n=m then -(1/2 : ℂ) else 0 := by
  let A := hillDirichletStateCurve q n hn
  let B := hillDirichletStateCurve q m hm
  let C := hillDirichletCosineCurve q m hm
  let M := scalarStateMass A
  let alpha := hillLogNormingProjection q m hm
  let P (x : ℝ) := (NLS.LinearVolterra.extend A x).1^2*
    ((NLS.LinearVolterra.extend C x).2*(NLS.LinearVolterra.extend B x).1+
      (NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend B x).2)
  let Q (x : ℝ) := (NLS.LinearVolterra.extend A x).1^2*(NLS.LinearVolterra.extend B x).1*(NLS.LinearVolterra.extend B x).2
  have hA := continuous_extend A
  have hB := continuous_extend B
  have hC := continuous_extend C
  have hP : Continuous P := (hA.fst.pow 2).mul ((hC.snd.mul hB.fst).add (hC.fst.mul hB.snd))
  have hQ : Continuous Q := ((hA.fst.pow 2).mul hB.fst).mul hB.snd
  have hdiff : deriv (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q m hm))
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] NLS.LinearVolterra.extend (hillLogNormingGradientSpatialCurve q m hm) := by
    filter_upwards [ae_hasDerivAt_hillLogNormingGradientCurve q m hm] with x hx
    exact hx.deriv
  have hform : hillDirichletLogGardnerBracket q n m hn hm=
      (M : ℂ)⁻¹*scalarStateMixedPairing A C B-
        (2*alpha*(M : ℂ)⁻¹)*scalarStateSquaredPairing A B := by
    calc
      hillDirichletLogGardnerBracket q n m hn hm=
          ∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn) x*
            NLS.LinearVolterra.extend (hillLogNormingGradientSpatialCurve q m hm) x := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
        filter_upwards [hdiff] with x hx
        rw [hx]
      _ = ∫ x in (0 : ℝ)..1,(M : ℂ)⁻¹*P x-(2*alpha*(M : ℂ)⁻¹)*Q x := by
        apply intervalIntegral.integral_congr
        intro x _
        change ((M : ℂ)⁻¹*(NLS.LinearVolterra.extend A x).1^2)*
          (((NLS.LinearVolterra.extend C x).2*(NLS.LinearVolterra.extend B x).1+
            (NLS.LinearVolterra.extend C x).1*(NLS.LinearVolterra.extend B x).2)-
            (2*alpha)*((NLS.LinearVolterra.extend B x).1*(NLS.LinearVolterra.extend B x).2))=_
        dsimp only [P,Q]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub ((hP.const_mul _).intervalIntegrable 0 1) ((hQ.const_mul _).intervalIntegrable 0 1),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
          scalarStateMixedPairing_eq_integral,scalarStateSquaredPairing_eq_integral]
  rw [hform,scalarStateSquaredPairing_hillDirichletState_zero,mul_zero,sub_zero]
  by_cases hnm : n=m
  · subst m
    rw [if_pos rfl,scalarStateMixedPairing_hillDirichlet_diagonal,hillDirichletState_crossMass_self]
    have hM : (M : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hillDirichletState_mass_pos q n hn).ne'
    change (M : ℂ)⁻¹*(-(M : ℂ)/2)= -(1/2 : ℂ)
    field_simp
  · rw [if_neg hnm,scalarStateMixedPairing_hillDirichlet_ne q n m hn hm hnm,mul_zero]

end NLS.KdV
