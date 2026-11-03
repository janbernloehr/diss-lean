import NLS.KdV.HillDirichletSimplicity
import NLS.KdV.HillRealGapSigns
import NLS.ComplexAnalysis.RealSimpleZeroSigns
import NLS.ComplexAnalysis.PositiveZeroUniqueness

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem hillL2DirichletCharacteristic_real (q : Coeff 2) (hq : IsRealHillPotential q) (x : ℝ) :
    (hillL2DirichletCharacteristic q x).im=0 := by
  exact (hillL2FrequencyStateCurve_real q hq (Complex.sqrt x)
    (by rw [complex_sqrt_sq];exact Complex.ofReal_im x) (0,1) (by norm_num) ⟨1,by norm_num⟩).1

theorem hillL2DirichletCharacteristic_signed_deriv_pos
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) (x : ℝ)
    (hx : x∈Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)))
    (hz : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) x=0) :
    0<(-1 : ℝ)^n*(deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) x).re := by
  let p := SpectralWeight.one.toCoeff q
  let z := Complex.sqrt (x : ℂ)
  let t : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  let c := (hillL2FrequencyStateCurve p z (1,0) t).1.re
  let g := (hillL2FrequencyStateCurve p z (0,1) t).2.re
  let d := (deriv (hillL2DirichletCharacteristic p) x).re
  let D := (hillL2Discriminant p x).re
  let s : ℝ := (-1)^n
  have hs : s^2=1 := by dsimp [s];rw [← pow_mul,Nat.mul_comm n 2,pow_mul];norm_num
  have he : z^2=(x : ℂ) := complex_sqrt_sq _
  have hre : (z^2).im=0 := by rw [he];rfl
  have hD : (hillL2FrequencyStateCurve p z (0,1) t).1=0 := hz
  have hc := (hillL2FrequencyStateCurve_real p hr z hre (1,0) (by norm_num) t).1
  have hg := (hillL2FrequencyStateCurve_real p hr z hre (0,1) (by norm_num) t).2
  have hw := hillL2FrequencyStateCurve_wronskian p z t
  rw [hD,zero_mul,sub_zero] at hw
  have hprod : c*g=1 := by
    simpa only [mul_re,hc,hg,mul_zero,sub_zero,one_re] using congrArg Complex.re hw
  have htrace : c+g=D := by
    have hh := congrArg Complex.re (hillL2FrequencyStateCurve_trace p z)
    rw [← hillL2Discriminant_sq,he] at hh
    exact hh
  have hbound : 2≤s*D := hillL2Discriminant_signed_gap_ge_two q hq hr n hn x hx
  have hsg : 0<s*g := by
    have hid : (s*D)*(s*g)=g^2+1 := by
      calc
        _ = s^2*(D*g) := by ring
        _ = g^2+1 := by rw [hs,one_mul,← htrace];nlinarith only [hprod]
    have hp : 0<(s*D)*(s*g) := by rw [hid];positivity
    exact pos_of_mul_pos_right hp (by linarith)
  have hnorm := congrArg Complex.re (hillL2Dirichlet_derivative_normalization p hr x hz)
  have hnorm' : d*g=NLS.ComplexAnalysis.scalarStateMass (hillL2FrequencyStateCurve p z (0,1)) := by
    change (deriv (hillL2DirichletCharacteristic p) x).re*g-
      (deriv (hillL2DirichletCharacteristic p) x).im*
        (hillL2FrequencyStateCurve p z (0,1) t).2.im = _ at hnorm
    simpa only [hg,mul_zero,sub_zero,ofReal_re] using hnorm
  have hmass := hillL2FrequencyStateCurve_mass_pos p z (0,1)
    (by intro hh;have hh' := congrArg Prod.snd hh;norm_num at hh')
  change 0<s*d
  have hid : (s*d)*(s*g)=d*g := by calc
    _ = s^2*(d*g) := by ring
    _ = d*g := by rw [hs,one_mul]
  have hp : 0<(s*d)*(s*g) := by rw [hid,hnorm'];exact hmass
  exact pos_of_mul_pos_left hp hsg.le

theorem hillL2Dirichlet_zero_unique_in_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n)
    (x y : ℝ)
    (hx : x∈Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)))
    (hy : y∈Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)))
    (hzx : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) x=0)
    (hzy : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) y=0) : x=y := by
  let p := SpectralWeight.one.toCoeff q
  let s : ℝ := (-1)^n
  have hs : s≠0 := pow_ne_zero _ (by norm_num)
  have ordered (a b : ℝ) (hab : a≤b)
      (ha : a∈Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)))
      (hb : b∈Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)))
      (hza : hillL2DirichletCharacteristic p a=0)
      (hzb : hillL2DirichletCharacteristic p b=0) : a=b := by
    apply eq_of_zero_of_pos_derivative_at_zeros
      (fun t : ℝ => s*(hillL2DirichletCharacteristic p t).re)
      (fun t : ℝ => s*(deriv (hillL2DirichletCharacteristic p) t).re) a b hab
    · intro t _
      exact ((analyticOnNhd_hillL2DirichletCharacteristic p t (mem_univ _)).differentiableAt.hasDerivAt.real_of_complex).const_mul s
    · intro t ht hz
      have hrt : hillL2DirichletCharacteristic p t=0 := by
        apply Complex.ext _ (hillL2DirichletCharacteristic_real p hr t)
        exact (mul_eq_zero.mp hz).resolve_left hs
      exact hillL2DirichletCharacteristic_signed_deriv_pos q hq hr n hn t
        ⟨le_trans ha.1 ht.1,le_trans ht.2 hb.2⟩ hrt
    · simp only [hza,zero_re,mul_zero]
    · simp only [hzb,zero_re,mul_zero]
  rcases le_total x y with hxy | hyx
  · exact ordered x y hxy hx hy hzx hzy
  · exact (ordered y x hyx hy hx hzy hzx).symm

end NLS.KdV
