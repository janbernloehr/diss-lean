import NLS.KdV.HillQuinticLocalResolvent
import NLS.KdV.HillCubicFrequencyCircle
import NLS.KdV.HillL2EnergySquareCircleAsymptotics
/-! # Actual quintic kernel and its mass correction on full circles -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ContDiff ComplexConjugate
namespace NLS.KdV

private def quinticKernelRemainder (a q b : ℂ) (p : (ℂ × ℂ) × ℂ) : ℂ :=
  let u := p.1.1
  let d := p.1.2
  let e := p.2
  let v := a+d*u^2
  let h := v*u^4
  let B := I/2+I*q*u^2/4+I*b*u^4/16+e*u^5
  (-I)^5*e+5*(-I)^4*(d*u*I/2+v*(I*q*u/4+I*b*u^3/16+e*u^4))+
    u^3*v^2*(10*(-I)^3+10*(-I)^2*h+5*(-I)*h^2+h^3)*B

private theorem quintic_kernel_polynomial_identity (a q b u d e : ℂ) :
    (-I+(a+d*u^2)*u^4)^5*(I/2+I*q*u^2/4+I*b*u^4/16+e*u^5)=
      1/2+q*u^2/4+b*u^4/16+5*I*a*u^4/2+
        u^5*quinticKernelRemainder a q b ((u,d),e) := by
  have hbin (A h : ℂ) : (A+h)^5=A^5+5*A^4*h+
      h^2*(10*A^3+10*A^2*h+5*A*h^2+h^3) := by ring
  rw [hbin]
  dsimp only [quinticKernelRemainder]
  ring_nf
  simp only [I_sq,I_pow_four,
    show I^3=-I by rw [pow_succ,I_sq];ring,
    show I^5=I by rw [pow_succ,I_pow_four];ring,
    show I^6=(-1:ℂ) by rw [show 6=2*3 from rfl,pow_mul,I_sq];norm_num]
  ring

private theorem exists_norm_quintic_kernel_error_bound (a q b : ℂ) (CE CG : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ z F G : ℂ, 1≤‖z‖ →
      ‖z‖^5*‖F+I*z-a/z^3‖≤CE →
      ‖z‖^6*‖G-I/(2*z)-I*q/(4*z^3)-I*b/(16*z^5)‖≤CG →
      ‖z‖*‖F^5*G-(z^4/2+q*z^2/4+b/16+5*I*a/2)‖≤C := by
  have hc : Continuous (quinticKernelRemainder a q b) := by
    unfold quinticKernelRemainder
    fun_prop
  let K : Set ((ℂ × ℂ) × ℂ) := (closedBall 0 1 ×ˢ closedBall 0 CE) ×ˢ closedBall 0 CG
  have hK : IsCompact K := (isCompact_closedBall (0:ℂ) 1 |>.prod
    (isCompact_closedBall (0:ℂ) CE)).prod (isCompact_closedBall (0:ℂ) CG)
  obtain ⟨C,hC,hbound⟩ := (hK.image hc).isBounded.exists_pos_norm_le
  refine ⟨C,hC,?_⟩
  intro z F G hz hF hG
  have hzpos : 0<‖z‖ := by linarith
  have hz0 : z≠0 := norm_pos_iff.mp hzpos
  let u := z⁻¹
  let d := (F+I*z-a/z^3)*z^5
  let e := (G-I/(2*z)-I*q/(4*z^3)-I*b/(16*z^5))*z^6
  have hu : ‖u‖≤1 := by dsimp only [u];rw [norm_inv];exact inv_le_one_of_one_le₀ hz
  have hd : ‖d‖≤CE := by simpa only [d,norm_mul,norm_pow,mul_comm] using hF
  have he : ‖e‖≤CG := by simpa only [e,norm_mul,norm_pow,mul_comm] using hG
  have hH : ‖quinticKernelRemainder a q b ((u,d),e)‖≤C :=
    hbound _ ⟨((u,d),e),⟨⟨by simpa using hu,by simpa using hd⟩,by simpa using he⟩,rfl⟩
  have hFp : F=z*(-I+(a+d*u^2)*u^4) := by
    dsimp only [d,u]
    field_simp [hz0]
    ring
  have hGp : G=u*(I/2+I*q*u^2/4+I*b*u^4/16+e*u^5) := by
    dsimp only [e,u]
    field_simp [hz0]
    ring
  have hmain : F^5*G-(z^4/2+q*z^2/4+b/16+5*I*a/2)=
      u*quinticKernelRemainder a q b ((u,d),e) := by
    rw [hFp,hGp,mul_pow]
    have hzu : z^5*u=z^4 := by dsimp only [u];field_simp
    rw [show z^5*(-I+(a+d*u^2)*u^4)^5*
        (u*(I/2+I*q*u^2/4+I*b*u^4/16+e*u^5))=
      (z^5*u)*((-I+(a+d*u^2)*u^4)^5*
        (I/2+I*q*u^2/4+I*b*u^4/16+e*u^5)) by ring,hzu,
      quintic_kernel_polynomial_identity]
    dsimp only [u]
    field_simp [hz0]
    ring
  rw [hmain,norm_mul]
  have hscale : ‖z‖*‖u‖=1 := by dsimp only [u];rw [norm_inv];exact mul_inv_cancel₀ hzpos.ne'
  calc
    _ = (‖z‖*‖u‖)*‖quinticKernelRemainder a q b ((u,d),e)‖ := by ring
    _ = ‖quinticKernelRemainder a q b ((u,d),e)‖ := by rw [hscale,one_mul]
    _ ≤ C := hH
theorem exists_hillL2RealCutPrimitive_upper_arc_cubic_coefficient_error_bound
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0) :
    ∃ C : ℝ, 0<C ∧ ∃ K : ℕ, ∀ n : ℕ, K≤n → ∀ t : Icc (0:ℝ) Real.pi,
      let z := hillFreeUpperFrequency n t
      (hillFreeBandFrequency n)^5*
        ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)+I*z-
          I*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))/(4*z^3)‖≤C := by
  let f : ℝ → ℂ := fun x => Q (x : AddCircle (2:ℝ))
  let a := I*classicalQuadraticInvariant f/4
  let b := I*classicalHamiltonian f/16
  obtain ⟨D,hD,K₀,hbound⟩ := exists_hillL2RealCutPrimitive_upper_arc_physical_error_bound Q hq hr hf hp hmean 0
  obtain ⟨K₁,hK₁⟩ := Filter.eventually_atTop.mp (tendsto_hillFreeBandFrequency.eventually_ge_atTop 1)
  refine ⟨D+‖b‖+1,by positivity,max K₀ K₁,?_⟩
  intro n hn t
  let z := hillFreeUpperFrequency n t
  let r := hillFreeBandFrequency n
  let F := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  have hz : ‖z‖=r := norm_hillFreeUpperFrequency n t
  have hr1 : 1≤r := hK₁ n ((le_max_right _ _).trans hn)
  have hrpos : 0<r := by linarith
  have hz0 : z≠0 := norm_pos_iff.mp (by rw [hz];exact hrpos)
  have h := hbound n ((le_max_left _ _).trans hn) t
  simp only [Finset.range_zero,Finset.sum_empty,sub_zero,Nat.zero_add] at h
  have he : F+I*(z-classicalQuadraticInvariant f/(4*z^3)-classicalHamiltonian f/(16*z^5))=
      F+I*z-a/z^3-b/z^5 := by dsimp only [a,b];ring
  change ‖F+I*(z-classicalQuadraticInvariant f/(4*z^3)-classicalHamiltonian f/(16*z^5))‖≤D/(2*r)^5 at h
  rw [he] at h
  have hcross : ‖F+I*z-a/z^3-b/z^5‖*(2*r)^5≤D := (le_div_iff₀ (by positivity)).mp h
  have hrpow : r^5≤(2*r)^5 := (pow_le_pow_left₀ hrpos.le (by linarith : r≤2*r) 5).trans
    (pow_le_pow_right₀ (by linarith : 1≤2*r) (by omega : 5≤5))
  have hδ : r^5*‖F+I*z-a/z^3-b/z^5‖≤D := by
    nlinarith [mul_le_mul_of_nonneg_left hrpow (norm_nonneg (F+I*z-a/z^3-b/z^5))]
  have hb := norm_weighted_laurent_term_le z b (by rw [hz];exact hr1) 5 5 le_rfl
  rw [hz] at hb
  have hsum : F+I*z-a/z^3=(F+I*z-a/z^3-b/z^5)+b/z^5 := by ring
  have hnorm := norm_add_le (F+I*z-a/z^3-b/z^5) (b/z^5)
  rw [← hsum] at hnorm
  have hh := mul_le_mul_of_nonneg_left hnorm (pow_nonneg hrpos.le 5)
  rw [mul_add] at hh
  change r^5*‖F+I*z-I*classicalQuadraticInvariant f/(4*z^3)‖≤_
  rw [show I*classicalQuadraticInvariant f/(4*z^3)=a/z^3 by dsimp only [a];ring]
  linarith



theorem exists_hillL2QuinticDirichletKernel_upper_arc_error_bound
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0) :
    ∃ C : ℝ, 0<C ∧ ∃ K : ℕ, ∀ n : ℕ, K≤n → ∀ t : Icc (0:ℝ) Real.pi,
      let f : ℝ → ℂ := fun x => Q (x : AddCircle (2:ℝ))
      let z := hillFreeUpperFrequency n t
      hillFreeBandFrequency n *
        ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)^5*
          (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)/
            hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2))-
              (z^4/2+f 0*z^2/4+(3*f 0^2-deriv (deriv f) 0)/16-
                5*classicalQuadraticInvariant f/8)‖≤C := by
  let f : ℝ → ℂ := fun x => Q (x : AddCircle (2:ℝ))
  let a := I*classicalQuadraticInvariant f/4
  let b := 3*f 0^2-deriv (deriv f) 0
  obtain ⟨CE,_hCE,KE,hphase⟩ := exists_hillL2RealCutPrimitive_upper_arc_cubic_coefficient_error_bound Q hq hr hf hp hmean
  obtain ⟨CG,_hCG,KG,hlocal⟩ := exists_hillL2Dirichlet_div_root_local_quintic_error_bound Q hq hr hf hp
  obtain ⟨C,hC,hbound⟩ := exists_norm_quintic_kernel_error_bound a (f 0) b CE CG
  obtain ⟨K₁,hK₁⟩ := eventually_atTop.mp (tendsto_hillFreeBandFrequency.eventually_ge_atTop 1)
  refine ⟨C,hC,max (max KE KG) K₁,?_⟩
  intro n hn t
  let z := hillFreeUpperFrequency n t
  let r := hillFreeBandFrequency n
  let F := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  let G := hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)/
    hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  have hz : ‖z‖=r := norm_hillFreeUpperFrequency n t
  have hF := hphase n ((le_max_left _ _).trans ((le_max_left _ _).trans hn)) t
  have hG := hlocal n ((le_max_right _ _).trans ((le_max_left _ _).trans hn)) t
  change r^5*‖F+I*z-I*classicalQuadraticInvariant f/(4*z^3)‖≤CE at hF
  have hFa : ‖z‖^5*‖F+I*z-a/z^3‖≤CE := by
    rw [hz,show a/z^3=I*classicalQuadraticInvariant f/(4*z^3) by dsimp only [a];ring]
    exact hF
  have hGb : ‖z‖^6*‖G-I/(2*z)-I*f 0/(4*z^3)-I*b/(16*z^5)‖≤CG := by
    rw [hz]
    exact hG
  have h := hbound z F G (by rw [hz];exact hK₁ n ((le_max_right _ _).trans hn)) hFa hGb
  have ha : 5*I*a/2= -5*classicalQuadraticInvariant f/8 := by
    dsimp only [a]
    ring_nf
    rw [I_sq]
    ring
  rw [ha,hz] at h
  simpa only [F,G,r,z,b,f,sub_eq_add_neg,neg_mul,neg_div] using h
theorem exists_hillL2QuinticDirichletKernel_circle_error_bound
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2:ℝ), (Q x).im=0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1)
    (hmean : (∫ x in (0:ℝ)..1, Q (x : AddCircle (2:ℝ)))=0) :
    ∃ C : ℝ, 0<C ∧ ∃ K : ℕ, ∀ n : ℕ, K≤n →
      ∀ E∈sphere (0:ℂ) ((hillFreeBandFrequency n)^2),
        hillFreeBandFrequency n *
          ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) E^5*
            (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) E/
              hillL2RealCutRoot (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) E)-
                (E^2/2+Q (0 : AddCircle (2:ℝ))*E/4+
                  (3*Q (0 : AddCircle (2:ℝ))^2-
                    deriv (deriv (fun x : ℝ => Q (x : AddCircle (2:ℝ)))) 0)/16-
                  5*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))/8)‖≤C := by
  let v : ℝ → ℂ := fun x => Q (x : AddCircle (2:ℝ))
  have hv : ∀ x, (v x).im=0 := fun x => hreal _
  have hvd : Differentiable ℝ v := (contDiff_infty_iff_deriv.mp hf).1
  have hvdd : Differentiable ℝ (deriv v) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf).2).1
  have hrealdd : (deriv (deriv v) 0).im=0 :=
    deriv_im_eq_zero_of_real (deriv v) hvdd (deriv_im_eq_zero_of_real v hvd hv) 0
  have hconjdd : conj (deriv (deriv v) 0)=deriv (deriv v) 0 :=
    Complex.conj_eq_iff_im.mpr hrealdd
  have hconjH := conj_classicalQuadraticInvariant_of_real v hv
  dsimp only [v] at hconjdd hconjH
  let q := hillContinuousCoefficients Q
  let f : ℂ → ℂ := fun E => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^5*
    (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E/
      hillL2RealCutRoot (SpectralWeight.one.toCoeff q) E)-(E^2/2+Q (0 : AddCircle (2:ℝ))*E/4+
      (3*Q (0 : AddCircle (2:ℝ))^2-deriv (deriv (fun x : ℝ => Q (x : AddCircle (2:ℝ)))) 0)/16-
      5*classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2:ℝ)))/8)
  obtain ⟨C,hC,K,hbound⟩ := exists_hillL2QuinticDirichletKernel_upper_arc_error_bound Q hq hr hf hp hmean
  refine ⟨C,hC,K,?_⟩
  intro n hn
  apply NLS.ComplexAnalysis.weighted_norm_bound_on_circle_of_upper_reflection f _ _ C
  · intro E hE hi
    have hnorm : ‖E‖=(hillFreeBandFrequency n)^2 := by
      simpa only [mem_sphere_iff_norm,sub_zero] using hE
    obtain ⟨t,ht⟩ := NLS.ComplexAnalysis.exists_upper_circleMap_parameter E _ hnorm hi
    have he : hillFreeUpperFrequency n t^2=E := (hillFreeUpperFrequency_sq n t).trans ht
    have h := hbound n hn t
    dsimp only at h
    have he4 : hillFreeUpperFrequency n t^4=E^2 := by rw [show 4=2*2 from rfl,pow_mul,he]
    rw [he4,he] at h
    exact h
  · intro E hE
    dsimp only [f]
    rw [hillL2RealCutPrimitive_conj q hq hr E hE,
      hillL2RealCutRoot_conj q hq hr E hE,
      hillL2DirichletCharacteristic_conj_of_continuous Q hreal E]
    simp only [map_sub,map_add,map_mul,map_div₀,map_pow,map_ofNat,
      hconjdd,hconjH,
      Complex.conj_eq_iff_im.mpr (hreal (0 : AddCircle (2:ℝ)))]
    ring

end NLS.KdV
