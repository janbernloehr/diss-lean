import NLS.KdV.ClassicalHillDirichletBoundaryPairing

/-! # The actual monodromy quadratic kernel and its Dirichlet pairing

The kernel is constructed from the two scalar Hill fundamental states.
We prove its spatial derivative and its exact Dirichlet boundary pairing.
Identification with the potential derivative of the discriminant is a
separate step; no such derivative identity is assumed here.
-/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

/-- The scalar fundamental matrix has determinant one at the endpoint. -/
theorem classicalHillFlow_endpoint_det (q : Curve ℂ) (b : ℂ) :
    (classicalHillFlow q b (1,0) 1).1*(classicalHillFlow q b (0,1) 1).2-
      (classicalHillFlow q b (1,0) 1).2*(classicalHillFlow q b (0,1) 1).1=1 := by
  let B := classicalHillFlow q b (1,0)
  let C := classicalHillFlow q b (0,1)
  have hB : Continuous B := continuous_classicalHillFlow q b (1,0)
  have hC : Continuous C := continuous_classicalHillFlow q b (0,1)
  have hd (t : Icc (0 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => (B x).1*(C x).2-(B x).2*(C x).1) 0 t.val := by
    have hBf : HasDerivAt (fun x : ℝ => (B x).1) (B t).2 t.val := by
      simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (1,0) t).fst
    have hBg : HasDerivAt (fun x : ℝ => (B x).2) ((q t-b)*(B t).1) t.val := by
      simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (1,0) t).snd
    have hCf : HasDerivAt (fun x : ℝ => (C x).1) (C t).2 t.val := by
      simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (0,1) t).fst
    have hCg : HasDerivAt (fun x : ℝ => (C x).2) ((q t-b)*(C t).1) t.val := by
      simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (0,1) t).snd
    convert! (hBf.mul hCg).sub (hBg.mul hCf) using 1
    ring
  have hc : Continuous (fun x : ℝ => (B x).1*(C x).2-(B x).2*(C x).1) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
    hc.continuousOn (fun x (hx : x∈Ioo (0 : ℝ) 1) => hd ⟨x,hx.1.le,hx.2.le⟩)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume 0 1)
  have hi' : (0 : ℂ) = (B 1).1*(C 1).2-(B 1).2*(C 1).1-1 := by
    simpa [B,C,classicalHillFlow_zero] using hi
  change (B 1).1*(C 1).2-(B 1).2*(C 1).1=1
  linear_combination -hi'

/-- Quadratic monodromy kernel in the physical scalar fundamental states. -/
def classicalHillTracePairingKernel (q : Curve ℂ) (b : ℂ) (x : ℝ) : ℂ :=
  (classicalHillFlow q b (0,1) 1).1*(classicalHillFlow q b (1,0) x).1^2+
  ((classicalHillFlow q b (0,1) 1).2-(classicalHillFlow q b (1,0) 1).1)*
    (classicalHillFlow q b (1,0) x).1*(classicalHillFlow q b (0,1) x).1-
  (classicalHillFlow q b (1,0) 1).2*(classicalHillFlow q b (0,1) x).1^2

/-- Literal spatial derivative, without a potential-derivative hypothesis. -/
def classicalHillTracePairingKernelDx (q : Curve ℂ) (b : ℂ) (x : ℝ) : ℂ :=
  2*(classicalHillFlow q b (0,1) 1).1*
    (classicalHillFlow q b (1,0) x).1*(classicalHillFlow q b (1,0) x).2+
  ((classicalHillFlow q b (0,1) 1).2-(classicalHillFlow q b (1,0) 1).1)*
    ((classicalHillFlow q b (1,0) x).1*(classicalHillFlow q b (0,1) x).2+
      (classicalHillFlow q b (1,0) x).2*(classicalHillFlow q b (0,1) x).1)-
  2*(classicalHillFlow q b (1,0) 1).2*
    (classicalHillFlow q b (0,1) x).1*(classicalHillFlow q b (0,1) x).2

theorem hasDerivAt_classicalHillTracePairingKernel (q : Curve ℂ) (b : ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalHillTracePairingKernel q b)
      (classicalHillTracePairingKernelDx q b t) t.val := by
  have hc : HasDerivAt (fun x : ℝ => (classicalHillFlow q b (1,0) x).1)
      (classicalHillFlow q b (1,0) t).2 t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (1,0) t).fst
  have hs : HasDerivAt (fun x : ℝ => (classicalHillFlow q b (0,1) x).1)
      (classicalHillFlow q b (0,1) t).2 t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (0,1) t).fst
  convert! (((hc.pow 2).const_mul _).add ((hc.const_mul _).mul hs)).sub
    ((hs.pow 2).const_mul _) using 1
  dsimp [classicalHillTracePairingKernelDx]
  ring

/-- The cross-multiplied Dirichlet/kernel pairing, valid also when `a=b`. -/
theorem classicalHill_dirichlet_traceKernel_pairing (q : Curve ℂ) (a b : ℂ)
    (ha : (classicalHillFlow q a (0,1) 1).1=0) :
    2*(a-b)*(∫ x in (0 : ℝ)..1, (classicalHillFlow q a (0,1) x).1^2*
      classicalHillTracePairingKernelDx q b x) =
        ((classicalHillFlow q a (0,1) 1).2^2-1)*(classicalHillFlow q b (0,1) 1).1 := by
  let A := classicalHillFlow q a (0,1)
  let B := classicalHillFlow q b (1,0)
  let C := classicalHillFlow q b (0,1)
  let P (x : ℝ) := (A x).1^2*(B x).1*(B x).2
  let Q (x : ℝ) := (A x).1^2*((B x).1*(C x).2+(B x).2*(C x).1)
  let R (x : ℝ) := (A x).1^2*(C x).1*(C x).2
  have hA : Continuous A := continuous_classicalHillFlow q a (0,1)
  have hB : Continuous B := continuous_classicalHillFlow q b (1,0)
  have hC : Continuous C := continuous_classicalHillFlow q b (0,1)
  have hP : Continuous P := by dsimp [P];fun_prop
  have hQ : Continuous Q := by dsimp [Q];fun_prop
  have hR : Continuous R := by dsimp [R];fun_prop
  have he : (fun x : ℝ => (A x).1^2*classicalHillTracePairingKernelDx q b x) =
      (fun x => 2*(C 1).1*P x+((C 1).2-(B 1).1)*Q x-2*(B 1).2*R x) := by
    funext x
    dsimp [P,Q,R,B,C,classicalHillTracePairingKernelDx]
    ring
  have hp := classicalHill_dirichlet_squared_pairing_boundary q a b (1,0) ha
  have hq := classicalHill_dirichlet_mixed_pairing_boundary q a b (1,0) (0,1) ha
  have hr := classicalHill_dirichlet_squared_pairing_boundary q a b (0,1) ha
  norm_num only [Prod.fst, one_pow, zero_pow, mul_zero, sub_zero] at hp hq hr
  change 4*(a-b)*(∫ x in (0 : ℝ)..1,P x)=(A 1).2^2*(B 1).1^2-1 at hp
  change 2*(a-b)*(∫ x in (0 : ℝ)..1,Q x)=(A 1).2^2*(B 1).1*(C 1).1 at hq
  change 4*(a-b)*(∫ x in (0 : ℝ)..1,R x)=(A 1).2^2*(C 1).1^2 at hr
  have hd := classicalHillFlow_endpoint_det q b
  change (B 1).1*(C 1).2-(B 1).2*(C 1).1=1 at hd
  change 2*(a-b)*(∫ x in (0 : ℝ)..1,(A x).1^2*classicalHillTracePairingKernelDx q b x)=_
  have hPi : IntervalIntegrable (fun x => 2*(C 1).1*P x) volume 0 1 :=
    (hP.const_mul _).intervalIntegrable 0 1
  have hQi : IntervalIntegrable (fun x => ((C 1).2-(B 1).1)*Q x) volume 0 1 :=
    (hQ.const_mul _).intervalIntegrable 0 1
  have hRi : IntervalIntegrable (fun x => 2*(B 1).2*R x) volume 0 1 :=
    (hR.const_mul _).intervalIntegrable 0 1
  rw [he, intervalIntegral.integral_sub (hPi.add hQi) hRi,
    intervalIntegral.integral_add hPi hQi]
  simp only [intervalIntegral.integral_const_mul]
  change _=((A 1).2^2-1)*(C 1).1
  linear_combination (C 1).1*hp+((C 1).2-(B 1).1)*hq-(B 1).2*hr+
    (A 1).2^2*(C 1).1*hd

/-- The same boundary identity with the actual spatial `deriv` of the kernel. -/
theorem classicalHill_dirichlet_traceKernel_deriv_pairing (q : Curve ℂ) (a b : ℂ)
    (ha : (classicalHillFlow q a (0,1) 1).1=0) :
    2*(a-b)*(∫ x in (0 : ℝ)..1, (classicalHillFlow q a (0,1) x).1^2*
      deriv (classicalHillTracePairingKernel q b) x) =
        ((classicalHillFlow q a (0,1) 1).2^2-1)*(classicalHillFlow q b (0,1) 1).1 := by
  have hi : (∫ x in (0 : ℝ)..1, (classicalHillFlow q a (0,1) x).1^2*
      deriv (classicalHillTracePairingKernel q b) x) =
      ∫ x in (0 : ℝ)..1, (classicalHillFlow q a (0,1) x).1^2*
        classicalHillTracePairingKernelDx q b x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
    exact congrArg (fun z : ℂ => (classicalHillFlow q a (0,1) x).1^2*z)
      (hasDerivAt_classicalHillTracePairingKernel q b ⟨x,hx'⟩).deriv
  rw [hi]
  exact classicalHill_dirichlet_traceKernel_pairing q a b ha

/-- Off the energy diagonal, the physical spatial pairing has this exact quotient. -/
theorem classicalHill_dirichlet_traceKernel_deriv_pairing_of_ne (q : Curve ℂ) (a b : ℂ)
    (ha : (classicalHillFlow q a (0,1) 1).1=0) (hab : a≠b) :
    (∫ x in (0 : ℝ)..1, (classicalHillFlow q a (0,1) x).1^2*
      deriv (classicalHillTracePairingKernel q b) x) =
        (((classicalHillFlow q a (0,1) 1).2^2-1)*(classicalHillFlow q b (0,1) 1).1)/
          (2*(a-b)) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hab))).mpr
  simpa only [mul_comm] using classicalHill_dirichlet_traceKernel_deriv_pairing q a b ha

end NLS.KdV
