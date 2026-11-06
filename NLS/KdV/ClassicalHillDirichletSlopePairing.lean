import NLS.KdV.ClassicalHillTracePairingKernel
import NLS.KdV.ClassicalHillMultipliers

/-! # The first-energy mixed boundary pairing for Dirichlet slope variation -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

/-- Boundary pairing with the product of the cosine and sine states at a
Dirichlet energy, without division by the energy difference. -/
theorem classicalHill_dirichlet_cs_squared_pairing_boundary
    (q : Curve ℂ) (a b : ℂ) (v : ℂ × ℂ)
    (ha : (classicalHillFlow q a (0,1) 1).1=0) :
    4*(a-b)*(∫ x in (0 : ℝ)..1, (classicalHillFlow q a (1,0) x).1*
      (classicalHillFlow q a (0,1) x).1*(classicalHillFlow q b v x).1*(classicalHillFlow q b v x).2)=
      -(classicalHillFlow q b v 1).1*(classicalHillFlow q b v 1).2+
        (classicalHillFlow q a (0,1) 1).2*(classicalHillFlow q a (1,0) 1).2*
          (classicalHillFlow q b v 1).1^2+v.1*v.2 := by
  let C := classicalHillFlow q a (1,0)
  let S := classicalHillFlow q a (0,1)
  let B := classicalHillFlow q b v
  let W (x : ℝ) := (C x).1*(B x).2-(C x).2*(B x).1
  let V (x : ℝ) := (S x).1*(B x).2-(S x).2*(B x).1
  let P (x : ℝ) := (C x).1*(S x).1*(B x).1*(B x).2
  let Q (x : ℝ) := ((C x).2*(S x).1+(C x).1*(S x).2)*(B x).1^2
  have hC : Continuous C := continuous_classicalHillFlow q a (1,0)
  have hS : Continuous S := continuous_classicalHillFlow q a (0,1)
  have hB : Continuous B := continuous_classicalHillFlow q b v
  have hP : Continuous P := by dsimp [P];fun_prop
  have hQ : Continuous Q := by dsimp [Q];fun_prop
  have hCf (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => (C x).1) (C t).2 t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q a (1,0) t).fst
  have hCg (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => (C x).2) ((q t-a)*(C t).1) t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q a (1,0) t).snd
  have hSf (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => (S x).1) (S t).2 t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q a (0,1) t).fst
  have hSg (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => (S x).2) ((q t-a)*(S t).1) t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q a (0,1) t).snd
  have hBf (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => (B x).1) (B t).2 t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b v t).fst
  have hBg (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => (B x).2) ((q t-b)*(B t).1) t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b v t).snd
  have hWd (t : Icc (0 : ℝ) 1) : HasDerivAt W ((a-b)*(C t).1*(B t).1) t.val := by
    convert! ((hCf t).mul (hBg t)).sub ((hCg t).mul (hBf t)) using 1
    ring
  have hVd (t : Icc (0 : ℝ) 1) : HasDerivAt V ((a-b)*(S t).1*(B t).1) t.val := by
    convert! ((hSf t).mul (hBg t)).sub ((hSg t).mul (hBf t)) using 1
    ring
  have hWVd (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => W x*V x)
      ((a-b)*(2*P t-Q t)) t.val := by
    convert! (hWd t).mul (hVd t) using 1
    dsimp [W,V,P,Q]
    ring
  have hCSd (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => (C x).1*(S x).1*(B x).1^2)
      (2*P t+Q t) t.val := by
    convert! (((hCf t).mul (hSf t)).mul ((hBf t).pow 2)) using 1
    dsimp [P,Q]
    ring
  have hWVc : Continuous (fun x : ℝ => W x*V x) := by dsimp [W,V];fun_prop
  have hCSc : Continuous (fun x : ℝ => (C x).1*(S x).1*(B x).1^2) := by fun_prop
  have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
    hWVc.continuousOn (fun x (hx : x∈Ioo (0 : ℝ) 1) => hWVd ⟨x,hx.1.le,hx.2.le⟩)
    ((continuous_const.mul ((hP.const_mul 2).sub hQ)).intervalIntegrable 0 1)
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
    hCSc.continuousOn (fun x (hx : x∈Ioo (0 : ℝ) 1) => hCSd ⟨x,hx.1.le,hx.2.le⟩)
    (((hP.const_mul 2).add hQ).intervalIntegrable 0 1)
  change (∫ x in (0 : ℝ)..1,(a-b)*(2*P x-Q x))=W 1*V 1-W 0*V 0 at h1
  change (∫ x in (0 : ℝ)..1,2*P x+Q x)=(C 1).1*(S 1).1*(B 1).1^2-(C 0).1*(S 0).1*(B 0).1^2 at h2
  simp only [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub ((hP.const_mul 2).intervalIntegrable 0 1) (hQ.intervalIntegrable 0 1),
    intervalIntegral.integral_add ((hP.const_mul 2).intervalIntegrable 0 1) (hQ.intervalIntegrable 0 1)] at h1 h2
  have hd := classicalHillFlow_endpoint_det q a
  rw [ha,mul_zero,sub_zero] at hd
  simp only [W,V,C,S,B,ha,classicalHillFlow_zero,zero_mul,one_mul,mul_zero,sub_zero,zero_sub] at h1 h2
  change 4*(a-b)*(∫ x in (0 : ℝ)..1,P x)=_
  linear_combination h1+(a-b)*h2-(classicalHillFlow q b v 1).1*(classicalHillFlow q b v 1).2*hd

/-- Polarization in the second-energy state retains the first-energy
cosine/sine product required for the actual Dirichlet slope. -/
theorem classicalHill_dirichlet_cs_mixed_pairing_boundary
    (q : Curve ℂ) (a b : ℂ) (v w : ℂ × ℂ)
    (ha : (classicalHillFlow q a (0,1) 1).1=0) :
    4*(a-b)*(∫ x in (0 : ℝ)..1, (classicalHillFlow q a (1,0) x).1*
      (classicalHillFlow q a (0,1) x).1*
        ((classicalHillFlow q b v x).1*(classicalHillFlow q b w x).2+
          (classicalHillFlow q b v x).2*(classicalHillFlow q b w x).1))=
      -(classicalHillFlow q b v 1).1*(classicalHillFlow q b w 1).2-
        (classicalHillFlow q b v 1).2*(classicalHillFlow q b w 1).1+
      2*(classicalHillFlow q a (0,1) 1).2*(classicalHillFlow q a (1,0) 1).2*
        (classicalHillFlow q b v 1).1*(classicalHillFlow q b w 1).1+v.1*w.2+v.2*w.1 := by
  let C := classicalHillFlow q a (1,0)
  let S := classicalHillFlow q a (0,1)
  let P (u : ℂ × ℂ) (x : ℝ) := (C x).1*(S x).1*(classicalHillFlow q b u x).1*(classicalHillFlow q b u x).2
  let Q (x : ℝ) := (C x).1*(S x).1*
    ((classicalHillFlow q b v x).1*(classicalHillFlow q b w x).2+
      (classicalHillFlow q b v x).2*(classicalHillFlow q b w x).1)
  have hC : Continuous C := continuous_classicalHillFlow q a (1,0)
  have hS : Continuous S := continuous_classicalHillFlow q a (0,1)
  have hB (u : ℂ × ℂ) : Continuous (classicalHillFlow q b u) := continuous_classicalHillFlow q b u
  have hP (u : ℂ × ℂ) : Continuous (P u) := by dsimp [P];fun_prop
  have hQ : Continuous Q := by dsimp [Q];fun_prop
  have heq : (∫ x in (0 : ℝ)..1,P (v+w) x)=
      (∫ x in (0 : ℝ)..1,P v x)+(∫ x in (0 : ℝ)..1,P w x)+(∫ x in (0 : ℝ)..1,Q x) := by
    calc
      _ = ∫ x in (0 : ℝ)..1, (P v x+P w x)+Q x := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x∈Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
        dsimp only [P,Q]
        rw [classicalHillFlow_add q b v w ⟨x,hx'⟩]
        change (C x).1*(S x).1*((classicalHillFlow q b v x).1+(classicalHillFlow q b w x).1)*
          ((classicalHillFlow q b v x).2+(classicalHillFlow q b w x).2)=_
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add ((hP v).intervalIntegrable 0 1 |>.add ((hP w).intervalIntegrable 0 1))
          (hQ.intervalIntegrable 0 1),intervalIntegral.integral_add ((hP v).intervalIntegrable 0 1) ((hP w).intervalIntegrable 0 1)]
  have hs := classicalHill_dirichlet_cs_squared_pairing_boundary q a b (v+w) ha
  have hv := classicalHill_dirichlet_cs_squared_pairing_boundary q a b v ha
  have hw := classicalHill_dirichlet_cs_squared_pairing_boundary q a b w ha
  change 4*(a-b)*(∫ x in (0 : ℝ)..1,P (v+w) x)=_ at hs
  rw [heq,classicalHillFlow_add q b v w ⟨1,by norm_num⟩] at hs
  change 4*(a-b)*(((∫ x in (0 : ℝ)..1,P v x)+(∫ x in (0 : ℝ)..1,P w x))+(∫ x in (0 : ℝ)..1,Q x))=
    -((classicalHillFlow q b v 1).1+(classicalHillFlow q b w 1).1)*
      ((classicalHillFlow q b v 1).2+(classicalHillFlow q b w 1).2)+
    (classicalHillFlow q a (0,1) 1).2*(classicalHillFlow q a (1,0) 1).2*
      ((classicalHillFlow q b v 1).1+(classicalHillFlow q b w 1).1)^2+(v.1+w.1)*(v.2+w.2) at hs
  change 4*(a-b)*(∫ x in (0 : ℝ)..1,Q x)=_
  linear_combination hs-hv-hw

/-- The actual trace-gradient kernel paired with the first-energy cosine/sine
product has the exact endpoint slope factor, including the energy diagonal. -/
theorem classicalHill_dirichlet_cs_traceKernel_pairing
    (q : Curve ℂ) (a b : ℂ) (ha : (classicalHillFlow q a (0,1) 1).1=0) :
    2*(a-b)*(∫ x in (0 : ℝ)..1, (classicalHillFlow q a (1,0) x).1*
      (classicalHillFlow q a (0,1) x).1*classicalHillTracePairingKernelDx q b x)=
      (classicalHillFlow q a (0,1) 1).2*(classicalHillFlow q a (1,0) 1).2*
        (classicalHillFlow q b (0,1) 1).1 := by
  let F := classicalHillFlow q a (1,0)
  let A := classicalHillFlow q a (0,1)
  let B := classicalHillFlow q b (1,0)
  let C := classicalHillFlow q b (0,1)
  let P (x : ℝ) := (F x).1*(A x).1*(B x).1*(B x).2
  let Q (x : ℝ) := (F x).1*(A x).1*((B x).1*(C x).2+(B x).2*(C x).1)
  let R (x : ℝ) := (F x).1*(A x).1*(C x).1*(C x).2
  have hF : Continuous F := continuous_classicalHillFlow q a (1,0)
  have hA : Continuous A := continuous_classicalHillFlow q a (0,1)
  have hB : Continuous B := continuous_classicalHillFlow q b (1,0)
  have hC : Continuous C := continuous_classicalHillFlow q b (0,1)
  have hP : Continuous P := by dsimp [P];fun_prop
  have hQ : Continuous Q := by dsimp [Q];fun_prop
  have hR : Continuous R := by dsimp [R];fun_prop
  have he : (fun x : ℝ => (F x).1*(A x).1*classicalHillTracePairingKernelDx q b x)=
      (fun x => 2*(C 1).1*P x+((C 1).2-(B 1).1)*Q x-2*(B 1).2*R x) := by
    funext x
    dsimp [P,Q,R,B,C,classicalHillTracePairingKernelDx]
    ring
  have hp := classicalHill_dirichlet_cs_squared_pairing_boundary q a b (1,0) ha
  have hq := classicalHill_dirichlet_cs_mixed_pairing_boundary q a b (1,0) (0,1) ha
  have hr := classicalHill_dirichlet_cs_squared_pairing_boundary q a b (0,1) ha
  norm_num only [Prod.fst,Prod.snd,mul_zero,zero_mul,one_mul,add_zero,zero_add] at hp hq hr
  change 4*(a-b)*(∫ x in (0 : ℝ)..1,P x)=-(B 1).1*(B 1).2+(A 1).2*(F 1).2*(B 1).1^2 at hp
  change 4*(a-b)*(∫ x in (0 : ℝ)..1,Q x)=
    -(B 1).1*(C 1).2-(B 1).2*(C 1).1+2*(A 1).2*(F 1).2*(B 1).1*(C 1).1+1 at hq
  change 4*(a-b)*(∫ x in (0 : ℝ)..1,R x)=-(C 1).1*(C 1).2+(A 1).2*(F 1).2*(C 1).1^2 at hr
  have hd := classicalHillFlow_endpoint_det q b
  change (B 1).1*(C 1).2-(B 1).2*(C 1).1=1 at hd
  have hPi : IntervalIntegrable (fun x => 2*(C 1).1*P x) volume 0 1 := (hP.const_mul _).intervalIntegrable 0 1
  have hQi : IntervalIntegrable (fun x => ((C 1).2-(B 1).1)*Q x) volume 0 1 := (hQ.const_mul _).intervalIntegrable 0 1
  have hRi : IntervalIntegrable (fun x => 2*(B 1).2*R x) volume 0 1 := (hR.const_mul _).intervalIntegrable 0 1
  change 2*(a-b)*(∫ x in (0 : ℝ)..1,(F x).1*(A x).1*classicalHillTracePairingKernelDx q b x)=_
  rw [he,intervalIntegral.integral_sub (hPi.add hQi) hRi,intervalIntegral.integral_add hPi hQi]
  simp only [intervalIntegral.integral_const_mul]
  change _=(A 1).2*(F 1).2*(C 1).1
  linear_combination (C 1).1*hp+(((C 1).2-(B 1).1)/2)*hq-(B 1).2*hr+
    ((A 1).2*(F 1).2*(C 1).1-((C 1).2-(B 1).1)/2)*hd

end NLS.KdV
