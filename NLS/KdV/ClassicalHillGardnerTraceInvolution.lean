import NLS.KdV.ClassicalHillDiscriminantGradient

/-! # Actual scalar Hill trace involution for the Gardner spatial pairing

The trace gradient, its spatial derivative, and its velocity quadratic
form satisfy a closed differential system. An explicit concomitant has
matching endpoints, proving trace involution without differentiating the
potential. The resulting actual trace directions have mean zero, and
every Hill discriminant has zero potential derivative along each direction.
-/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

/-- The velocity quadratic form associated to the actual trace kernel. -/
def classicalHillTracePairingKernelFlux (q : Curve ℂ) (b : ℂ) (x : ℝ) : ℂ :=
  (classicalHillFlow q b (0,1) 1).1*(classicalHillFlow q b (1,0) x).2^2+
  ((classicalHillFlow q b (0,1) 1).2-(classicalHillFlow q b (1,0) 1).1)*
    (classicalHillFlow q b (1,0) x).2*(classicalHillFlow q b (0,1) x).2-
  (classicalHillFlow q b (1,0) 1).2*(classicalHillFlow q b (0,1) x).2^2

theorem hasDerivAt_classicalHillTracePairingKernelDx (q : Curve ℂ) (b : ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalHillTracePairingKernelDx q b)
      (2*classicalHillTracePairingKernelFlux q b t+
        2*(q t-b)*classicalHillTracePairingKernel q b t) t.val := by
  have hcf : HasDerivAt (fun x : ℝ => (classicalHillFlow q b (1,0) x).1)
      (classicalHillFlow q b (1,0) t).2 t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (1,0) t).fst
  have hcg : HasDerivAt (fun x : ℝ => (classicalHillFlow q b (1,0) x).2)
      ((q t-b)*(classicalHillFlow q b (1,0) t).1) t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (1,0) t).snd
  have hsf : HasDerivAt (fun x : ℝ => (classicalHillFlow q b (0,1) x).1)
      (classicalHillFlow q b (0,1) t).2 t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (0,1) t).fst
  have hsg : HasDerivAt (fun x : ℝ => (classicalHillFlow q b (0,1) x).2)
      ((q t-b)*(classicalHillFlow q b (0,1) t).1) t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (0,1) t).snd
  convert! ((((hcf.const_mul _).mul hcg).add
    (((hcf.mul hsg).add (hcg.mul hsf)).const_mul _)).sub
      ((hsf.const_mul _).mul hsg)) using 1
  dsimp [classicalHillTracePairingKernel,classicalHillTracePairingKernelDx,
    classicalHillTracePairingKernelFlux]
  ring

theorem hasDerivAt_classicalHillTracePairingKernelFlux (q : Curve ℂ) (b : ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalHillTracePairingKernelFlux q b)
      ((q t-b)*classicalHillTracePairingKernelDx q b t) t.val := by
  have hcg : HasDerivAt (fun x : ℝ => (classicalHillFlow q b (1,0) x).2)
      ((q t-b)*(classicalHillFlow q b (1,0) t).1) t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (1,0) t).snd
  have hsg : HasDerivAt (fun x : ℝ => (classicalHillFlow q b (0,1) x).2)
      ((q t-b)*(classicalHillFlow q b (0,1) t).1) t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (0,1) t).snd
  convert! (((hcg.pow 2).const_mul _).add ((hcg.const_mul _).mul hsg)).sub
    ((hsg.pow 2).const_mul _) using 1
  dsimp [classicalHillTracePairingKernelDx,classicalHillTracePairingKernelFlux]
  ring

theorem continuous_classicalHillTracePairingKernelFlux (q : Curve ℂ) (b : ℂ) :
    Continuous (classicalHillTracePairingKernelFlux q b) := by
  have hc := continuous_classicalHillFlow q b (1,0)
  have hs := continuous_classicalHillFlow q b (0,1)
  unfold classicalHillTracePairingKernelFlux
  fun_prop

theorem classicalHillTracePairingKernelDx_endpoints (q : Curve ℂ) (b : ℂ) :
    classicalHillTracePairingKernelDx q b 1=classicalHillTracePairingKernelDx q b 0 := by
  have hd := classicalHillFlow_endpoint_det q b
  simp only [classicalHillTracePairingKernelDx,classicalHillFlow_zero]
  linear_combination
    ((classicalHillFlow q b (0,1) 1).2-(classicalHillFlow q b (1,0) 1).1)*hd

theorem classicalHillTracePairingKernelFlux_endpoints (q : Curve ℂ) (b : ℂ) :
    classicalHillTracePairingKernelFlux q b 1=
      classicalHillTracePairingKernelFlux q b 0 := by
  have hd := classicalHillFlow_endpoint_det q b
  simp only [classicalHillTracePairingKernelFlux,classicalHillFlow_zero]
  linear_combination -(classicalHillFlow q b (1,0) 1).2*hd

/-- Actual trace gradients commute for the scalar Gardner spatial pairing. -/
theorem integral_classicalHillTracePairingKernel_mul_Dx_eq_zero
    (q : Curve ℂ) (a b : ℂ) :
    (∫ x in (0 : ℝ)..1, classicalHillTracePairingKernel q a x*
      classicalHillTracePairingKernelDx q b x)=0 := by
  let g := classicalHillTracePairingKernel q
  let h := classicalHillTracePairingKernelDx q
  let j := classicalHillTracePairingKernelFlux q
  have hg (c : ℂ) : Continuous (g c) := continuous_classicalHillTracePairingKernel q c
  have hh (c : ℂ) : Continuous (h c) := continuous_classicalHillTracePairingKernelDx q c
  have hj (c : ℂ) : Continuous (j c) := continuous_classicalHillTracePairingKernelFlux q c
  have hdg (c : ℂ) (t : Icc (0 : ℝ) 1) : HasDerivAt (g c) (h c t) t.val :=
    hasDerivAt_classicalHillTracePairingKernel q c t
  have hdh (c : ℂ) (t : Icc (0 : ℝ) 1) :
      HasDerivAt (h c) (2*j c t+2*(q t-c)*g c t) t.val :=
    hasDerivAt_classicalHillTracePairingKernelDx q c t
  have hdj (c : ℂ) (t : Icc (0 : ℝ) 1) :
      HasDerivAt (j c) ((q t-c)*h c t) t.val :=
    hasDerivAt_classicalHillTracePairingKernelFlux q c t
  have heg (c : ℂ) : g c 1=g c 0 := classicalHillTracePairingKernel_endpoints q c
  have heh (c : ℂ) : h c 1=h c 0 := classicalHillTracePairingKernelDx_endpoints q c
  have hej (c : ℂ) : j c 1=j c 0 := classicalHillTracePairingKernelFlux_endpoints q c
  by_cases hab : a=b
  · subst b
    have hd (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => g a x^2)
        (2*(g a t*h a t)) t.val := by
      convert! (hdg a t).pow 2 using 1
      ring
    have hc : Continuous (fun x : ℝ => g a x^2) := (hg a).pow 2
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
      hc.continuousOn (fun x (hx : x∈Ioo (0 : ℝ) 1) => hd ⟨x,hx.1.le,hx.2.le⟩)
      ((continuous_const.mul ((hg a).mul (hh a))).intervalIntegrable 0 1)
    change (∫ x in (0 : ℝ)..1,2*(g a x*h a x))=g a 1^2-g a 0^2 at hi
    rw [intervalIntegral.integral_const_mul,heg a,sub_self] at hi
    exact (mul_eq_zero.mp hi).resolve_left (by norm_num)
  · let U (x : ℝ) := 2*g a x*j b x+2*j a x*g b x-h a x*h b x+
        2*(a-b)*g a x*g b x
    have hUd (t : Icc (0 : ℝ) 1) : HasDerivAt U
        (4*(a-b)*(g a t*h b t)) t.val := by
      convert! (((((hdg a t).const_mul _).mul (hdj b t)).add
        (((hdj a t).const_mul _).mul (hdg b t))).sub
          ((hdh a t).mul (hdh b t))).add
            (((hdg a t).const_mul _).mul (hdg b t)) using 1
      ring
    have hUc : Continuous U := by dsimp [U];fun_prop
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
      hUc.continuousOn (fun x (hx : x∈Ioo (0 : ℝ) 1) => hUd ⟨x,hx.1.le,hx.2.le⟩)
      ((continuous_const.mul ((hg a).mul (hh b))).intervalIntegrable 0 1)
    change (∫ x in (0 : ℝ)..1,4*(a-b)*(g a x*h b x))=U 1-U 0 at hi
    have he : U 1=U 0 := by dsimp [U];rw [heg a,heg b,heh a,heh b,hej a,hej b]
    rw [intervalIntegral.integral_const_mul,he,sub_self] at hi
    exact (mul_eq_zero.mp hi).resolve_left
      (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hab))

/-- The Gardner direction is the actual spatial derivative of the trace gradient. -/
def classicalHillDiscriminantGardnerDirection (q : Curve ℂ) (b : ℂ) : Curve ℂ where
  toFun t := classicalHillTracePairingKernelDx q b t
  continuous_toFun :=
    (continuous_classicalHillTracePairingKernelDx q b).comp continuous_subtype_val

theorem integral_classicalHillDiscriminantGardnerDirection_eq_zero
    (q : Curve ℂ) (b : ℂ) :
    (∫ x in (0 : ℝ)..1, extend (classicalHillDiscriminantGardnerDirection q b) x)=0 := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
    (continuous_classicalHillTracePairingKernel q b).continuousOn
    (fun x (hx : x∈Ioo (0 : ℝ) 1) =>
      hasDerivAt_classicalHillTracePairingKernel q b ⟨x,hx.1.le,hx.2.le⟩)
    ((continuous_classicalHillTracePairingKernelDx q b).intervalIntegrable 0 1)
  have he : (∫ x in (0 : ℝ)..1, extend (classicalHillDiscriminantGardnerDirection q b) x)=
      ∫ x in (0 : ℝ)..1,classicalHillTracePairingKernelDx q b x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x∈Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
    simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hx',
      classicalHillDiscriminantGardnerDirection,ContinuousMap.coe_mk]
  rw [he,hi,classicalHillTracePairingKernel_endpoints,sub_self]

/-- Every actual Hill discriminant is stationary in every trace Gardner direction. -/
theorem fderiv_classicalHillDiscriminant_gardnerDirection_eq_zero
    (q : Curve ℂ) (a b : ℂ) :
    (fderiv ℂ (fun p : Curve ℂ => classicalHillDiscriminant p a) q)
      (classicalHillDiscriminantGardnerDirection q b)=0 := by
  rw [fderiv_classicalHillDiscriminant_eq_kernel_integral]
  have he : (∫ x in (0 : ℝ)..1, classicalHillTracePairingKernel q a x*
      extend (classicalHillDiscriminantGardnerDirection q b) x)=
      ∫ x in (0 : ℝ)..1,classicalHillTracePairingKernel q a x*
        classicalHillTracePairingKernelDx q b x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x∈Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
    simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hx',
      classicalHillDiscriminantGardnerDirection,ContinuousMap.coe_mk]
  rw [he]
  exact integral_classicalHillTracePairingKernel_mul_Dx_eq_zero q a b

/-- The literal spatial-derivative Gardner pairing of the actual trace gradients vanishes. -/
theorem integral_classicalHillTracePairingKernel_mul_deriv_eq_zero
    (q : Curve ℂ) (a b : ℂ) :
    (∫ x in (0 : ℝ)..1, classicalHillTracePairingKernel q a x*
      deriv (classicalHillTracePairingKernel q b) x)=0 := by
  have he : (∫ x in (0 : ℝ)..1,classicalHillTracePairingKernel q a x*
      deriv (classicalHillTracePairingKernel q b) x)=
      ∫ x in (0 : ℝ)..1,classicalHillTracePairingKernel q a x*
        classicalHillTracePairingKernelDx q b x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x∈Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
    exact congrArg (fun v : ℂ => classicalHillTracePairingKernel q a x*v)
      (hasDerivAt_classicalHillTracePairingKernel q b ⟨x,hx'⟩).deriv
  rw [he]
  exact integral_classicalHillTracePairingKernel_mul_Dx_eq_zero q a b

end NLS.KdV
