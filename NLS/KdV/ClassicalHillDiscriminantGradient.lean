import NLS.KdV.ClassicalHillTracePairingKernel
import NLS.ZakharovShabat.ClassicalDiscriminantGradient

/-! # The actual scalar Hill discriminant potential gradient

The constant-upper bridge identifies the proved IVP trace derivative with
its literal scalar quadratic kernel. No gradient representation is assumed.
An exact directional formula includes the Dirichlet boundary factors, and
the squared-state direction is proved to have mean zero at a Dirichlet root.
-/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem classicalHillTracePairingKernel_eq_discriminantGradient
    (q : Curve ℂ) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    classicalHillTracePairingKernel q (z^2) t =
      -(classicalDiscriminantGradient (constantUpperPotential q) z t).2 := by
  let e : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  unfold classicalHillTracePairingKernel
  rw [classicalHillFlow_eq_constantUpper q z (0,1) e,
    classicalHillFlow_eq_constantUpper q z (1,0) e,
    classicalHillFlow_eq_constantUpper q z (0,1) t,
    classicalHillFlow_eq_constantUpper q z (1,0) t]
  simp only [constantUpperInitialVector,mul_one,mul_zero,sub_zero,zero_sub]
  rw [classicalSolution_eq_columns (constantUpperPotential q) z (1,-z) e,
    classicalSolution_eq_columns (constantUpperPotential q) z (0,I) e,
    classicalSolution_eq_columns (constantUpperPotential q) z (1,-z) t,
    classicalSolution_eq_columns (constantUpperPotential q) z (0,I) t]
  simp only [constantUpperStateMap_apply,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
    smul_eq_mul,one_mul,zero_mul,zero_add,
    classicalDiscriminantGradient,classicalMonodromy,classicalFundamentalMatrix]
  dsimp [e]
  ring_nf
  simp
  ring

theorem hasFDerivAt_constantUpperPotential (q : Curve ℂ) :
    HasFDerivAt constantUpperPotential constantUpperLinearPotential q := by
  have he : constantUpperPotential =
      (fun p => constantUpperOrigin+constantUpperLinearPotential p) :=
    funext constantUpperPotential_eq_affine
  rw [he]
  simpa only [zero_add] using!
    (hasFDerivAt_const (𝕜 := ℂ) constantUpperOrigin q).add
      constantUpperLinearPotential.hasFDerivAt

theorem fderiv_classicalHillDiscriminant_eq_kernel_integral
    (q h : Curve ℂ) (b : ℂ) :
    (fderiv ℂ (fun p : Curve ℂ => classicalHillDiscriminant p b) q) h =
      ∫ x in (0 : ℝ)..1, classicalHillTracePairingKernel q b x*extend h x := by
  obtain ⟨z,rfl⟩ := IsAlgClosed.exists_pow_nat_eq b (by norm_num : 0<2)
  let Φ := constantUpperPotential q
  have ha : AnalyticAt ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalDiscriminant Ψ z) Φ :=
    (NLS.ZakharovShabat.analyticOnNhd_classicalDiscriminant_joint (z,Φ) (mem_univ _)).comp
      (f := fun Ψ : Curve (ℂ × ℂ) => (z,Ψ)) (analyticAt_const.prod analyticAt_id)
  have hd := (ha.differentiableAt.hasFDerivAt.comp q
    (hasFDerivAt_constantUpperPotential q)).fderiv
  change fderiv ℂ (fun p : Curve ℂ => classicalDiscriminant (constantUpperPotential p) z) q = _ at hd
  have he : (fun p : Curve ℂ => classicalHillDiscriminant p (z^2)) =
      (fun p => classicalDiscriminant (constantUpperPotential p) z) := by
    funext p
    exact classicalHillDiscriminant_sq p z
  rw [he,hd,ContinuousLinearMap.comp_apply,
    fderiv_classicalDiscriminant_eq_gradient_integral]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
  have hk := classicalHillTracePairingKernel_eq_discriminantGradient q z ⟨x,hx'⟩
  change _=classicalHillTracePairingKernel q (z^2) x*extend h x
  rw [hk]
  have hH : extend (constantUpperLinearPotential h) x = (0,-extend h x) := by
    simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hx']
    rfl
  dsimp only
  rw [hH]
  change (classicalDiscriminantGradient Φ z x).1*0+
    (classicalDiscriminantGradient Φ z x).2*(-extend h x) =
      -(classicalDiscriminantGradient Φ z x).2*extend h x
  ring

theorem continuous_classicalHillTracePairingKernel (q : Curve ℂ) (b : ℂ) :
    Continuous (classicalHillTracePairingKernel q b) := by
  have hc := continuous_classicalHillFlow q b (1,0)
  have hs := continuous_classicalHillFlow q b (0,1)
  unfold classicalHillTracePairingKernel
  fun_prop

theorem continuous_classicalHillTracePairingKernelDx (q : Curve ℂ) (b : ℂ) :
    Continuous (classicalHillTracePairingKernelDx q b) := by
  have hc := continuous_classicalHillFlow q b (1,0)
  have hs := continuous_classicalHillFlow q b (0,1)
  unfold classicalHillTracePairingKernelDx
  fun_prop

/-- The actual spatial derivative of the squared Dirichlet solution. -/
def classicalHillDirichletSquaredDirection (q : Curve ℂ) (a : ℂ) : Curve ℂ where
  toFun t := 2*(classicalHillFlow q a (0,1) t).1*(classicalHillFlow q a (0,1) t).2
  continuous_toFun := by
    have hA : Continuous (fun t : Icc (0 : ℝ) 1 => classicalHillFlow q a (0,1) t) :=
      (continuous_classicalHillFlow q a (0,1)).comp continuous_subtype_val
    fun_prop

theorem fderiv_classicalHillDiscriminant_dirichletSquaredDirection
    (q : Curve ℂ) (a b : ℂ) (ha : (classicalHillFlow q a (0,1) 1).1=0) :
    2*(a-b)*((fderiv ℂ (fun p : Curve ℂ => classicalHillDiscriminant p b) q)
      (classicalHillDirichletSquaredDirection q a)) =
        -(((classicalHillFlow q a (0,1) 1).2^2-1)*(classicalHillFlow q b (0,1) 1).1) := by
  let A := classicalHillFlow q a (0,1)
  let H (x : ℝ) := 2*(A x).1*(A x).2
  let g := classicalHillTracePairingKernel q b
  let dg := classicalHillTracePairingKernelDx q b
  have hA : Continuous A := continuous_classicalHillFlow q a (0,1)
  have hH : Continuous H := by dsimp [H];fun_prop
  have hg : Continuous g := continuous_classicalHillTracePairingKernel q b
  have hdg : Continuous dg := continuous_classicalHillTracePairingKernelDx q b
  have hdA (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => (A x).1^2) (H t) t.val := by
    have hf : HasDerivAt (fun x : ℝ => (A x).1) (A t).2 t.val := by
      simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q a (0,1) t).fst
    convert! hf.pow 2 using 1
    dsimp [H]
    ring
  have hprod (t : Icc (0 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => (A x).1^2*g x) (H t*g t+(A t).1^2*dg t) t.val :=
    (hdA t).mul (hasDerivAt_classicalHillTracePairingKernel q b t)
  have hprodcont : Continuous (fun x : ℝ => (A x).1^2*g x) := by fun_prop
  have hleft : Continuous (fun x : ℝ => H x*g x) := hH.mul hg
  have hright : Continuous (fun x : ℝ => (A x).1^2*dg x) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
    hprodcont.continuousOn (fun x (hx : x∈Ioo (0 : ℝ) 1) => hprod ⟨x,hx.1.le,hx.2.le⟩)
    ((hleft.add hright).intervalIntegrable 0 1)
  change (∫ x in (0 : ℝ)..1, H x*g x+(A x).1^2*dg x)=_ at hi
  rw [intervalIntegral.integral_add (hleft.intervalIntegrable 0 1)
    (hright.intervalIntegrable 0 1)] at hi
  have hi' : (∫ x in (0 : ℝ)..1,H x*g x)+(∫ x in (0 : ℝ)..1,(A x).1^2*dg x)=0 := by
    simpa [A,ha,classicalHillFlow_zero] using hi
  have hf := fderiv_classicalHillDiscriminant_eq_kernel_integral q
    (classicalHillDirichletSquaredDirection q a) b
  have he : (∫ x in (0 : ℝ)..1, g x*extend (classicalHillDirichletSquaredDirection q a) x)=
      ∫ x in (0 : ℝ)..1,H x*g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x∈Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
    simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hx',
      classicalHillDirichletSquaredDirection,ContinuousMap.coe_mk]
    change g x*(2*(A x).1*(A x).2)=H x*g x
    dsimp [H]
    ring
  change _=∫ x in (0 : ℝ)..1,g x*extend (classicalHillDirichletSquaredDirection q a) x at hf
  rw [he] at hf
  have hb := classicalHill_dirichlet_traceKernel_pairing q a b ha
  change 2*(a-b)*(∫ x in (0 : ℝ)..1,(A x).1^2*dg x)=_ at hb
  linear_combination 2*(a-b)*hf+2*(a-b)*hi'-hb

theorem integral_classicalHillDirichletSquaredDirection_eq_zero
    (q : Curve ℂ) (a : ℂ) (ha : (classicalHillFlow q a (0,1) 1).1=0) :
    (∫ x in (0 : ℝ)..1, extend (classicalHillDirichletSquaredDirection q a) x)=0 := by
  let A := classicalHillFlow q a (0,1)
  have hA : Continuous A := continuous_classicalHillFlow q a (0,1)
  have hd (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => (A x).1^2)
      (extend (classicalHillDirichletSquaredDirection q a) t) t.val := by
    have hf : HasDerivAt (fun x : ℝ => (A x).1) (A t).2 t.val := by
      simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q a (0,1) t).fst
    convert! hf.pow 2 using 1
    simp only [extend_coe,classicalHillDirichletSquaredDirection,ContinuousMap.coe_mk]
    dsimp [A]
    ring
  have hc : Continuous (fun x : ℝ => (A x).1^2) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
    hc.continuousOn (fun x (hx : x∈Ioo (0 : ℝ) 1) => hd ⟨x,hx.1.le,hx.2.le⟩)
    ((continuous_extend (classicalHillDirichletSquaredDirection q a)).intervalIntegrable 0 1)
  simpa [A,ha,classicalHillFlow_zero] using hi

theorem classicalHillTracePairingKernel_endpoints (q : Curve ℂ) (b : ℂ) :
    classicalHillTracePairingKernel q b 1=classicalHillTracePairingKernel q b 0 := by
  obtain ⟨z,rfl⟩ := IsAlgClosed.exists_pow_nat_eq b (by norm_num : 0<2)
  have h0 := classicalHillTracePairingKernel_eq_discriminantGradient q z ⟨0,by norm_num⟩
  have h1 := classicalHillTracePairingKernel_eq_discriminantGradient q z ⟨1,by norm_num⟩
  exact h1.trans ((congrArg (fun v : ℂ × ℂ => -v.2)
    (classicalDiscriminantGradient_endpoints (constantUpperPotential q) z)).trans h0.symm)

end NLS.KdV
