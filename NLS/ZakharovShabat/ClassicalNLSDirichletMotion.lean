import NLS.ZakharovShabat.ClassicalDiscriminantBoundaryFlow
import NLS.ZakharovShabat.ClassicalDirichletRootGradient
import NLS.ZakharovShabat.ClassicalNLSVectorField

/-! The actual physical NLS variation of the Zakharov--Shabat solutions. -/
noncomputable section
open Set Complex Filter Topology NLS.LinearVolterra
open scoped ContDiff ComplexConjugate Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The time part of the physical NLS Lax pair, acting on a vector. -/
def classicalNLSTransport (a b : ℝ → ℂ) (z : ℂ) (x : ℝ) (v : ℂ × ℂ) : ℂ × ℂ :=
  ((-2*I*z^2-I*a x*b x)*v.1+(2*I*z*a x-deriv a x)*v.2,
   (-2*I*z*b x-deriv b x)*v.1+(2*I*z^2+I*a x*b x)*v.2)

/-- The transport has matching endpoint values for smooth periodic data. -/
theorem classicalNLSTransport_endpoints (a b : ℝ → ℂ)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (z : ℂ) (v : ℂ × ℂ) :
    classicalNLSTransport a b z 1 v = classicalNLSTransport a b z 0 v := by
  have ha : a 1 = a 0 := by simpa using hpa 0
  have hb : b 1 = b 0 := by simpa using hpb 0
  have hda : deriv a 1 = deriv a 0 := by
    simpa using periodic_deriv_of_periodic a 1 hpa 0
  have hdb : deriv b 1 = deriv b 0 := by
    simpa using periodic_deriv_of_periodic b 1 hpb 0
  simp only [classicalNLSTransport, ha, hb, hda, hdb]

theorem continuous_classicalNLSTransport_solution
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    Continuous (fun x => classicalNLSTransport a b z x (classicalSolution Φ z v x)) := by
  have hda := (contDiff_infty_iff_deriv.mp ha).2.continuous
  have hdb := (contDiff_infty_iff_deriv.mp hb).2.continuous
  have hca := ha.continuous
  have hcb := hb.continuous
  have hu := continuous_classicalSolution Φ z v
  unfold classicalNLSTransport
  fun_prop

/-- Differentiating the transport produces precisely the physical NLS
potential variation, with the original cross-component Poisson signs. -/
theorem hasDerivAt_classicalNLSTransport_solution
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (Φ H : Curve (ℂ × ℂ))
    (hΦ : ∀ x : Icc (0 : ℝ) 1, Φ x = (a x,b x))
    (hH : ∀ x : Icc (0 : ℝ) 1,
      H x = ((classicalNLSVectorField a b).1 x,(classicalNLSVectorField a b).2 x))
    (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    HasDerivAt (fun x => classicalNLSTransport a b z x (classicalSolution Φ z v x))
      (classicalODECoefficient (Φ t) z
        (classicalNLSTransport a b z t (classicalSolution Φ z v t))+
        classicalPotentialVariationSource Φ H z v t) t := by
  have hda := ((contDiff_infty_iff_deriv.mp ha).1 t).hasDerivAt
  have hdb := ((contDiff_infty_iff_deriv.mp hb).1 t).hasDerivAt
  have hdda := ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp ha).2).1 t).hasDerivAt
  have hddb := ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hb).2).1 t).hasDerivAt
  have hu := hasDerivAt_classicalSolution Φ z v t
  have hu₁ := HasFDerivAt.hasDerivAt hu.fst
  have hu₂ := HasFDerivAt.hasDerivAt hu.snd
  have hd := (hasDerivAt_const (t : ℝ) (-2*I*z^2)).sub ((hda.const_mul I).mul hdb)
  have he := (hasDerivAt_const (t : ℝ) (2*I*z^2)).add ((hda.const_mul I).mul hdb)
  have hq := (hda.const_mul (2*I*z)).sub hdda
  have hr := (hdb.const_mul (-2*I*z)).sub hddb
  have h := ((hd.mul hu₁).add (hq.mul hu₂)).prodMk ((hr.mul hu₁).add (he.mul hu₂))
  convert! h using 1
  apply Prod.ext <;>
    simp only [classicalNLSTransport,classicalODECoefficient_apply,
      classicalPotentialVariationSource_apply,hΦ,hH,classicalNLSVectorField,
      classicalNLSEnergyGradient,Prod.fst_add,Prod.snd_add] <;> dsimp <;>
    ring_nf <;> simp only [I_sq] <;> ring

/-- The commutator expression is the genuine potential derivative of
each fundamental solution, not a separately defined spectral flow. -/
theorem classicalNLS_potentialVariation_eq
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (Φ H : Curve (ℂ × ℂ))
    (hΦ : ∀ x : Icc (0 : ℝ) 1, Φ x = (a x,b x))
    (hH : ∀ x : Icc (0 : ℝ) 1,
      H x = ((classicalNLSVectorField a b).1 x,(classicalNLSVectorField a b).2 x))
    (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalPotentialVariation Φ H z v t =
      classicalNLSTransport a b z t (classicalSolution Φ z v t)-
        classicalSolution Φ z (classicalNLSTransport a b z 0 v) t := by
  let R : ℝ → ℂ × ℂ := fun x =>
    classicalNLSTransport a b z x (classicalSolution Φ z v x)-
      classicalSolution Φ z (classicalNLSTransport a b z 0 v) x
  let V := classicalPotentialVariation Φ H z v
  have hc : Continuous (fun x => R x-V x) :=
    ((continuous_classicalNLSTransport_solution a b ha hb Φ z v).sub
      (continuous_classicalSolution _ _ _)).sub
      (contDiff_classicalPotentialVariation Φ H z v).continuous
  have he := classicalSolution_unique Φ z 0 (fun x => R x-V x) hc.continuousOn
    (by simp [R,V]) (by
      intro s _
      have hd := ((hasDerivAt_classicalNLSTransport_solution a b ha hb Φ H hΦ hH z v s).sub
        (hasDerivAt_classicalSolution Φ z (classicalNLSTransport a b z 0 v) s)).sub
        (hasDerivAt_classicalPotentialVariation Φ H z v s)
      convert! hd using 1
      apply Prod.ext <;>
        simp only [classicalODECoefficient_apply,classicalPotentialVariationSource_apply,
          Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub] <;>
        dsimp [R,V] <;> ring)
  have hz : classicalSolution Φ z 0 t = 0 := by
    rw [classicalSolution_eq_columns]
    simp
  have h := he t.property
  rw [hz] at h
  exact (sub_eq_zero.mp h).symm

/-- The matrix of the physical time transport. -/
def classicalNLSTimeMatrix (a b : ℝ → ℂ) (z : ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-2*I*z^2-I*a x*b x, 2*I*z*a x-deriv a x;
     -2*I*z*b x-deriv b x, 2*I*z^2+I*a x*b x]

/-- The actual monodromy derivative along the physical NLS field is
the endpoint commutator of its polynomial time matrix. -/
theorem fderiv_classicalMonodromy_physicalNLS_commutator
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (Φ H : Curve (ℂ × ℂ))
    (hΦ : ∀ x : Icc (0 : ℝ) 1, Φ x = (a x,b x))
    (hH : ∀ x : Icc (0 : ℝ) 1,
      H x = ((classicalNLSVectorField a b).1 x,(classicalNLSVectorField a b).2 x))
    (z : ℂ) :
    (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalMonodromy Ψ z) Φ) H =
      classicalNLSTimeMatrix a b z 0 * classicalMonodromy Φ z -
        classicalMonodromy Φ z * classicalNLSTimeMatrix a b z 0 := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hv (v : ℂ × ℂ) : classicalPotentialVariation Φ H z v 1 =
      classicalNLSTransport a b z 0 (classicalSolution Φ z v 1)-
        ((classicalNLSTransport a b z 0 v).1 • classicalSolution Φ z (1,0) 1+
         (classicalNLSTransport a b z 0 v).2 • classicalSolution Φ z (0,1) 1) := by
    rw [classicalNLS_potentialVariation_eq a b ha hb Φ H hΦ hH z v t,
      classicalNLSTransport_endpoints a b hpa hpb,
      classicalSolution_eq_columns Φ z (classicalNLSTransport a b z 0 v) t]
  have hf₁ := congrArg Prod.fst (hv (1,0))
  have hs₁ := congrArg Prod.snd (hv (1,0))
  have hf₂ := congrArg Prod.fst (hv (0,1))
  have hs₂ := congrArg Prod.snd (hv (0,1))
  simp only [classicalNLSTransport,Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul] at hf₁ hs₁ hf₂ hs₂
  rw [fderiv_classicalMonodromy_eq_potentialVariations]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sub_apply,Matrix.mul_apply,Fin.sum_univ_two,
      classicalMonodromy,classicalFundamentalMatrix,classicalNLSTimeMatrix] <;> dsimp
  · linear_combination hf₁
  · linear_combination hf₂
  · linear_combination hs₁
  · linear_combination hs₂

/-- The additional local factor in the physical NLS Dirichlet velocity. -/
def classicalNLSDirichletSpeedFactor (a b : ℝ → ℂ) (z : ℂ) : ℂ :=
  2*z^2-z*(a 0+b 0)+a 0*b 0+(deriv a 0-deriv b 0)/(2*I)

/-- At a Dirichlet zero, the physical characteristic variation is the
actual terminal anti-discriminant times the local speed factor. -/
theorem fderiv_classicalDirichletCharacteristic_physicalNLS_at_root
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (Φ H : Curve (ℂ × ℂ))
    (hΦ : ∀ x : Icc (0 : ℝ) 1, Φ x = (a x,b x))
    (hH : ∀ x : Icc (0 : ℝ) 1,
      H x = ((classicalNLSVectorField a b).1 x,(classicalNLSVectorField a b).2 x))
    (z : ℂ) (hz : classicalSeparatedCharacteristic .dirichlet Φ z = 0) :
    (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) =>
        classicalSeparatedCharacteristic .dirichlet Ψ z) Φ) H =
      classicalAntiDiscriminant Φ z * classicalNLSDirichletSpeedFactor a b z := by
  have hzero : classicalMonodromy Φ z 1 1-classicalMonodromy Φ z 0 0+
      classicalMonodromy Φ z 1 0-classicalMonodromy Φ z 0 1 = 0 := by
    simpa only [classicalSeparatedCharacteristic,BoundaryCondition.extensionSign,one_mul,
      div_eq_zero_iff,mul_eq_zero,OfNat.ofNat_ne_zero,I_ne_zero,or_self,or_false,
      add_sub_assoc] using hz
  rw [fderiv_classicalSeparatedCharacteristic_eq_monodromy,
    fderiv_classicalMonodromy_physicalNLS_commutator a b ha hb hpa hpb Φ H hΦ hH]
  simp only [Matrix.sub_apply,Matrix.mul_apply,Fin.sum_univ_two,
    classicalNLSTimeMatrix,classicalAntiDiscriminant,classicalNLSDirichletSpeedFactor,
    BoundaryCondition.extensionSign,one_mul]
  dsimp
  field_simp
  linear_combination (2*I*z*(b 0-a 0)+deriv a 0+deriv b 0)*hzero

/-- On the real form the speed factor is a real polynomial in the
Dirichlet point, with the physical endpoint derivative retained. -/
theorem classicalNLSDirichletSpeedFactor_real (a : ℝ → ℂ) (xi : ℝ) :
    classicalNLSDirichletSpeedFactor a (fun x => conj (a x)) xi =
      ((2*xi^2-2*xi*(a 0).re+‖a 0‖^2+(deriv a 0).im : ℝ) : ℂ) := by
  have hplus : a 0+conj (a 0) = ((2*(a 0).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
    ring
  have hminus : deriv a 0-conj (deriv a 0) = 2*I*((deriv a 0).im : ℂ) := by
    apply Complex.ext <;> simp
    ring
  have hprod : a 0*conj (a 0) = ((‖a 0‖^2 : ℝ) : ℂ) := by
    rw [mul_conj,Complex.normSq_eq_norm_sq]
  have hd : deriv (fun x => conj (a x)) = fun x => conj (deriv a x) := deriv.star'
  rw [classicalNLSDirichletSpeedFactor,hd,hplus,hprod,hminus]
  push_cast
  field_simp

/-- The physical NLS differential of any continuous simple Dirichlet
branch is the exact anti-discriminant formula with its speed factor. -/
theorem fderiv_classicalDirichletRoot_physicalNLS
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (Φ H : Curve (ℂ × ℂ))
    (hΦ : ∀ x : Icc (0 : ℝ) 1, Φ x = (a x,b x))
    (hH : ∀ x : Icc (0 : ℝ) 1,
      H x = ((classicalNLSVectorField a b).1 x,(classicalNLSVectorField a b).2 x))
    (μ : Curve (ℂ × ℂ) → ℂ) (hμ : ContinuousAt μ Φ)
    (hroot : ∀ᶠ Ψ in 𝓝 Φ, classicalSeparatedCharacteristic .dirichlet Ψ (μ Ψ) = 0)
    (hsimple : deriv (classicalSeparatedCharacteristic .dirichlet Φ) (μ Φ) ≠ 0) :
    (fderiv ℂ μ Φ) H =
      -(classicalAntiDiscriminant Φ (μ Φ)*classicalNLSDirichletSpeedFactor a b (μ Φ)) /
        deriv (classicalSeparatedCharacteristic .dirichlet Φ) (μ Φ) := by
  let F : ℂ × Curve (ℂ × ℂ) → ℂ := fun t => classicalSeparatedCharacteristic .dirichlet t.2 t.1
  have hF : AnalyticAt ℂ F (μ Φ,Φ) :=
    analyticOnNhd_classicalSeparatedCharacteristic_joint .dirichlet (μ Φ,Φ) (mem_univ _)
  have hμA : AnalyticAt ℂ μ Φ := by
    apply NLS.ComplexAnalysis.analyticAt_implicitRoot F μ Φ hF hμ hroot
    rw [← NLS.ComplexAnalysis.deriv_spectral_section_eq_fderiv F (μ Φ) Φ hF.differentiableAt]
    exact hsimple
  have hzero : (fun Ψ : Curve (ℂ × ℂ) => F (μ Ψ,Ψ)) =ᶠ[𝓝 Φ] (fun _ => (0 : ℂ)) := hroot
  have hchain := NLS.ComplexAnalysis.fderiv_moving_spectral_parameter F μ Φ
    hF.differentiableAt hμA.differentiableAt
  rw [hzero.fderiv_eq] at hchain
  simp only [fderiv_const_apply] at hchain
  have he := congrArg (fun L : Curve (ℂ × ℂ) →L[ℂ] ℂ => L H) hchain
  simp only [zero_apply,add_apply,smul_apply,smul_eq_mul] at he
  change 0 = (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) =>
      classicalSeparatedCharacteristic .dirichlet Ψ (μ Φ)) Φ) H+
      deriv (classicalSeparatedCharacteristic .dirichlet Φ) (μ Φ)*(fderiv ℂ μ Φ) H at he
  rw [fderiv_classicalDirichletCharacteristic_physicalNLS_at_root a b ha hb hpa hpb
    Φ H hΦ hH (μ Φ) hroot.self_of_nhds] at he
  apply (eq_div_iff hsimple).mpr
  linear_combination -he

/-- Any trajectory with the actual physical NLS tangent has this
Dirichlet velocity at a simple continuously selected root. -/
theorem hasDerivAt_classicalDirichletRoot_physicalNLS
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (γ : ℝ → Curve (ℂ × ℂ)) (H : Curve (ℂ × ℂ)) (time : ℝ)
    (hγ : HasDerivAt γ H time)
    (hΦ : ∀ x : Icc (0 : ℝ) 1, γ time x = (a x,b x))
    (hH : ∀ x : Icc (0 : ℝ) 1,
      H x = ((classicalNLSVectorField a b).1 x,(classicalNLSVectorField a b).2 x))
    (μ : Curve (ℂ × ℂ) → ℂ) (hμ : ContinuousAt μ (γ time))
    (hroot : ∀ᶠ Ψ in 𝓝 (γ time), classicalSeparatedCharacteristic .dirichlet Ψ (μ Ψ) = 0)
    (hsimple : deriv (classicalSeparatedCharacteristic .dirichlet (γ time)) (μ (γ time)) ≠ 0) :
    HasDerivAt (fun t => μ (γ t))
      (-(classicalAntiDiscriminant (γ time) (μ (γ time))*
          classicalNLSDirichletSpeedFactor a b (μ (γ time))) /
        deriv (classicalSeparatedCharacteristic .dirichlet (γ time)) (μ (γ time))) time := by
  let F : ℂ × Curve (ℂ × ℂ) → ℂ := fun t => classicalSeparatedCharacteristic .dirichlet t.2 t.1
  have hF : AnalyticAt ℂ F (μ (γ time),γ time) :=
    analyticOnNhd_classicalSeparatedCharacteristic_joint .dirichlet _ (mem_univ _)
  have hμA : AnalyticAt ℂ μ (γ time) := by
    apply NLS.ComplexAnalysis.analyticAt_implicitRoot F μ (γ time) hF hμ hroot
    rw [← NLS.ComplexAnalysis.deriv_spectral_section_eq_fderiv F (μ (γ time))
      (γ time) hF.differentiableAt]
    exact hsimple
  have h := (hμA.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt time hγ
  change HasDerivAt (fun t => μ (γ t)) ((fderiv ℂ μ (γ time)) H) time at h
  rw [fderiv_classicalDirichletRoot_physicalNLS a b ha hb hpa hpb
    (γ time) H hΦ hH μ hμ hroot hsimple] at h
  exact h

end NLS.ZakharovShabat
