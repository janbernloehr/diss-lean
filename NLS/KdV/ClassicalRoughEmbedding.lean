import NLS.KdV.HillHminusOneSourcePrimitive
import NLS.KdV.ClassicalHighCriticalPoints
import NLS.KdV.HillHminusOneCriticalNumerators

/-! # The actual continuous interval potential inside unit-period Hminus1

The map uses physical interval Fourier classes and imposes no endpoint
matching. It preserves the actual trace, source sheet and primitive.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

private def lowerCurveCLM : Curve ℂ →L[ℂ] Curve (ℂ × ℂ) :=
  ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) 1) (ContinuousLinearMap.inr ℂ ℂ ℂ)

private def lowerSourceCLM : Curve ℂ →L[ℂ] CoeffPair 2 :=
  sourcePhysicalL2Equiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (continuousPotentialL2CLM.comp lowerCurveCLM)

/-- Actual unit-interval Fourier coefficients of a continuous scalar potential. -/
def classicalHillL2Coefficients : Curve ℂ →L[ℂ] Coeff 2 :=
  (ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2)).comp
    ((CoeffPair.toMax 2).toContinuousLinearMap.comp lowerSourceCLM)

private theorem lowerSource_fst (q : Curve ℂ) : (lowerSourceCLM q).fst = 0 := by
  apply NLS.Fourier.unitL2SynthesisEquiv.injective
  change (sourcePhysicalL2Equiv (lowerSourceCLM q)).fst = _
  rw [show sourcePhysicalL2Equiv (lowerSourceCLM q) =
      continuousPotentialL2CLM (lowerCurveCLM q) from sourcePhysicalL2Equiv.apply_symm_apply _]
  rw [map_zero]
  apply Lp.ext
  have h := continuousPotentialL2Class_representative (lowerCurveCLM q)
  filter_upwards [h,Lp.coeFn_zero (ℂ) 2 (volume.restrict (Ioc (0 : ℝ) 1))] with x hx hz
  exact (congrArg Prod.fst hx).trans (by simpa [lowerCurveCLM,LinearVolterra.extend] using hz.symm)

private theorem constantUpper_zero_source : classicalHillSourceCoefficients 0 =
    WithLp.toLp 2 ((lp.single 2 0 (-1) : Coeff 2),0) := by
  apply sourcePhysicalL2Equiv.injective
  rw [show sourcePhysicalL2Equiv (classicalHillSourceCoefficients 0) =
      continuousPotentialL2CLM (constantUpperPotential 0) from sourcePhysicalL2Equiv.apply_symm_apply _]
  rw [sourcePhysicalL2Equiv_apply]
  have he : (WithLp.toLp 2 ((lp.single 2 0 (-1) : Coeff 2),0)) =
      CoeffPair.ofFinsupp (p := 2) (Finsupp.single 0 (-1),0) := by
    apply WithLp.ofLp_injective
    apply Prod.ext <;> ext k <;> by_cases hk : k = 0 <;> simp [lp.single_apply,hk]
  rw [he,sourcePhysicalL2_ofFinsupp]
  change continuousPotentialL2Class _ = continuousPotentialL2Class _
  apply congrArg continuousPotentialL2Class
  ext t
  · change (-1 : ℂ) = NLS.Fourier.polynomial (Finsupp.single 0 (-1)) (t : ℝ)
    simp only [NLS.Fourier.polynomial,Finsupp.sum_single_index,zero_mul]
    simp [NLS.Fourier.wave]
  · change -(0 : ℂ) = NLS.Fourier.polynomial 0 (t : ℝ)
    simp [NLS.Fourier.polynomial]

/-- The literal constant-upper source contains exactly these physical coefficients. -/
theorem classicalHillSourceCoefficients_eq (q : Curve ℂ) :
    classicalHillSourceCoefficients q =
      WithLp.toLp 2 ((lp.single 2 0 (-1) : Coeff 2),-classicalHillL2Coefficients q) := by
  have hcurve : constantUpperPotential q = constantUpperPotential 0-lowerCurveCLM q := by
    ext t <;> simp [constantUpperPotential,lowerCurveCLM]
  have hsource : classicalHillSourceCoefficients q = classicalHillSourceCoefficients 0-lowerSourceCLM q := by
    rw [classicalHillSourceCoefficients,hcurve,map_sub,map_sub]
    rfl
  rw [hsource,constantUpper_zero_source]
  apply WithLp.ofLp_injective
  apply Prod.ext
  · change (lp.single 2 0 (-1) : Coeff 2)-(lowerSourceCLM q).fst = _
    rw [lowerSource_fst,sub_zero]
  · change (0 : Coeff 2)-(lowerSourceCLM q).snd = -(lowerSourceCLM q).snd
    exact zero_sub _

/-- The physical first-order realization is the existing classical coefficient potential. -/
theorem hillFirstOrderPotential_classical (q : Curve ℂ) :
    hillFirstOrderPotential (Coeff.periodDouble (classicalHillL2Coefficients q)) =
      classicalHillCoefficientPotential q := by
  change _ = periodOnePotential (classicalHillSourceCoefficients q)
  rw [classicalHillSourceCoefficients_eq,periodOnePotential_apply]
  change (lp.single 2 0 (-1),-Coeff.periodDouble (classicalHillL2Coefficients q)) =
    (Coeff.periodDouble (lp.single 2 0 (-1)),Coeff.periodDouble (-classicalHillL2Coefficients q))
  rw [periodDouble_single_zero,map_neg]

/-- The continuous interval parameter has a bounded linear realization in Hminus1. -/
def classicalHillHminusInclusion : Curve ℂ →L[ℂ] PeriodOneHminusOne :=
  periodOneL2Inclusion.comp classicalHillL2Coefficients

theorem hillHminusDiscriminant_eq_classical (q : Curve ℂ) (lambda : ℂ) :
    hillHminusDiscriminant (classicalHillHminusInclusion q) lambda = classicalHillDiscriminant q lambda := by
  obtain ⟨z,rfl⟩ := IsAlgClosed.exists_pow_nat_eq lambda (by norm_num : 0 < 2)
  rw [classicalHillHminusInclusion,ContinuousLinearMap.comp_apply,hillHminusDiscriminant_eq_hillL2,
    hillL2Discriminant_sq,hillL2FrequencyDiscriminant,hillFirstOrderPotential_classical]
  change l2Discriminant (sourcePhysicalL2 (classicalHillSourceCoefficients q)) z = _
  rw [classicalHillSourceCoefficients,sourcePhysicalL2_equiv_symm,
    continuousPotentialL2CLM_apply,l2Discriminant_of_continuous,classicalHillDiscriminant_sq]

/-- The established continuous sheets are the shared trace-family construction. -/
def classicalHillSourceFamily : TracePrimitiveFamily (Curve ℂ) where
  trace := fun t => classicalHillDiscriminant t.2 t.1
  analytic_trace := analyticOnNhd_classicalHillDiscriminant_joint
  freePrimitive := classicalHillFreePrimitive
  freeDomain := slitPlane
  isOpen_freeDomain := isOpen_slitPlane
  analytic_freePrimitive := analyticOnNhd_classicalHillFreePrimitive
  free_trace := two_cosh_classicalHillFreePrimitive

@[simp] theorem classicalHillSourceFamily_domain :
    classicalHillSourceFamily.continuationDomain = classicalHillContinuationDomain := rfl
@[simp] theorem classicalHillSourceFamily_root :
    classicalHillSourceFamily.root = classicalHillContinuedRoot := rfl
@[simp] theorem classicalHillSourceFamily_primitive :
    classicalHillSourceFamily.primitive = classicalHillContinuedPrimitive := rfl

theorem hillHminusContinuationDomain_classical_iff (lambda : ℂ) (q : Curve ℂ) :
    (lambda,classicalHillHminusInclusion q) ∈ hillHminusContinuationDomain ↔
      (lambda,q) ∈ classicalHillContinuationDomain :=
  TracePrimitiveFamily.continuationDomain_comp_iff classicalHillSourceFamily hillHminusSourceFamily
    classicalHillHminusInclusion (fun z q => hillHminusDiscriminant_eq_classical q z) rfl lambda q

theorem hillHminusContinuedRoot_eq_classical (lambda : ℂ) (q : Curve ℂ)
    (ht : (lambda,q) ∈ classicalHillContinuationDomain) :
    hillHminusContinuedRoot (lambda,classicalHillHminusInclusion q) =
      classicalHillContinuedRoot (lambda,q) :=
  TracePrimitiveFamily.root_comp classicalHillSourceFamily hillHminusSourceFamily
    classicalHillHminusInclusion (fun z q => hillHminusDiscriminant_eq_classical q z)
    (fun _ => rfl) rfl lambda q ht

theorem hillHminusContinuedPrimitive_eq_classical (lambda : ℂ) (q : Curve ℂ)
    (ht : (lambda,q) ∈ classicalHillContinuationDomain) :
    hillHminusContinuedPrimitive (lambda,classicalHillHminusInclusion q) =
      classicalHillContinuedPrimitive (lambda,q) :=
  TracePrimitiveFamily.primitive_comp classicalHillSourceFamily hillHminusSourceFamily
    classicalHillHminusInclusion (fun z q => hillHminusDiscriminant_eq_classical q z)
    (fun _ => rfl) rfl lambda q ht

theorem hillHminusDiscriminantDerivative_eq_classical (lambda : ℂ) (q : Curve ℂ) :
    hillHminusDiscriminantDerivative (lambda,classicalHillHminusInclusion q) =
      classicalHillDiscriminantDerivative (lambda,q) := by
  have he : hillHminusDiscriminant (classicalHillHminusInclusion q) = classicalHillDiscriminant q :=
    funext (hillHminusDiscriminant_eq_classical q)
  exact congrArg (fun f : ℂ → ℂ => deriv f lambda) he

/-- A finite unit-period Fourier polynomial realizes its literal coefficients. -/
theorem classicalHillL2Coefficients_polynomial (a : ℤ →₀ ℂ) :
    classicalHillL2Coefficients
      (⟨fun t => NLS.Fourier.polynomial a (t : ℝ),
        (NLS.Fourier.continuous_polynomial a).comp continuous_subtype_val⟩ : Curve ℂ) =
      Coeff.ofFinsupp a := by
  let q : Curve ℂ := ⟨fun t => NLS.Fourier.polynomial a (t : ℝ),
    (NLS.Fourier.continuous_polynomial a).comp continuous_subtype_val⟩
  have he : lowerCurveCLM q = finiteSourceCurve (0,a) := by
    ext t
    · change (0 : ℂ) = NLS.Fourier.polynomial 0 (t : ℝ)
      simp [NLS.Fourier.polynomial]
    · rfl
  have hs : lowerSourceCLM q = CoeffPair.ofFinsupp (p := 2) (0,a) := by
    apply sourcePhysicalL2Equiv.injective
    rw [show sourcePhysicalL2Equiv (lowerSourceCLM q) = continuousPotentialL2CLM (lowerCurveCLM q)
      from sourcePhysicalL2Equiv.apply_symm_apply _,sourcePhysicalL2Equiv_apply,sourcePhysicalL2_ofFinsupp,he]
    rfl
  change (lowerSourceCLM q).snd = Coeff.ofFinsupp a
  rw [hs]
  rfl

theorem denseRange_classicalHillL2Coefficients : DenseRange classicalHillL2Coefficients := by
  have hsub : range (Coeff.ofFinsupp (p := 2)) ⊆ range classicalHillL2Coefficients := by
    rintro _ ⟨a,rfl⟩
    exact ⟨⟨fun t => NLS.Fourier.polynomial a (t : ℝ),
      (NLS.Fourier.continuous_polynomial a).comp continuous_subtype_val⟩,classicalHillL2Coefficients_polynomial a⟩
  intro a
  exact closure_mono hsub (Coeff.denseRange_ofFinsupp (p := 2) (by norm_num) a)

/-- Continuous interval potentials are genuinely dense in the rough topology. -/
theorem denseRange_classicalHillHminusInclusion : DenseRange classicalHillHminusInclusion := by
  have hsub : range (WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2) ⊆ range classicalHillHminusInclusion := by
    rintro _ ⟨a,rfl⟩
    refine ⟨⟨fun t => NLS.Fourier.polynomial a (t : ℝ),
      (NLS.Fourier.continuous_polynomial a).comp continuous_subtype_val⟩,?_⟩
    rw [classicalHillHminusInclusion,ContinuousLinearMap.comp_apply,classicalHillL2Coefficients_polynomial]
    apply Subtype.ext
    funext k
    rw [periodOneL2Inclusion_apply,Coeff.ofFinsupp_apply,WeightedCoeff.ofFinsupp_apply]
  intro q
  exact closure_mono hsub (WeightedCoeff.denseRange_ofFinsupp _ 2 (by norm_num) q)

end NLS.KdV
