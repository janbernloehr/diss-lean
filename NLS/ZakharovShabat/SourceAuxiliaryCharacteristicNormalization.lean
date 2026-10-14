import NLS.ZakharovShabat.SourceLemma9_1Auxiliary
import NLS.ZakharovShabat.ClassicalTriangularPotential

/-!
# Normalization of the auxiliary products following Lemma 9.1

The original endpoint domains give the Neumann-minus-Dirichlet
anti-discriminant. The monodromy expressions printed on p. 53 exchange
those labels. Exact finite-source and physical Hilbert identities make this
comparison explicit; a nonzero triangular potential distinguishes the two.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual auxiliary product has its classical normalization at every finite exponent. -/
theorem sourceAuxiliaryCharacteristic_finite_eq_classical (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    auxiliaryPeriodOneCharacteristic hp hp1 b (CoeffPair.ofFinsupp (p := p) a) z =
      classicalAuxiliaryCharacteristic b (finiteSourceCurve a) z := by
  rcases le_total p 2 with h | h
  · have he := congrFun (auxiliaryPeriodOneCharacteristic_exponent hp (by simp)
      hp1 (by norm_num) h b (CoeffPair.ofFinsupp (p := p) a)) z
    rw [CoeffPair.exponentInclusion_ofFinsupp] at he
    exact he.trans (auxiliaryPeriodOneCharacteristic_finite_eq_classical b a z)
  · have he := congrFun (auxiliaryPeriodOneCharacteristic_exponent (by simp) hp
      (by norm_num) hp1 h b (CoeffPair.ofFinsupp (p := 2) a)) z
    rw [CoeffPair.exponentInclusion_ofFinsupp] at he
    exact he.symm.trans (auxiliaryPeriodOneCharacteristic_finite_eq_classical b a z)

/-- The auxiliary characteristic is fixed by the ordinary pair and the actual anti-discriminant. -/
theorem sourceAuxiliaryCharacteristic_eq_ordinary (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ) :
    auxiliaryPeriodOneCharacteristic hp hp1 b φ z =
      (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z+
        periodOneBoundaryCharacteristic hp hp1 .neumann φ z)/2-
        BoundaryCondition.extensionSign b*sourceAntiDiscriminantCandidate hp hp1 φ z/2 := by
  have hc (F : ℂ × CoeffPair p → ℂ) (hF : AnalyticOnNhd ℂ F univ) :
      Continuous (fun ψ : CoeffPair p => F (z,ψ)) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact ((hF (z,ψ) (mem_univ _)).comp (f := fun η : CoeffPair p => (z,η))
      (analyticAt_const.prod analyticAt_id)).continuousAt
  have hD := hc _ (analyticOnNhd_periodOneBoundaryCharacteristic_joint hp hp1 .dirichlet)
  have hN := hc _ (analyticOnNhd_periodOneBoundaryCharacteristic_joint hp hp1 .neumann)
  have hA := hc _ (analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1)
  have hr : Continuous (fun ψ : CoeffPair p =>
      (periodOneBoundaryCharacteristic hp hp1 .dirichlet ψ z+
        periodOneBoundaryCharacteristic hp hp1 .neumann ψ z)/2-
        BoundaryCondition.extensionSign b*sourceAntiDiscriminantCandidate hp hp1 ψ z/2) :=
    ((hD.add hN).div_const 2).sub ((continuous_const.mul hA).div_const 2)
  have he := (denseRange_finiteSourcePairs hp).equalizer
    (hc _ (analyticOnNhd_auxiliaryPeriodOneCharacteristic_joint hp hp1 b)) hr (by
      funext a
      simp only [Function.comp_apply,sourceAuxiliaryCharacteristic_finite_eq_classical,
        periodOneBoundaryCharacteristic_finite_eq_classical_all,
        sourceAntiDiscriminantCandidate_finite_eq_classical_of_exponent]
      exact classicalAuxiliaryCharacteristic_eq_ordinary b (finiteSourceCurve a) z)
  exact congrFun he φ

/-- The exact physical Hilbert formula, with the signs dictated by the endpoint domains. -/
theorem sourceAuxiliaryCharacteristic_eq_l2_monodromy (b : BoundaryCondition)
    (φ : CoeffPair 2) (z : ℂ) :
    auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) b φ z =
      ((l2Monodromy (sourcePhysicalL2 φ) z) 1 1-(l2Monodromy (sourcePhysicalL2 φ) z) 0 0-
        BoundaryCondition.extensionSign b*Complex.I*
          ((l2Monodromy (sourcePhysicalL2 φ) z) 1 0+(l2Monodromy (sourcePhysicalL2 φ) z) 0 1))/(2*Complex.I) := by
  rw [sourceAuxiliaryCharacteristic_eq_ordinary,periodOneBoundaryCharacteristic_eq_l2,
    periodOneBoundaryCharacteristic_eq_l2,sourceAntiDiscriminantCandidate_eq_l2]
  simp only [l2SeparatedCharacteristic,l2AntiDiscriminant,BoundaryCondition.extensionSign,one_mul,neg_one_mul]
  field_simp
  ring

/-- The printed starred Dirichlet expression is the actual Neumann product on finite sources. -/
theorem sourceLemma9_1_printed_starredDirichlet (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    ((classicalMonodromy (finiteSourceCurve a) z) 1 1+Complex.I*(classicalMonodromy (finiteSourceCurve a) z) 1 0+
      Complex.I*(classicalMonodromy (finiteSourceCurve a) z) 0 1-(classicalMonodromy (finiteSourceCurve a) z) 0 0)/(2*Complex.I) =
      auxiliaryPeriodOneCharacteristic hp hp1 .neumann (CoeffPair.ofFinsupp (p := p) a) z := by
  rw [sourceAuxiliaryCharacteristic_finite_eq_classical]
  exact printed_starredDirichlet_eq_actualNeumann _ z

/-- The printed starred Neumann expression is the actual Dirichlet product on finite sources. -/
theorem sourceLemma9_1_printed_starredNeumann (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    ((classicalMonodromy (finiteSourceCurve a) z) 1 1-Complex.I*(classicalMonodromy (finiteSourceCurve a) z) 1 0-
      Complex.I*(classicalMonodromy (finiteSourceCurve a) z) 0 1-(classicalMonodromy (finiteSourceCurve a) z) 0 0)/(2*Complex.I) =
      auxiliaryPeriodOneCharacteristic hp hp1 .dirichlet (CoeffPair.ofFinsupp (p := p) a) z := by
  rw [sourceAuxiliaryCharacteristic_finite_eq_classical]
  exact printed_starredNeumann_eq_actualDirichlet _ z

/-- The two actual characteristics agree exactly where their anti-discriminant vanishes. -/
theorem sourceAuxiliaryCharacteristics_eq_iff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    auxiliaryPeriodOneCharacteristic hp hp1 .neumann φ z =
      auxiliaryPeriodOneCharacteristic hp hp1 .dirichlet φ z ↔
      sourceAntiDiscriminantCandidate hp hp1 φ z = 0 :=
  sub_eq_zero.symm

/-- The triangular potential's first column has no lower coupling. -/
theorem classicalSolution_triangular_first (z : ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSolution classicalTriangularPotential z (1,0) t =
      (exp (-Complex.I*z*t.val),0) := by
  have h := classicalSolution_unique classicalTriangularPotential z (1,0)
    (fun s : ℝ => (exp (-Complex.I*z*s),0)) (by fun_prop) (by simp) (by
      intro s _
      have hd := ((Complex.ofRealCLM.hasDerivAt.const_mul (-Complex.I*z)).cexp).prodMk
        (hasDerivAt_const s.val (0 : ℂ))
      convert! hd using 1
      simp only [classicalODECoefficient_apply,classicalTriangularPotential,ContinuousMap.const_apply]
      ext <;> dsimp <;> ring)
  exact (h t.property).symm

/-- A nonzero smooth source distinguishes the two starred formulas; the label swap has content. -/
theorem sourceLemma9_1_starred_labels_distinct :
    classicalAuxiliaryCharacteristic .neumann classicalTriangularPotential Complex.I ≠
      classicalAuxiliaryCharacteristic .dirichlet classicalTriangularPotential Complex.I := by
  intro he
  have hz : classicalAntiDiscriminant classicalTriangularPotential Complex.I = 0 := by
    rw [classicalAntiDiscriminant_eq_auxiliary_sub,he,sub_self]
  have hne := classicalTriangularMonodromy_upper_ne_zero Complex.I (by simp)
  apply hne
  have hfirst : (classicalSolution classicalTriangularPotential Complex.I (1,0) 1).2 = 0 :=
    congrArg Prod.snd (classicalSolution_triangular_first Complex.I ⟨1,by constructor <;> norm_num⟩)
  change (classicalSolution classicalTriangularPotential Complex.I (0,1) 1).1+
    (classicalSolution classicalTriangularPotential Complex.I (1,0) 1).2 = 0 at hz
  simpa only [hfirst,add_zero] using hz

/-- The label mismatch occurs in the actual source products at every finite p > 1. -/
theorem sourceLemma9_1_starred_labels_distinct_source (hp : p ≠ ⊤) (hp1 : 1 < p) :
    auxiliaryPeriodOneCharacteristic hp hp1 .neumann
      (CoeffPair.ofFinsupp (p := p) (Finsupp.single 0 1,0)) Complex.I ≠
    auxiliaryPeriodOneCharacteristic hp hp1 .dirichlet
      (CoeffPair.ofFinsupp (p := p) (Finsupp.single 0 1,0)) Complex.I := by
  have hf : finiteSourceCurve (Finsupp.single 0 1,0) = classicalTriangularPotential := by
    ext t <;> simp [finiteSourceCurve,BoundaryCondition.periodOnePair,NLS.Fourier.polynomial,
      NLS.Fourier.wave_zero,classicalTriangularPotential]
  simpa only [sourceAuxiliaryCharacteristic_finite_eq_classical,hf] using sourceLemma9_1_starred_labels_distinct

end NLS.ZakharovShabat
