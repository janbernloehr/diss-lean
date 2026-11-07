import NLS.KdV.SingularDirichletPhysicalRows
import NLS.KdV.SingularDirichletCharacteristicNecessity
import NLS.MKdV.QuasiHillL2StateSobolev
import NLS.FunctionalAnalysis.ClosedIntervalDerivativeCongruence

/-! # The full native Dirichlet point-eigenvalue criterion

Every independently defined AC Dirichlet state reconstructs a native zero-trace
H1 eigenvector. Shifted Miura charts give the criterion for every complex
original H-minus-one potential and every complex energy, including zero.
The assertion concerns point eigenvalues; closedness, other spectrum and
algebraic multiplicity agreement remain separate proof obligations.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat NLS.MKdV

/-- Every independent physical Dirichlet state is represented, pointwise on the
ENTIRE closed interval, by a native H1 weak eigenvector. -/
theorem exists_native_Miura_eigen_of_quasiHill_state (u : Coeff 2) (lambda : ℂ)
    (w : Curve (ℂ × ℂ)) (hw : IsQuasiHillL2DirichletState u lambda w) :
    ∃ f : UnitDirichletH1,
      singularDirichletOperator (periodOneOriginal (periodOneMiura u)) f =
        lambda • singularDirichletDomainInclusion f ∧
      ∀ t : Icc (0:ℝ) 1, (w t).1 = unitDirichletRepresentative f t.val := by
  let Y := fun x : ℝ => (extend w x).1
  let G := fun x : ℝ => (extend w x).2
  have hregs := hw.1.intervalH1 u lambda w
  have h0 : Y 0 = 0 :=
    (congrArg Prod.fst (extend_coe w ⟨0,by constructor <;> norm_num⟩)).trans hw.2.1
  have h1 : Y 1 = 0 :=
    (congrArg Prod.fst (extend_coe w ⟨1,by constructor <;> norm_num⟩)).trans hw.2.2
  obtain ⟨f, hf, _⟩ := existsUnique_unitDirichletRepresentative Y hregs.1 h0 h1
  have hYeq : EqOn Y (unitDirichletRepresentative f) (Icc (0:ℝ) 1) :=
    fun x hx => (hf x hx).symm
  have hfirst : ∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt (unitDirichletRepresentative f)
      (unitL2SynthesisEquiv u x*unitDirichletRepresentative f x+G x) x := by
    have h := ae_hasDerivAt_Ioc_congr_of_eqOn_Icc hYeq (hw.1.position_row u lambda w)
    filter_upwards [h, ae_restrict_mem measurableSet_Ioc] with x hx hxi
    change HasDerivAt (unitDirichletRepresentative f) (unitL2SynthesisEquiv u x*Y x+G x) x at hx
    rw [hYeq ⟨hxi.1.le,hxi.2⟩] at hx
    exact hx
  have hsecond : ∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt G
      (-lambda*unitDirichletRepresentative f x-unitL2SynthesisEquiv u x*G x) x := by
    filter_upwards [hw.1.quasiDerivative_row u lambda w, ae_restrict_mem measurableSet_Ioc]
      with x hx hxi
    change HasDerivAt G (-lambda*Y x-unitL2SynthesisEquiv u x*G x) x at hx
    rw [hYeq ⟨hxi.1.le,hxi.2⟩] at hx
    exact hx
  refine ⟨f, singularDirichletMiura_eigen_of_physical_rows u lambda f G
    (continuous_extend w).snd hregs.2.1 hregs.2.2 hfirst hsecond, ?_⟩
  intro t
  exact (congrArg Prod.fst (extend_coe w t)).symm.trans (hf t.val t.property).symm

/-- Every Miura characteristic zero gives a NONZERO native H1 weak eigenvector. -/
theorem exists_native_Miura_eigen_of_quasiHillL2Dirichlet_eq_zero (u : Coeff 2) (lambda : ℂ)
    (hd : quasiHillL2Dirichlet u lambda = 0) :
    ∃ f : UnitDirichletH1, f ≠ 0 ∧
      singularDirichletOperator (periodOneOriginal (periodOneMiura u)) f =
        lambda • singularDirichletDomainInclusion f := by
  obtain ⟨w, hw, t, ht⟩ := (quasiHillL2Dirichlet_eq_zero_iff_exists_eigenstate u lambda).mp hd
  obtain ⟨f, he, hpos⟩ := exists_native_Miura_eigen_of_quasiHill_state u lambda w hw
  refine ⟨f, ?_, he⟩
  intro hz
  apply ht
  rw [hpos, hz]
  change periodOneSobolevSynthesis (0 : ScalarDomain 2) (t.val : AddCircle (2:ℝ)) = 0
  rw [map_zero]
  rfl

/-- A characteristic zero gives a native weak eigenvector for EVERY complex
original H-minus-one source potential, at every complex energy including zero. -/
theorem exists_native_eigen_of_hillHminusDirichlet_eq_zero (q : PeriodOneHminusOne) (lambda : ℂ)
    (hd : hillHminusDirichlet q lambda = 0) :
    ∃ f : UnitDirichletH1, f ≠ 0 ∧
      singularDirichletOperator (periodOneOriginal q) f = lambda • singularDirichletDomainInclusion f := by
  let C := hillHminusMiuraChartAt q
  have hi := C.image q (mem_hillHminusMiuraChartAt q)
  rw [hillHminusDirichlet_eq_miura_of_shifted_image q (C.lift q) C.energyShift lambda hi] at hd
  obtain ⟨f, hf, he⟩ := exists_native_Miura_eigen_of_quasiHillL2Dirichlet_eq_zero
    (C.lift q) (lambda+C.energyShift) hd
  rw [hi, singularDirichletOperator_source_add_constant] at he
  change singularDirichletOperator (periodOneOriginal q) f+
    C.energyShift • singularDirichletDomainInclusion f =
      (lambda+C.energyShift) • singularDirichletDomainInclusion f at he
  have hh : singularDirichletOperator (periodOneOriginal q) f+
      C.energyShift • singularDirichletDomainInclusion f =
        lambda • singularDirichletDomainInclusion f+C.energyShift • singularDirichletDomainInclusion f :=
    he.trans (add_smul lambda C.energyShift (singularDirichletDomainInclusion f))
  exact ⟨f, hf, add_right_cancel hh⟩

/-- Complete all-complex point-eigenvalue criterion on the FULL native
zero-trace H1-to-H-minus-one spaces, without a supplied lift or spectral labeling. -/
theorem hillHminusDirichlet_eq_zero_iff_native_eigen (q : PeriodOneHminusOne) (lambda : ℂ) :
    hillHminusDirichlet q lambda = 0 ↔
      ∃ f : UnitDirichletH1, f ≠ 0 ∧
        singularDirichletOperator (periodOneOriginal q) f = lambda • singularDirichletDomainInclusion f := by
  constructor
  · exact exists_native_eigen_of_hillHminusDirichlet_eq_zero q lambda
  · rintro ⟨f, hf, he⟩
    exact hillHminusDirichlet_eq_zero_of_native_eigen q lambda f hf he

/-- The same exact criterion for the actual partial operator on the FULL
Dirichlet H-minus-one base with its complete zero-trace H1 domain. -/
theorem hillHminusDirichlet_eq_zero_iff_partial_eigen (q : PeriodOneHminusOne) (lambda : ℂ) :
    hillHminusDirichlet q lambda = 0 ↔
      ∃ v : (singularDirichletPartialOperator (periodOneOriginal q)).domain,
        v.val ≠ 0 ∧ singularDirichletPartialOperator (periodOneOriginal q) v = lambda • v.val := by
  constructor
  · intro hd
    obtain ⟨f, hf, he⟩ := (hillHminusDirichlet_eq_zero_iff_native_eigen q lambda).mp hd
    apply (singularDirichletPartialOperator_eigen_iff (periodOneOriginal q) lambda).mpr
    exact ⟨f, hf, (singularDirichletPencil_eq_zero_iff (periodOneOriginal q) lambda f).mpr he⟩
  · exact hillHminusDirichlet_eq_zero_of_partial_eigen q lambda

end NLS.KdV
