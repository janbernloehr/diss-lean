import NLS.ZakharovShabat.ClassicalSeparatedCharacteristics
import NLS.ZakharovShabat.ClassicalParityEigenvectors
import NLS.ZakharovShabat.ClassicalIntervalEigenvalues

/-! # Actual boundary eigenvalues and the classical separated characteristic
Original coefficient eigenvectors restrict to the unique initial-value
solution of a compatible continuous potential. Their endpoint conditions
therefore force the literal separated characteristic to vanish.
-/

noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- Scalar multiplication of initial data scales the whole classical solution. -/
theorem classicalSolution_smul (Φ : Curve (ℂ × ℂ)) (z c : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSolution Φ z (c • v) t = c • classicalSolution Φ z v t := by
  rw [classicalSolution_eq_columns Φ z (c • v) t,classicalSolution_eq_columns Φ z v t]
  simp only [Prod.smul_fst,Prod.smul_snd,smul_add,smul_smul,smul_eq_mul]

/-- Any nonzero solution with both separated endpoint conditions forces the characteristic to vanish. -/
theorem classicalSeparatedCharacteristic_eq_zero_of_solution (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (hv : v ≠ 0)
    (hleft : v.1 = extensionSign b * v.2)
    (hright : (classicalSolution Φ z v 1).1 = extensionSign b * (classicalSolution Φ z v 1).2) :
    classicalSeparatedCharacteristic b Φ z = 0 := by
  have hv2 : v.2 = extensionSign b*v.1 := by rw [hleft,← mul_assoc,extensionSign_sq,one_mul]
  have hv1 : v.1 ≠ 0 := by
    intro he
    exact hv (Prod.ext he (by rw [hv2,he,mul_zero]; rfl))
  have hvEq : v = v.1 • (1,extensionSign b) := by
    apply Prod.ext
    · simp only [Prod.smul_fst,smul_eq_mul,mul_one]
    · simpa only [Prod.smul_snd,smul_eq_mul,mul_comm] using hv2
  have he : classicalSolution Φ z v 1 = v.1 • classicalSolution Φ z (1,extensionSign b) 1 :=
    (congrArg (fun w => classicalSolution Φ z w 1) hvEq).trans
      (classicalSolution_smul Φ z v.1 (1,extensionSign b) ⟨1,by constructor <;> norm_num⟩)
  apply (classicalSeparatedCharacteristic_eq_zero_iff b Φ z).mpr
  apply mul_left_cancel₀ hv1
  rw [he] at hright
  change v.1 * (classicalSolution Φ z (1,extensionSign b) 1).1 =
    extensionSign b * (v.1 * (classicalSolution Φ z (1,extensionSign b) 1).2) at hright
  exact hright.trans (by ring)

/-- The separated characteristic has exactly the nonzero classical endpoint solutions as zeros. -/
theorem classicalSeparatedCharacteristic_eq_zero_iff_exists_solution (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) : classicalSeparatedCharacteristic b Φ z = 0 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ v.1 = extensionSign b*v.2 ∧
        (classicalSolution Φ z v 1).1 = extensionSign b*(classicalSolution Φ z v 1).2 := by
  constructor
  · intro hz
    exact ⟨(1,extensionSign b),by simp,by simp,(classicalSeparatedCharacteristic_eq_zero_iff b Φ z).mp hz⟩
  · rintro ⟨v,hv,hl,hr⟩
    exact classicalSeparatedCharacteristic_eq_zero_of_solution b Φ z v hv hl hr

/-- A nonzero boundary eigenvector has nonzero initial data on the original interval. -/
theorem physicalDomain_initial_ne_zero_of_boundary_eigenvector
    (b : BoundaryCondition) (φ : PairSpace 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (a : Domain 2) (ha : a ∈ domain b) (hne : a ≠ 0)
    (z : ℂ) (he : operator (by simp) φ a = z • domainInclusion a) : physicalDomain a 0 ≠ 0 := by
  intro hz
  apply classicalIntervalRestriction_ne_zero b a ha hne
  have h := physicalDomain_eq_classicalSolution φ Φ hΦ a z he
  intro t ht
  change physicalDomain a t = 0
  rw [h ht,hz]
  exact classicalSolution_zero_initial Φ z ⟨t,ht⟩

/-- Every actual boundary eigenvalue is a zero of the compatible continuous endpoint characteristic. -/
theorem classicalSeparatedCharacteristic_eq_zero_of_mem_boundarySpectrum
    (b : BoundaryCondition) (φ : PairSpace 2) (hφ : φ ∈ dirichletSubspace) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ)
    (hz : z ∈ b.spectrum (by simp) φ hφ) : classicalSeparatedCharacteristic b Φ z = 0 := by
  obtain ⟨a,ha,hne,he⟩ := (b.mem_spectrum_iff_exists_eigenvector (by simp) φ hφ z).mp hz
  have hv := physicalDomain_initial_ne_zero_of_boundary_eigenvector b φ Φ hΦ a ha hne z he
  have hb := classicalIntervalRestriction_mem b a ha
  have hs := physicalDomain_eq_classicalSolution φ Φ hΦ a z he
  apply classicalSeparatedCharacteristic_eq_zero_of_solution b Φ z (physicalDomain a 0) hv hb.left
  have hr : (physicalDomain a 1).1 = extensionSign b*(physicalDomain a 1).2 := hb.right
  rw [hs (by constructor <;> norm_num)] at hr
  exact hr

/-- In particular, every original physical interval eigenvalue is a zero of its actual monodromy formula. -/
theorem classicalSeparatedCharacteristic_eq_zero_of_mem_classicalEigenvalues
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (z : ℂ)
    (hz : z ∈ b.classicalEigenvalues (extend Φ)) : classicalSeparatedCharacteristic b Φ z = 0 := by
  rw [b.classicalEigenvalues_eq_boundarySpectrum (extend Φ) hΦ] at hz
  exact classicalSeparatedCharacteristic_eq_zero_of_mem_boundarySpectrum b _
    (dirichletPotentialCoefficients_mem _ _) Φ
    (physicalBase_dirichletPotentialCoefficients_restrict _ _) z hz

/-- The literal characteristic zeros are exactly the original continuous-potential interval eigenvalues. -/
theorem classicalSeparatedCharacteristic_eq_zero_iff_mem_classicalEigenvalues
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (z : ℂ) :
    classicalSeparatedCharacteristic b Φ z = 0 ↔ z ∈ b.classicalEigenvalues (extend Φ) := by
  refine ⟨fun hz => ?_,classicalSeparatedCharacteristic_eq_zero_of_mem_classicalEigenvalues b Φ hΦ z⟩
  let v : ℂ × ℂ := (1,extensionSign b)
  have hc := contDiff_classicalSolution Φ z v
  have hf : HasClassicalIntervalDomain b (classicalSolution Φ z v) :=
    ⟨NLS.Fourier.hasIntervalH1Regularity_of_contDiff hc.fst,
      NLS.Fourier.hasIntervalH1Regularity_of_contDiff hc.snd,
      by simp [v],(classicalSeparatedCharacteristic_eq_zero_iff b Φ z).mp hz⟩
  refine ⟨classicalSolution Φ z v,hf,?_,?_⟩
  · intro he
    have h0 := congrArg Prod.fst (he (by constructor <;> norm_num : (0 : ℝ) ∈ Icc 0 1))
    simp only [classicalSolution_zero,v,Prod.fst_zero,Pi.zero_apply,one_ne_zero] at h0
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact physicalOperator_classicalSolution Φ z v ⟨t,⟨ht.1.le,ht.2⟩⟩

end NLS.ZakharovShabat
