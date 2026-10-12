import NLS.ZakharovShabat.L2SeparatedCharacteristics
import NLS.ZakharovShabat.ContinuousSourceAntiDiscriminantGradient

/-! # Physical L2 realization of the original source boundary characteristics

Density removes the continuous-representative hypotheses, retaining exact
normalization, the original boundary spectra, and algebraic multiplicities.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- Every Hilbert source has the exact physical separated characteristic. -/
theorem periodOneBoundaryCharacteristic_eq_l2 (b : BoundaryCondition) (φ : CoeffPair 2) (z : ℂ) :
    periodOneBoundaryCharacteristic (by simp) (by norm_num) b φ z =
      l2SeparatedCharacteristic b (sourcePhysicalL2 φ) z := by
  have hc : Continuous (fun ψ : CoeffPair 2 => (z,ψ)) := continuous_const.prodMk continuous_id
  have hF : Continuous (fun ψ : CoeffPair 2 => periodOneBoundaryCharacteristic (by simp) (by norm_num) b ψ z) := by
    have h := continuousOn_univ.mp
      (analyticOnNhd_periodOneBoundaryCharacteristic_joint (p := 2) (by simp) (by norm_num) b).continuousOn
    have hcomp := h.comp hc
    exact hcomp
  have hp : Continuous (fun ψ : CoeffPair 2 => (z,sourcePhysicalL2 ψ)) :=
    continuous_const.prodMk sourcePhysicalL2.continuous
  have hG : Continuous (fun ψ : CoeffPair 2 => l2SeparatedCharacteristic b (sourcePhysicalL2 ψ) z) := by
    have h := continuousOn_univ.mp (analyticOnNhd_l2SeparatedCharacteristic_joint b).continuousOn
    have hcomp := h.comp hp
    exact hcomp
  have he := CoeffPair.eq_of_continuous_of_finsupp (p := 2) (by simp) _ _ hF hG (fun a => by
    rw [sourcePhysicalL2_ofFinsupp,l2SeparatedCharacteristic_of_continuous]
    exact periodOneBoundaryCharacteristic_finite_eq_classical b a z)
  exact congrFun he φ

/-- The original anti-discriminant is the actual off-diagonal monodromy sum at every Hilbert source. -/
theorem sourceAntiDiscriminantCandidate_eq_l2 (φ : CoeffPair 2) (z : ℂ) :
    sourceAntiDiscriminantCandidate (by simp) (by norm_num) φ z = l2AntiDiscriminant (sourcePhysicalL2 φ) z := by
  have hc : Continuous (fun ψ : CoeffPair 2 => (z,ψ)) := continuous_const.prodMk continuous_id
  have hF : Continuous (fun ψ : CoeffPair 2 => sourceAntiDiscriminantCandidate (by simp) (by norm_num) ψ z) := by
    have h := continuousOn_univ.mp
      (analyticOnNhd_sourceAntiDiscriminantCandidate_joint (p := 2) (by simp) (by norm_num)).continuousOn
    have hcomp := h.comp hc
    exact hcomp
  have hp : Continuous (fun ψ : CoeffPair 2 => (z,sourcePhysicalL2 ψ)) :=
    continuous_const.prodMk sourcePhysicalL2.continuous
  have hG : Continuous (fun ψ : CoeffPair 2 => l2AntiDiscriminant (sourcePhysicalL2 ψ) z) := by
    have h := continuousOn_univ.mp analyticOnNhd_l2AntiDiscriminant_joint.continuousOn
    have hcomp := h.comp hp
    exact hcomp
  have he := CoeffPair.eq_of_continuous_of_finsupp (p := 2) (by simp) _ _ hF hG (fun a => by
    rw [sourcePhysicalL2_ofFinsupp,l2AntiDiscriminant_of_continuous]
    exact sourceAntiDiscriminantCandidate_finite_eq_classical a z)
  exact congrFun he φ

/-- The physical characteristic detects exactly the original source boundary spectrum. -/
theorem l2SeparatedCharacteristic_source_eq_zero_iff (b : BoundaryCondition) (φ : CoeffPair 2) (z : ℂ) :
    l2SeparatedCharacteristic b (sourcePhysicalL2 φ) z = 0 ↔
      z ∈ b.spectrum (by simp) (periodOneBoundaryPotential (by simp) (by norm_num) φ).val
        (periodOneBoundaryPotential (by simp) (by norm_num) φ).property := by
  rw [← periodOneBoundaryCharacteristic_eq_l2]
  exact periodOneBoundaryCharacteristic_eq_zero_iff (by simp) (by norm_num) b φ z

/-- The literal L2 endpoint condition is equivalent to membership in the original source boundary spectrum. -/
theorem sourceBoundarySpectrum_iff_l2_endpoint (b : BoundaryCondition) (φ : CoeffPair 2) (z : ℂ) :
    z ∈ b.spectrum (by simp) (periodOneBoundaryPotential (by simp) (by norm_num) φ).val
        (periodOneBoundaryPotential (by simp) (by norm_num) φ).property ↔
      (l2SolutionCurve (sourcePhysicalL2 φ) z (1,BoundaryCondition.extensionSign b)
        ⟨1,by constructor <;> norm_num⟩).1 = BoundaryCondition.extensionSign b*
      (l2SolutionCurve (sourcePhysicalL2 φ) z (1,BoundaryCondition.extensionSign b)
        ⟨1,by constructor <;> norm_num⟩).2 :=
  (l2SeparatedCharacteristic_source_eq_zero_iff b φ z).symm.trans
    (l2SeparatedCharacteristic_eq_zero_iff b _ z)

/-- Orders of the actual L2 characteristic zeros are the original algebraic multiplicities. -/
theorem analyticOrderAt_l2SeparatedCharacteristic_source (b : BoundaryCondition) (φ : CoeffPair 2) (z : ℂ) :
    analyticOrderAt (l2SeparatedCharacteristic b (sourcePhysicalL2 φ)) z =
      (b.algebraicMultiplicity (by simp) (periodOneBoundaryPotential (by simp) (by norm_num) φ).val
        (periodOneBoundaryPotential (by simp) (by norm_num) φ).property z : ℕ∞) := by
  have he := funext (periodOneBoundaryCharacteristic_eq_l2 b φ)
  rw [← he]
  exact analyticOrderAt_periodOneBoundaryCharacteristic (by simp) (by norm_num) b φ z

/-- A complete source boundary labeling gives the exact physical L2 characteristic product. -/
theorem l2SeparatedCharacteristic_source_eq_product (b : BoundaryCondition) (φ : CoeffPair 2)
    (N : ℕ) (ξ : ℤ → ℂ)
    (h : BoundaryRootLabeling b (by simp) (periodOneBoundaryPotential (by simp) (by norm_num) φ).val
      (periodOneBoundaryPotential (by simp) (by norm_num) φ).property N ξ) :
    l2SeparatedCharacteristic b (sourcePhysicalL2 φ) = boundaryCharacteristicProduct ξ :=
  (funext (periodOneBoundaryCharacteristic_eq_l2 b φ)).symm.trans
    (periodOneBoundaryCharacteristic_eq_product (by simp) (by norm_num) b φ N ξ h)

end NLS.ZakharovShabat
