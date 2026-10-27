import NLS.ZakharovShabat.SourceConstantPeriodicSpectrum
import NLS.ZakharovShabat.PhysicalPeriodicSpectrum

/-! # Actual physical spectra of constant potentials and a nonreal eigenvalue -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace NLS.ZakharovShabat

/-- The physical potential used below is literally the constant pair almost everywhere. -/
theorem sourcePhysicalL2_constant_representative (a b : ℂ) :
    intervalL2Representative (sourcePhysicalL2 (sourceConstantPotential (p := 2) a b))
      =ᵐ[volume.restrict (Ioc 0 1)] (fun _ : ℝ => (a,b)) := by
  have he : sourceConstantPotential (p := 2) a b =
      CoeffPair.ofFinsupp (Finsupp.single 0 a,Finsupp.single 0 b) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext k <;>
      simp [CoeffPair.ofFinsupp,Coeff.ofFinsupp,Finsupp.single_apply,eq_comm]
  have h := sourcePhysicalL2_representative (sourceConstantPotential (p := 2) a b)
  rw [he] at h ⊢
  apply h.trans
  have hf := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2))
    (physicalBase_periodOnePotential_finite (Finsupp.single 0 a,Finsupp.single 0 b))
  filter_upwards [hf] with x hx
  simpa [BoundaryCondition.periodOnePair,NLS.Fourier.polynomial] using hx

/-- The original constant-potential equation describes the independently
defined bounded-inverse spectrum of the physical period-two operator. -/
theorem mem_physicalPeriodicSpectrum_constant_iff (a b z : ℂ) (ha : a ≠ 0) :
    z ∈ physicalPeriodicSpectrum (periodOnePair (sourceConstantPotential (p := 2) a b)) ↔
      ∃ k : ℤ, z^2 = ((Real.pi : ℂ)*k)^2+a*b := by
  rw [physicalPeriodicSpectrum_eq]
  exact mem_periodicSpectrum_sourceConstant_iff (by simp) a b z ha

/-- The same exact equation holds for the union of the two full classical
unit-interval spectra, parameterized by the actual physical L² potential. -/
theorem mem_classicalSignedSpectrum_union_constant_iff (a b z : ℂ) (ha : a ≠ 0) :
    z ∈ classicalSignedSpectrum (sourcePhysicalL2 (sourceConstantPotential (p := 2) a b)) 0 ∪
      classicalSignedSpectrum (sourcePhysicalL2 (sourceConstantPotential (p := 2) a b)) 1 ↔
      ∃ k : ℤ, z^2 = ((Real.pi : ℂ)*k)^2+a*b := by
  rw [classicalSignedSpectrum_union_sourcePhysicalL2]
  exact mem_periodicSpectrum_sourceConstant_iff (by simp) a b z ha

/-- The physical constant potential `(1,-1)` has the nonreal spectral point `i`. -/
theorem I_mem_physicalPeriodicSpectrum_constant :
    Complex.I ∈ physicalPeriodicSpectrum
      (periodOnePair (sourceConstantPotential (p := 2) 1 (-1))) := by
  apply (mem_physicalPeriodicSpectrum_constant_iff 1 (-1) Complex.I one_ne_zero).mpr
  exact ⟨0,by norm_num⟩

/-- The nonreal spectral point is an actual classical full-domain ODE eigenvalue. -/
theorem I_mem_classicalSignedEigenvalues_union_constant :
    Complex.I ∈ classicalSignedEigenvalues
      (sourcePhysicalL2 (sourceConstantPotential (p := 2) 1 (-1))) 0 ∪
      classicalSignedEigenvalues
        (sourcePhysicalL2 (sourceConstantPotential (p := 2) 1 (-1))) 1 := by
  rw [← classicalSignedSpectrum_eq_eigenvalues,← classicalSignedSpectrum_eq_eigenvalues]
  apply (mem_classicalSignedSpectrum_union_constant_iff 1 (-1) Complex.I one_ne_zero).mpr
  exact ⟨0,by norm_num⟩

/-- The explicit physical witness is not of real type. -/
theorem constant_one_neg_one_not_classicalRealType :
    ¬ IsClassicalRealType (intervalL2Representative
      (sourcePhysicalL2 (sourceConstantPotential (p := 2) 1 (-1)))) := by
  intro h
  have hh := (sourcePhysicalL2_realType_iff (sourceConstantPotential (p := 2) 1 (-1))).mp h 0
  change (sourceConstantPotential (p := 2) 1 (-1)).snd 0 =
    (starRingEnd ℂ) ((sourceConstantPotential (p := 2) 1 (-1)).fst (-0)) at hh
  norm_num at hh

/-- Both actual boundary realizations of the witness fail self-adjointness. -/
theorem classicalSignedOperator_constant_one_neg_one_not_selfAdjoint (r : ℤ) :
    ¬ IsSelfAdjoint (classicalSignedOperator
      (sourcePhysicalL2 (sourceConstantPotential (p := 2) 1 (-1))) r) :=
  fun h => constant_one_neg_one_not_classicalRealType
    ((classicalSignedOperator_isSelfAdjoint_iff _ r).mp h)

/-- The p.18 assertion that the general complex physical spectrum need not be
real has an explicit original-potential and original-operator witness. -/
theorem exists_nonreal_classicalSignedEigenvalue :
    ∃ (u : IntervalPairL2) (z : ℂ), z.im ≠ 0 ∧
      z ∈ classicalSignedEigenvalues u 0 ∪ classicalSignedEigenvalues u 1 :=
  ⟨sourcePhysicalL2 (sourceConstantPotential 1 (-1)),Complex.I,
    by simp,I_mem_classicalSignedEigenvalues_union_constant⟩

end NLS.ZakharovShabat
