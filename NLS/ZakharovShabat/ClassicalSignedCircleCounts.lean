import NLS.ZakharovShabat.ClassicalSignedMultiplicity
import NLS.ZakharovShabat.ContourSpectrum

/-! # Finite circular counts for the actual classical signed operators -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Metric Set
namespace NLS.ZakharovShabat

/-- The finite set of actual signed spectral values inside an open disk. -/
def enclosedClassicalSignedSpectrum (u : IntervalPairL2) (r : ℤ) (c : ℂ) (R : ℝ) : Finset ℂ :=
  (finite_classicalSignedSpectrum_inter_of_isBounded u r (K := ball c R) isBounded_ball).toFinset

@[simp] theorem mem_enclosedClassicalSignedSpectrum (u : IntervalPairL2) (r : ℤ)
    (c z : ℂ) (R : ℝ) :
    z ∈ enclosedClassicalSignedSpectrum u r c R ↔
      z ∈ classicalSignedSpectrum u r ∧ z ∈ ball c R :=
  Set.Finite.mem_toFinset _

/-- Each signed physical spectrum lies in the original period-two spectrum. -/
theorem classicalSignedSpectrum_subset_periodic (u : IntervalPairL2) (r : ℤ) :
    classicalSignedSpectrum u r ⊆
      periodicSpectrum (by simp) (periodOnePotential (sourcePhysicalL2Equiv.symm u)) := by
  rw [classicalSignedSpectrum_eq]
  have h := sourceParitySpectrum_subset_full (by simp)
    (periodOnePair (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _) r
  rw [sourceResolventSet_eq] at h
  exact h

/-- Counting actual physical Jordan-chain dimensions in a disk agrees with the
original parity count in the same disk, including parameters of multiplicity zero. -/
theorem sum_enclosedClassicalSignedSpectrum_eq (u : IntervalPairL2) (r : ℤ) (c : ℂ) (R : ℝ) :
    (∑ z ∈ enclosedClassicalSignedSpectrum u r c R, classicalSignedAlgebraicMultiplicity u r z) =
      ∑ z ∈ enclosedPeriodicSpectrum (by simp)
        (periodOnePotential (sourcePhysicalL2Equiv.symm u)) c R,
        parityAlgebraicMultiplicity (by simp)
          (periodOnePotential (sourcePhysicalL2Equiv.symm u)) r z := by
  classical
  have hsub : enclosedClassicalSignedSpectrum u r c R ⊆
      enclosedPeriodicSpectrum (by simp) (periodOnePotential (sourcePhysicalL2Equiv.symm u)) c R := by
    intro z hz
    rw [mem_enclosedClassicalSignedSpectrum] at hz
    exact (mem_enclosedPeriodicSpectrum _ _ _ _ _).mpr
      ⟨classicalSignedSpectrum_subset_periodic u r hz.1,hz.2⟩
  calc
    _ = ∑ z ∈ enclosedPeriodicSpectrum (by simp)
        (periodOnePotential (sourcePhysicalL2Equiv.symm u)) c R,
        classicalSignedAlgebraicMultiplicity u r z := by
      apply Finset.sum_subset hsub
      intro z hz hn
      apply Nat.eq_zero_of_not_pos
      intro hpos
      apply hn
      exact (mem_enclosedClassicalSignedSpectrum _ _ _ _ _).mpr
        ⟨(classicalSignedAlgebraicMultiplicity_pos_iff _ _ _).mp hpos,
          ((mem_enclosedPeriodicSpectrum _ _ _ _ _).mp hz).2⟩
    _ = _ := Finset.sum_congr rfl (fun z _ => classicalSignedAlgebraicMultiplicity_eq u r z)

/-- A period-two resolvent circle is simultaneously free of both actual signed spectra. -/
theorem classicalSignedCircle_subset_resolvent (u : IntervalPairL2) (r : ℤ) (c : ℂ) (R : ℝ)
    (h : sphere c R ⊆ resolventSet (by simp)
      (periodOnePotential (sourcePhysicalL2Equiv.symm u))) :
    sphere c R ⊆ classicalSignedResolventSet u r := by
  intro z hz
  by_contra hn
  exact classicalSignedSpectrum_subset_periodic u r hn (h hz)

end NLS.ZakharovShabat
