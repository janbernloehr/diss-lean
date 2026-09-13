import NLS.ZakharovShabat.BoundaryJetRootEquivalence
import NLS.ZakharovShabat.ParityRootMultiplicity

/-!
# Original algebraic multiplicity from finite boundary Taylor nullities

At every finite length the boundary Taylor kernel has exactly the dimension of
the original parity root space. These nullities increase and eventually equal
the full original algebraic multiplicity. Identifying that eventual dimension
with the analytic order of the boundary determinant remains a separate step.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- Nullity of the first `N` equations of the actual boundary Taylor system. -/
def boundaryJetNullity (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) (N : ℕ) : ℕ :=
  Module.finrank ℂ (LinearMap.ker (finiteBoundaryJetMap Φ z σ N))

/-- The empty Taylor system has a zero-dimensional space of coefficient vectors. -/
@[simp] theorem boundaryJetNullity_zero (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) :
    boundaryJetNullity Φ z σ 0 = 0 := Module.finrank_zero_of_subsingleton

/-- There are at most two complex coordinates of freedom per Taylor level. -/
theorem boundaryJetNullity_le_twice (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) (N : ℕ) :
    boundaryJetNullity Φ z σ N ≤ 2*N := by
  have h := Submodule.finrank_le (LinearMap.ker (finiteBoundaryJetMap Φ z σ N))
  have hd : Module.finrank ℂ (Fin N → ℂ × ℂ) = 2*N := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_prod]
    simp [mul_comm]
  calc
    _ ≤ Module.finrank ℂ (Fin N → ℂ × ℂ) := h
    _ = _ := hd

/-- Every finite parity root subspace is finite dimensional, including at length zero. -/
theorem finiteDimensional_finiteParityRootSpace (φ : PairSpace 2) (z : ℂ) (r : ℤ) (N : ℕ) :
    FiniteDimensional ℂ ↥(periodicRootSpace (by simp) φ z N ⊓ pairParitySubspace r) := by
  let : FiniteDimensional ℂ (periodicRootSpace (by simp) φ z N) :=
    finiteDimensional_periodicRootSpace (by simp) φ z N
  exact FiniteDimensional.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)

/-- At every length, the actual boundary nullity equals the original finite parity root dimension. -/
theorem boundaryJetNullity_eq_finiteParityRootSpace (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) (N : ℕ) : boundaryJetNullity Φ z (wave r 1) N =
      Module.finrank ℂ ↥(periodicRootSpace (by simp) φ z N ⊓ pairParitySubspace r) := by
  cases N with
  | zero =>
    rw [boundaryJetNullity_zero]
    have hb : periodicRootSpace (by simp) φ z 0 ⊓ pairParitySubspace r = ⊥ := bot_inf_eq _
    rw [hb,finrank_bot]
  | succ n => exact finrank_boundaryJetKernel_eq_finiteParityRootSpace φ hφ Φ hΦ z r n

/-- Longer boundary Taylor systems have nondecreasing nullity, as do the original root spaces. -/
theorem boundaryJetNullity_monotone (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) : Monotone (boundaryJetNullity Φ z (wave r 1)) := by
  intro N M hNM
  rw [boundaryJetNullity_eq_finiteParityRootSpace φ hφ Φ hΦ,
    boundaryJetNullity_eq_finiteParityRootSpace φ hφ Φ hΦ]
  let : FiniteDimensional ℂ ↥(periodicRootSpace (by simp) φ z M ⊓ pairParitySubspace r) :=
    finiteDimensional_finiteParityRootSpace φ z r M
  exact Submodule.finrank_mono (inf_le_inf_right _ (periodicRootSpace_mono (by simp) φ z hNM))

/-- No finite boundary Taylor nullity exceeds the full original parity algebraic multiplicity. -/
theorem boundaryJetNullity_le_parityMultiplicity (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) (N : ℕ) :
    boundaryJetNullity Φ z (wave r 1) N ≤ parityAlgebraicMultiplicity (by simp) φ r z := by
  rw [boundaryJetNullity_eq_finiteParityRootSpace φ hφ Φ hΦ]
  let : FiniteDimensional ℂ ↥(periodicRootSpaceTop (by simp) φ z ⊓ pairParitySubspace r) :=
    finiteDimensional_parityRootSpace (by simp) φ r z
  exact Submodule.finrank_mono (inf_le_inf_right _ (le_iSup (periodicRootSpace (by simp) φ z) N))

/-- Once the original root space stabilizes, every larger boundary Taylor kernel has its full algebraic multiplicity. -/
theorem exists_boundaryJetNullity_eq_parityMultiplicity (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) : ∃ N : ℕ, ∀ M ≥ N,
      boundaryJetNullity Φ z (wave r 1) M = parityAlgebraicMultiplicity (by simp) φ r z := by
  obtain ⟨N,hN⟩ := exists_periodicRootSpace_eq_top (by simp) φ z
  refine ⟨N,fun M hM => ?_⟩
  rw [boundaryJetNullity_eq_finiteParityRootSpace φ hφ Φ hΦ]
  have he : periodicRootSpace (by simp) φ z M = periodicRootSpaceTop (by simp) φ z := by
    apply le_antisymm (le_iSup (periodicRootSpace (by simp) φ z) M)
    exact (le_of_eq hN.symm).trans (periodicRootSpace_mono (by simp) φ z hM)
  rw [he]
  rfl

/-- The boundary nullity sequence is eventually exactly the original parity multiplicity. -/
theorem eventually_boundaryJetNullity_eq_parityMultiplicity (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) : ∀ᶠ N : ℕ in Filter.atTop,
      boundaryJetNullity Φ z (wave r 1) N = parityAlgebraicMultiplicity (by simp) φ r z :=
  Filter.eventually_atTop.mpr (exists_boundaryJetNullity_eq_parityMultiplicity φ hφ Φ hΦ z r)

/-- A stabilized boundary nullity is uniquely determined, so any analytic determinant-order computation will recover the original multiplicity. -/
theorem parityMultiplicity_eq_of_eventually_boundaryJetNullity (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) (m : ℕ)
    (hm : ∀ᶠ N : ℕ in Filter.atTop, boundaryJetNullity Φ z (wave r 1) N = m) :
    parityAlgebraicMultiplicity (by simp) φ r z = m := by
  obtain ⟨N,hN,hM⟩ := ((eventually_boundaryJetNullity_eq_parityMultiplicity φ hφ Φ hΦ z r).and hm).exists
  exact hN.symm.trans hM

end NLS.ZakharovShabat
