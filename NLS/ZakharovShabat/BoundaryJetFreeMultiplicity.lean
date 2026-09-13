import NLS.ZakharovShabat.BoundaryJetMultiplicity

/-!
# Exact free boundary Taylor nullities at every length

For the free operator all generalized eigenvectors are ordinary eigenvectors.
The boundary Taylor nullity is therefore already the full parity multiplicity
at length one, for positive and negative Fourier indices alike.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

private theorem free_continuous_representative :
    physicalBase (0 : PairSpace 2) =ᵐ[volume.restrict (Ioc 0 1)] extend (0 : Curve (ℂ × ℂ)) := by
  have h := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (show (1 : ℝ) ≤ 2 by norm_num)) physicalBase_zero
  filter_upwards [h] with x hx
  simpa only [LinearVolterra.extend,ContinuousMap.zero_apply,Pi.zero_apply] using! hx

/-- At every positive length, the free boundary nullity is two in the Fourier parity and zero in the opposite parity. -/
theorem boundaryJetNullity_free_succ (r k : ℤ) (n : ℕ) :
    boundaryJetNullity 0 ((Real.pi : ℂ)*k) (wave r 1) (n+1) = if k % 2 = r % 2 then 2 else 0 := by
  rw [boundaryJetNullity_eq_finiteParityRootSpace 0 (Submodule.zero_mem _) 0 free_continuous_representative]
  have he : periodicRootSpace (p := 2) (by simp) 0 ((Real.pi : ℂ)*k) (n+1) =
      periodicRootSpaceTop (by simp) 0 ((Real.pi : ℂ)*k) := by
    apply le_antisymm (le_iSup (periodicRootSpace (by simp) 0 ((Real.pi : ℂ)*k)) (n+1))
    exact (le_of_eq (periodicRootSpace_one_zero_eq_top (p := 2) (by simp) k).symm).trans
      (periodicRootSpace_mono (by simp) 0 ((Real.pi : ℂ)*k) (by omega))
  rw [he]
  exact parityAlgebraicMultiplicity_zero (p := 2) (by simp) r k

/-- The complete free nullity sequence includes the empty system and every positive length. -/
theorem boundaryJetNullity_free (r k : ℤ) (N : ℕ) :
    boundaryJetNullity 0 ((Real.pi : ℂ)*k) (wave r 1) N =
      if N = 0 then 0 else if k % 2 = r % 2 then 2 else 0 := by
  cases N with
  | zero => simp
  | succ n => simpa only [Nat.succ_ne_zero,if_false] using boundaryJetNullity_free_succ r k n

end NLS.ZakharovShabat
