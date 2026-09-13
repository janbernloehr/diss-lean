import NLS.ZakharovShabat.ParitySpectralProducts

/-!
# Free specialization of the perturbed parity products

The entire constructions recover the two free discriminant factors with
prefactors minus one and four. These identities check the normalization at
all spectral parameters, including the free lattice and its double roots.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- At the free sequences, a paired factor is exactly the squared free factor. -/
theorem spectralPairFactor_free (z : ℂ) (n : ℤ) :
    spectralPairFactor (fun k => (Real.pi : ℂ)*k) (fun k => (Real.pi : ℂ)*k) z n =
      freeSpectralFactor (Real.pi : ℂ) z n := by
  by_cases hn : n = 0
  · simp [spectralPairFactor, hn, pow_two]
  · simp only [spectralPairFactor, freeSpectralFactor, if_neg hn, pow_two]
    ring

/-- The free even cutoff has precisely the corrected prefactor minus one. -/
theorem evenSpectralPairCutoff_free (z : ℂ) (N : ℕ) :
    evenSpectralPairCutoff (fun k => (Real.pi : ℂ)*k) (fun k => (Real.pi : ℂ)*k) z N =
      -freeSpectralPartialProduct (2*(Real.pi : ℂ)) z N := by
  simp only [evenSpectralPairCutoff, spectralPairFactor_free,
    ← freeSpectralFactor_even, freeSpectralPartialProduct_eq_prod_Icc]

/-- The free odd cutoff is the literal antiperiodic cutoff with prefactor four. -/
theorem oddSpectralPairCutoff_free (z : ℂ) (N : ℕ) :
    oddSpectralPairCutoff (fun k => (Real.pi : ℂ)*k) (fun k => (Real.pi : ℂ)*k) z N =
      freeAntiperiodicProduct z N := by
  simp only [oddSpectralPairCutoff, spectralPairFactor_free, freeAntiperiodicProduct]

/-- The entire even product recovers the free discriminant minus two. -/
theorem evenSpectralPairProduct_free (z : ℂ) :
    evenSpectralPairProduct (fun k => (Real.pi : ℂ)*k) (fun k => (Real.pi : ℂ)*k) z =
      freeDiscriminant z-2 := by
  have hm : Memℓp (fun n : ℤ => (Real.pi : ℂ)*n-(Real.pi : ℂ)*n) 1 := by
    simpa only [sub_self] using (zero_mem_ℓp' : Memℓp (fun _ : ℤ => (0 : ℂ)) 1)
  have h := (tendstoLocallyUniformlyOn_evenSpectralPairProduct (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    _ _ hm hm).tendsto_at (Set.mem_univ z)
  simp only [evenSpectralPairCutoff_free] at h
  exact tendsto_nhds_unique h (tendsto_freePeriodOneProduct z)

/-- The entire odd product recovers the free discriminant plus two. -/
theorem oddSpectralPairProduct_free (z : ℂ) :
    oddSpectralPairProduct (fun k => (Real.pi : ℂ)*k) (fun k => (Real.pi : ℂ)*k) z =
      freeDiscriminant z+2 := by
  have hm : Memℓp (fun n : ℤ => (Real.pi : ℂ)*n-(Real.pi : ℂ)*n) 1 := by
    simpa only [sub_self] using (zero_mem_ℓp' : Memℓp (fun _ : ℤ => (0 : ℂ)) 1)
  have h := (tendstoLocallyUniformlyOn_oddSpectralPairProduct (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    _ _ hm hm).tendsto_at (Set.mem_univ z)
  simp only [oddSpectralPairCutoff_free] at h
  exact tendsto_nhds_unique h (tendsto_freeAntiperiodicProduct z)

/-- The two normalizations give compatible discriminant values at the free potential. -/
theorem paritySpectralPairProducts_free_compatible (z : ℂ) :
    evenSpectralPairProduct (fun k => (Real.pi : ℂ)*k) (fun k => (Real.pi : ℂ)*k) z+2 =
      oddSpectralPairProduct (fun k => (Real.pi : ℂ)*k) (fun k => (Real.pi : ℂ)*k) z-2 := by
  rw [evenSpectralPairProduct_free, oddSpectralPairProduct_free]
  ring

end NLS.ZakharovShabat
