import NLS.ZakharovShabat.CanonicalBoundaryCharacteristic

/-! # Free normalization of the intrinsic boundary characteristic
At zero potential both intrinsic approximants are the literal free cutoffs,
so the Dirichlet and Neumann characteristic functions are exactly sine.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal Classical
namespace NLS.ZakharovShabat.BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both free central boundary spectra contain exactly the signed central lattice points. -/
theorem centralSpectrum_zero (b : BoundaryCondition) (hp : p ≠ ⊤) (N : ℕ) :
    b.centralSpectrum hp (0 : PairSpace p) (by simp) N =
      (Finset.Icc (-(N : ℤ)) N).image (fun n : ℤ => (Real.pi : ℂ)*n) := by
  unfold centralSpectrum
  rw [centralPeriodicSpectrum_zero]
  apply Finset.filter_eq_self.mpr
  intro z hz
  obtain ⟨n,_,rfl⟩ := Finset.mem_image.mp hz
  exact b.free_index_mem_spectrum hp n

/-- The free normalized intrinsic polynomials agree with the free single-sequence cutoffs. -/
theorem normalizedCentralPolynomial_zero (b : BoundaryCondition) (hp : p ≠ ⊤) (N : ℕ) (z : ℂ) :
    b.normalizedCentralPolynomial hp (0 : PairSpace p) (by simp) N z =
      boundaryCharacteristicPartialProduct (fun n => (Real.pi : ℂ)*n) z N := by
  have he : b.centralPolynomial hp (0 : PairSpace p) (by simp) N z =
      ∏ n ∈ Finset.Icc (-(N : ℤ)) N, ((Real.pi : ℂ)*n-z) := by
    unfold centralPolynomial
    rw [b.centralSpectrum_zero,Finset.prod_image]
    · simp only [b.algebraicMultiplicity_zero,pow_one]
    · intro n _ m _ hnm
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact_mod_cast mul_left_cancel₀ hpi hnm
  simp only [normalizedCentralPolynomial,he,boundaryCharacteristicPartialProduct,
    singleSpectralFactor,Finset.prod_div_distrib,neg_div]

/-- The intrinsic characteristic has the literal source sine normalization at zero potential. -/
theorem characteristic_zero (b : BoundaryCondition) (hp : p ≠ ⊤) (z : ℂ) :
    b.characteristic hp (0 : PairSpace p) (by simp) z = Complex.sin z := by
  have hd : Memℓp (fun n : ℤ => (Real.pi : ℂ)*n-(Real.pi : ℂ)*n) p := by
    simp only [sub_self]
    exact zero_mem_ℓp'
  have ht := (tendstoLocallyUniformlyOn_boundaryCharacteristicProduct hp
    (fun n => (Real.pi : ℂ)*n) hd).tendsto_at (mem_univ z)
  simp only [characteristic,b.normalizedCentralPolynomial_zero]
  exact ht.limUnder_eq.trans (boundaryCharacteristicProduct_free z)

end NLS.ZakharovShabat.BoundaryCondition
