import NLS.KdV.HillFreeAbelianResidue
import NLS.KdV.HillFreeAbelianProductSeparation
import NLS.KdV.HillFreeUniformDiagonalTail

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- Exact separation at the own free energy, where the omitted factor
is already absent on both sides. -/
theorem hillFreeAbelianHilbertProduct_own_separation
    (n : ℕ) (a : Coeff 2) :
    hillAbelianHilbertProduct n ((freeHillValue n : ℂ),a)=
      hillAbelianNumeratorProduct hillFreeGapRoot n (freeHillValue n : ℂ)*
        hilbertWeightedProduct (hillFreeSeparatedWeight n n) a := by
  let E : ℂ := freeHillValue n
  let f : ℕ → ℂ := hillAbelianComplexNumeratorFactor n (E,a)
  let g : ℕ → ℂ := fun j => hillAbelianNumeratorFactor hillFreeGapRoot n j E
  let v : ℕ → ℂ := fun j => 1+a ((j+1 : ℕ) : ℤ)*hillFreeSeparatedWeight n n ((j+1 : ℕ) : ℤ)
  have hf := (multipliable_hillAbelianComplexNumeratorFactors n (E,a)).hasProd
  have hg := (multipliable_hillAbelianNumeratorFactors 0 h0q h0r hillFreeGapRoot
    (hillFreeGapRoot_mem_box h0q h0r) n E).hasProd
  have hv := (multipliable_positive_hilbertWeightedFactors (hillFreeSeparatedWeight n n) a).hasProd
  have he (j : ℕ) : f j=g j*v j := by
    by_cases hj : j+1=n
    · simp only [f,g,v,hillAbelianComplexNumeratorFactor,hillAbelianNumeratorFactor,
        hillFreeSeparatedWeight_natSucc,if_pos hj,if_pos (Or.inl hj),mul_zero,add_zero,mul_one]
    · have hdiff : (freeHillValue (j+1 : ℕ) : ℂ)-(freeHillValue n : ℂ)≠0 :=
        sub_ne_zero.mpr (ofReal_injective.ne (strictMono_freeHillValue.injective.ne hj))
      simp only [f,g,v,E,hillAbelianComplexNumeratorFactor,hillAbelianNumeratorFactor,
        hillGapRootEnergyFactor,hillFreeGapRoot,hillFreeSeparatedWeight_natSucc,
        if_neg hj,if_neg (by omega : ¬(j+1=n ∨ j+1=n))]
      field_simp
      ring
  have heq : f=(fun j => g j*v j) := funext he
  change HasProd f _ at hf
  rw [heq] at hf
  have hprod := hf.unique (hg.mul hv)
  rw [←hillAbelianHilbertProduct_eq_tprod,
    ←hilbertWeightedProduct_eq_positive_tprod _ _ (hillFreeSeparatedWeight_nonpositive n n)] at hprod
  exact hprod

/-- The actual free own-gap period is the genuine separated weighted
product, with no off-diagonal scaling factor. -/
theorem hillFreeOwnHilbertPeriod_eq_product (n : ℕ) (hn : 1≤n) (a : Coeff 2) :
    hillAbelianHilbertPeriod 0 h0q h0r n n a=hilbertWeightedProduct (hillFreeSeparatedWeight n n) a := by
  have hRef : hillAbelianPsiCandidate hillFreeGapRoot n (freeHillValue n : ℂ)≠0 := by
    apply hillFreeAbelianReference_ne_zero_on_disc h0q h0r n hn
    rw [hillFreeGapCenter h0q h0r n hn]
    exact mem_closedBall_self (add_nonneg (hillRealGapContour_geometry 0 h0q h0r n hn).1
      (hillRealGapContour_geometry 0 h0q h0r n hn).2.1.le)
  rw [hillFreeAbelianHilbertPeriod_residue h0q h0r n n hn a,hillAbelianHilbertPsi,
    hillFreeAbelianHilbertProduct_own_separation h0q h0r n a]
  apply (div_eq_iff hRef).mpr
  rw [hillAbelianPsiCandidate]
  ring

/-- Free own periods approach one uniformly on compact Hilbert root sets. -/
theorem exists_hillFreeOwnHilbertPeriod_uniform_on_compact
    (K : Set (Coeff 2)) (hK : IsCompact K) (ε : ℝ) (hε : 0<ε) :
    ∃ J : ℕ, ∀ n : ℕ, 1≤n → J≤n → ∀ a∈K,
      ‖hillAbelianHilbertPeriod 0 h0q h0r n n a-1‖<ε := by
  obtain ⟨J,hJ⟩ := exists_hilbertWeightedProduct_hillFreeSeparatedWeight_uniform_on_compact K hK ε hε
  refine ⟨J,?_⟩
  intro n hn hnJ a ha
  rw [hillFreeOwnHilbertPeriod_eq_product h0q h0r n hn a]
  exact hJ n n hnJ a ha

end NLS.KdV
