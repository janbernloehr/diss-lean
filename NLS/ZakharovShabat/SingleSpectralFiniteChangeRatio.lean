import NLS.ZakharovShabat.SourceGapInterpolationProduct

/-! # Exact ratios for finitely changed spectral roots

When two displaced lattices agree off a finite set, the quotient of their
normalized entire products is exactly the finite quotient of those factors.
The proof uses the literal symmetric cutoffs, so no rearrangement of a
conditionally convergent product or normalization constant is assumed.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem singleSpectralPartialProduct_finite_change
    (ξ η : ℤ → ℂ) (s : Finset ℤ) (he : ∀ n ∉ s, ξ n = η n)
    (z : ℂ) (hz : ∀ n : ℤ, η n ≠ z) (N : ℕ)
    (hsub : s ⊆ Finset.Icc (-(N : ℤ)) N) :
    singleSpectralPartialProduct ξ z N = singleSpectralPartialProduct η z N *
      ∏ n ∈ s, (ξ n-z)/(η n-z) := by
  have hf (n : ℤ) : singleSpectralFactor ξ z n =
      singleSpectralFactor η z n * ((ξ n-z)/(η n-z)) := by
    unfold singleSpectralFactor
    field_simp [sub_ne_zero.mpr (hz n)]
  have hp : (∏ n ∈ Finset.Icc (-(N : ℤ)) N, (ξ n-z)/(η n-z)) =
      ∏ n ∈ s, (ξ n-z)/(η n-z) := by
    symm
    apply Finset.prod_subset hsub
    intro n _ hn
    rw [he n hn, div_self (sub_ne_zero.mpr (hz n))]
  simp only [singleSpectralPartialProduct, hf, Finset.prod_mul_distrib, hp, mul_assoc]

/-- Finite changes of the root sequence give the exact normalized entire-product multiplier. -/
theorem entireSingleSpectralProduct_finite_change
    (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (s : Finset ℤ) (he : ∀ n ∉ s, ξ n = η n)
    (z : ℂ) (hz : ∀ n : ℤ, η n ≠ z) :
    entireSingleSpectralProduct ξ z = entireSingleSpectralProduct η z *
      ∏ n ∈ s, (ξ n-z)/(η n-z) := by
  have hleft := (tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp ξ hξ).tendsto_at (mem_univ z)
  have hright := ((tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp η hη).tendsto_at
    (mem_univ z)).mul_const (∏ n ∈ s, (ξ n-z)/(η n-z))
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [Finset.tendsto_Icc_neg.eventually (eventually_ge_atTop s)] with N hN
  exact (singleSpectralPartialProduct_finite_change ξ η s he z hz N hN).symm

/-- Away from the denominator roots the actual quotient is a literal finite product. -/
theorem entireSingleSpectralProduct_ratio_of_finite_change
    (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (s : Finset ℤ) (he : ∀ n ∉ s, ξ n = η n)
    (z : ℂ) (hz : ∀ n : ℤ, η n ≠ z) :
    entireSingleSpectralProduct ξ z / entireSingleSpectralProduct η z =
      ∏ n ∈ s, (ξ n-z)/(η n-z) := by
  have hne : entireSingleSpectralProduct η z ≠ 0 := by
    intro h
    obtain ⟨n,hn⟩ := (entireSingleSpectralProduct_eq_zero_iff_of_lp hp η hη z).mp h
    exact hz n hn
  rw [entireSingleSpectralProduct_finite_change hp ξ η hξ hη s he z hz]
  exact mul_div_cancel_left₀ _ hne

end NLS.ZakharovShabat
