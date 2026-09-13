import NLS.ZakharovShabat.CentralPolynomialBounds
import NLS.ZakharovShabat.ActualRelativeProductsUniform
import NLS.ComplexAnalysis.UniformEntireFamilies

/-!
# Canonical products uniform over potential neighborhoods

Restore the bounded central correction and the free product on half-gap balls,
then use maximum modulus uniformly in the potential to fill the free lattice.
One potential neighborhood works for every compact spectral set.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Relative pair limits are bounded uniformly over bounded displacement families on half-gap balls. -/
theorem exists_bound_spectralRelativePair_family {X : Type*} (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ξ η : X → ℤ → ℂ) (hξ : ∀ x, Memℓp (fun n => ξ x n-(Real.pi : ℂ)*n) p)
    (hη : ∀ x, Memℓp (fun n => η x n-(Real.pi : ℂ)*n) p)
    (R : ℝ) (hR : 0 ≤ R)
    (hbξ : ∀ x, ‖(⟨_,hξ x⟩ : Coeff p)‖ ≤ R)
    (hbη : ∀ x, ‖(⟨_,hη x⟩ : Coeff p)‖ ≤ R) (z₀ : ℂ) (hz₀ : z₀ ∉ freeLattice) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ closedBall z₀ (freeGap z₀/2) ×ˢ (Set.univ : Set X),
      ‖spectralRelativePairProduct (ξ t.2) (η t.2) t.1‖ ≤ B := by
  obtain ⟨A,hA,hAb,_⟩ := uniformCauchySeqOn_spectralRelativeFactor_family hp hp1 ξ hξ Set.univ R hR
    (fun x _ => hbξ x) z₀ hz₀
  obtain ⟨B,hB,hBb,_⟩ := uniformCauchySeqOn_spectralRelativeFactor_family hp hp1 η hη Set.univ R hR
    (fun x _ => hbη x) z₀ hz₀
  refine ⟨A*B,mul_nonneg hA hB,fun t ht => ?_⟩
  apply le_of_tendsto (tendsto_spectralRelativePairProduct hp (ξ t.2) (η t.2) (hξ t.2) (hη t.2)
    t.1 (closedBall_half_freeGap_subset z₀ hz₀ ht.1)).norm
  filter_upwards [] with M
  rw [Finset.prod_mul_distrib, norm_mul]
  exact mul_le_mul (hAb M t ht) (hBb M t ht) (norm_nonneg _) hA

/-- Bounded actual spectral data make the intrinsic polynomials uniformly Cauchy near each nonfree point. -/
theorem uniformCauchySeqOn_normalizedCentral_halfGap {X : Type*}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : X → WeightedCoeffPair w.toWeight p)
    (N : ℕ) (ξ η : X → ℤ → ℂ)
    (hξ : ∀ x, Memℓp (fun n => ξ x n-(Real.pi : ℂ)*n) p)
    (hη : ∀ x, Memℓp (fun n => η x n-(Real.pi : ℂ)*n) p)
    (R : ℝ) (hR : 0 ≤ R)
    (hbξ : ∀ x, ‖(⟨_,hξ x⟩ : Coeff p)‖ ≤ R)
    (hbη : ∀ x, ‖(⟨_,hη x⟩ : Coeff p)‖ ≤ R)
    (hc : ∀ x, PeriodicCountingData hp (weightedBaseToPair w (φ x)) N)
    (hr : ∀ x n, N < n.natAbs → PeriodicResonantPair hp w (φ x) n (ξ x n) (η x n))
    (hfree : ∀ x n, n.natAbs ≤ N → ξ x n = (Real.pi : ℂ)*n ∧ η x n = (Real.pi : ℂ)*n)
    (z₀ : ℂ) (hz₀ : z₀ ∉ freeLattice) :
    UniformCauchySeqOn (fun (M : ℕ) (t : ℂ × X) =>
      normalizedCentralPeriodicPolynomial hp (weightedBaseToPair w (φ t.2)) M t.1)
      atTop (closedBall z₀ (freeGap z₀/2) ×ˢ Set.univ) := by
  let K := closedBall z₀ (freeGap z₀/2)
  let S : Set (ℂ × X) := K ×ˢ Set.univ
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKl : K ⊆ freeLatticeᶜ := closedBall_half_freeGap_subset z₀ hz₀
  have hrel := tendstoUniformlyOn_spectralRelativePair_family hp hp1 ξ η hξ hη Set.univ R hR
    (fun x _ => hbξ x) (fun x _ => hbη x) z₀ hz₀
  obtain ⟨B,hB,hBb⟩ := exists_bound_spectralRelativePair_family hp hp1 ξ η hξ hη R hR hbξ hbη z₀ hz₀
  have hfreeLim := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (tendstoLocallyUniformlyOn_freePeriodicFullProduct.mono (Set.subset_univ K))
  have hfreeLift := (hfreeLim.comp (Prod.fst : ℂ × X → ℂ)).mono
    (show S ⊆ Prod.fst ⁻¹' K from fun _ ht => ht.1)
  have hcont : ContinuousOn (fun z : ℂ => freeDiscriminant z^2-4) K := by
    unfold freeDiscriminant
    fun_prop
  obtain ⟨A,hAb⟩ := hK.exists_bound_of_continuousOn hcont
  have hprod := NLS.ComplexAnalysis.tendstoUniformlyOn_mul_bounded _ _ _ _ S (max A 0) B
    (le_max_right _ _) hB hfreeLift hrel
    (fun t ht => (hAb t.1 ht.1).trans (le_max_left _ _)) hBb
  let C (t : ℂ × X) := centralPeriodicPolynomial hp (weightedBaseToPair w (φ t.2)) N t.1 /
    centralFreePolynomial N t.1
  obtain ⟨D,hD,hDb⟩ := exists_bound_centralPeriodicQuotient hp N K hK hKl
  have hconst : TendstoUniformlyOn (fun _ : ℕ => C) C atTop S := by
    rw [Metric.tendstoUniformlyOn_iff]
    exact fun ε hε => Filter.Eventually.of_forall (fun _ _ _ => by simpa using hε)
  have hfull := NLS.ComplexAnalysis.tendstoUniformlyOn_mul_bounded _ _ _ _ S D (max A 0*B)
    hD (mul_nonneg (le_max_right _ _) hB) hconst hprod
    (fun t ht => hDb _ (hc t.2) t.1 ht.1) (fun t ht => by
      rw [norm_mul]
      exact mul_le_mul ((hAb t.1 ht.1).trans (le_max_left _ _)) (hBb t ht) (norm_nonneg _)
        (le_max_right _ _))
  apply (hfull.congr ?_).uniformCauchySeqOn
  filter_upwards [eventually_ge_atTop N] with M hM t ht
  exact (normalizedCentralPeriodicPolynomial_eq_relative hp w (φ t.2) N M hM (ξ t.2) (η t.2)
    (hc t.2) (hr t.2) (hfree t.2) t.1 (hKl ht.1)).symm

/-- Uniform bounded spectral data give canonical convergence on every compact spectral set. -/
theorem tendstoUniformlyOn_canonicalPeriodicProduct_family {X : Type*}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : X → WeightedCoeffPair w.toWeight p)
    (N : ℕ) (ξ η : X → ℤ → ℂ)
    (hξ : ∀ x, Memℓp (fun n => ξ x n-(Real.pi : ℂ)*n) p)
    (hη : ∀ x, Memℓp (fun n => η x n-(Real.pi : ℂ)*n) p)
    (R : ℝ) (hR : 0 ≤ R)
    (hbξ : ∀ x, ‖(⟨_,hξ x⟩ : Coeff p)‖ ≤ R)
    (hbη : ∀ x, ‖(⟨_,hη x⟩ : Coeff p)‖ ≤ R)
    (hc : ∀ x, PeriodicCountingData hp (weightedBaseToPair w (φ x)) N)
    (hr : ∀ x n, N < n.natAbs → PeriodicResonantPair hp w (φ x) n (ξ x n) (η x n))
    (hfree : ∀ x n, n.natAbs ≤ N → ξ x n = (Real.pi : ℂ)*n ∧ η x n = (Real.pi : ℂ)*n)
    (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun M (t : ℂ × X) =>
      normalizedCentralPeriodicPolynomial hp (weightedBaseToPair w (φ t.2)) M t.1)
      (fun t => canonicalPeriodicProduct hp (weightedBaseToPair w (φ t.2)) t.1)
      atTop (K ×ˢ Set.univ) := by
  let F (M : ℕ) (t : ℂ × X) := normalizedCentralPeriodicPolynomial hp (weightedBaseToPair w (φ t.2)) M t.1
  have hlocal : ∀ z ∉ freeLattice, ∃ V ∈ 𝓝 z, UniformCauchySeqOn F atTop (V ×ˢ Set.univ) := by
    intro z hz
    refine ⟨closedBall z (freeGap z/2),closedBall_mem_nhds z (half_pos (freeGap_pos hz)),?_⟩
    exact uniformCauchySeqOn_normalizedCentral_halfGap hp hp1 w φ N ξ η hξ hη R hR hbξ hbη hc hr hfree z hz
  have hC := NLS.ComplexAnalysis.uniformCauchySeqOn_compact_prod_of_countable F Set.univ
    (fun M x z => (analyticOnNhd_normalizedCentralPeriodicPolynomial hp (weightedBaseToPair w (φ x)) M z (Set.mem_univ z)).differentiableAt)
    freeLattice countable_freeLattice hlocal K hK
  exact hC.tendstoUniformlyOn_of_tendsto (fun t _ =>
    (tendstoLocallyUniformlyOn_canonicalPeriodicProduct hp hp1 (weightedBaseToPair w (φ t.2))).tendsto_at
      (Set.mem_univ t.1))

/-- One open convex potential neighborhood supports uniform canonical convergence on every spectral compact set. -/
theorem exists_uniform_canonicalPeriodicProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ U : Set (WeightedCoeffPair w.toWeight p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ K : Set ℂ, IsCompact K →
        TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × WeightedCoeffPair w.toWeight p) =>
          normalizedCentralPeriodicPolynomial hp (weightedBaseToPair w t.2) M t.1)
          (fun t => canonicalPeriodicProduct hp (weightedBaseToPair w t.2) t.1) atTop (K ×ˢ U) := by
  obtain ⟨N,_,U,ho,hconv,hφ,h0,R,hR,hdata⟩ := exists_uniform_bounded_periodicDisplacements hp hp1 w φ
  choose ξ η hξ hη hbξ hbη hfree hr hc using (fun ψ : U => hdata ψ.val ψ.property)
  refine ⟨U,ho,hconv,hφ,h0,fun K hK => ?_⟩
  apply NLS.ComplexAnalysis.tendstoUniformlyOn_prod_of_subtype
  exact tendstoUniformlyOn_canonicalPeriodicProduct_family hp hp1 w Subtype.val N ξ η hξ hη R hR
    hbξ hbη (fun ψ => hc ψ N le_rfl) hr hfree K hK

end NLS.ZakharovShabat
