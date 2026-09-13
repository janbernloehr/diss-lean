import NLS.ZakharovShabat.CanonicalParityProducts

/-!
# Joint uniform convergence to intrinsic parity products

The actual root labels disappear from the limit. Uniform convergence holds
on compact spectral sets times neighborhoods in the even-supported potential
space, and hence locally uniformly in the full joint domain.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The intrinsic parity limits converge uniformly over actual weighted potential neighborhoods. -/
theorem exists_uniform_canonicalParityProducts_weighted (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ U : Set (WeightedCoeffPair w.toWeight p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ r : ℤ, r = 0 ∨ r = 1 → ∀ K : Set ℂ, IsCompact K →
        TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × WeightedCoeffPair w.toWeight p) =>
          normalizedCentralParityPolynomial hp (weightedBaseToPair w t.2) (2*M) r t.1)
          (fun t => canonicalParityProduct hp (weightedBaseToPair w t.2) r t.1) atTop
          (K ×ˢ (U ∩ {ψ | weightedBaseToPair w ψ ∈ pairParitySubspace 0})) := by
  obtain ⟨N,_,U,ho,hconv,hφ,h0,ξ,η,h,hU⟩ := exists_uniform_normalizedCentralParityProducts_joint hp hp1 w φ
  let V := {ψ : WeightedCoeffPair w.toWeight p // ψ ∈ U ∧ weightedBaseToPair w ψ ∈ pairParitySubspace 0}
  refine ⟨U,ho,hconv,hφ,h0,?_⟩
  intro r hr K hK
  apply NLS.ComplexAnalysis.tendstoUniformlyOn_prod_of_subtype
  have he (t : ℂ × V) : canonicalParityProduct hp (weightedBaseToPair w t.2.val) 0 t.1 =
      evenSpectralPairProduct (ξ t.2) (η t.2) t.1 := congrFun ((h t.2).canonicalParity_eq_products hp1).1 t.1
  have hg (t : ℂ × V) : canonicalParityProduct hp (weightedBaseToPair w t.2.val) 1 t.1 =
      oddSpectralPairProduct (ξ t.2) (η t.2) t.1 := congrFun ((h t.2).canonicalParity_eq_products hp1).2 t.1
  rcases hr with rfl | rfl
  · exact (hU K hK).1.congr_right (fun t _ => (he t).symm)
  · exact (hU K hK).2.congr_right (fun t _ => (hg t).symm)

/-- One relative open convex neighborhood works for both intrinsic parity products and every spectral compact set. -/
theorem exists_uniform_canonicalParityProducts (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) :
    ∃ U : Set (pairParitySubspace (p := p) 0), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ r : ℤ, r = 0 ∨ r = 1 → ∀ K : Set ℂ, IsCompact K →
        TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × pairParitySubspace (p := p) 0) =>
          normalizedCentralParityPolynomial hp t.2 (2*M) r t.1)
          (fun t => canonicalParityProduct hp t.2 r t.1) atTop (K ×ˢ U) := by
  let L : pairParitySubspace (p := p) 0 →L[ℂ] WeightedCoeffPair SpectralWeight.one.toWeight p :=
    unitBaseEquiv.symm.toContinuousLinearMap.comp (pairParitySubspace (p := p) 0).subtypeL
  have he (ψ : pairParitySubspace (p := p) 0) : weightedBaseToPair SpectralWeight.one (L ψ) = (ψ : PairSpace p) := by
    change weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm (ψ : PairSpace p)) = _
    rw [← unitBaseEquiv_eq, ContinuousLinearEquiv.apply_symm_apply]
  obtain ⟨U,ho,hconv,hφ,h0,hU⟩ := exists_uniform_canonicalParityProducts_weighted hp hp1 SpectralWeight.one (L φ)
  refine ⟨L ⁻¹' U,ho.preimage L.continuous,hconv.linear_preimage (L.restrictScalars ℝ).toLinearMap,
    hφ,by simpa only [Set.mem_preimage, map_zero] using h0,?_⟩
  intro r hr K hK
  have ht := (hU r hr K hK).comp (fun t : ℂ × pairParitySubspace (p := p) 0 => (t.1,L t.2))
  have hm := ht.mono (show K ×ˢ (L ⁻¹' U) ⊆
      (fun t : ℂ × pairParitySubspace (p := p) 0 => (t.1,L t.2)) ⁻¹'
        (K ×ˢ (U ∩ {ψ | weightedBaseToPair SpectralWeight.one ψ ∈ pairParitySubspace 0})) from
    fun t ht => ⟨ht.1,ht.2,by
      change weightedBaseToPair SpectralWeight.one (L t.2) ∈ pairParitySubspace 0
      rw [he]
      exact t.2.property⟩)
  simpa only [Function.comp_def,he] using hm

/-- Intrinsic parity polynomials converge locally uniformly on the full joint even-potential domain. -/
theorem tendstoLocallyUniformlyOn_canonicalParityProduct_joint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (r : ℤ) (hr : r = 0 ∨ r = 1) :
    TendstoLocallyUniformlyOn (fun (M : ℕ) (t : ℂ × pairParitySubspace (p := p) 0) =>
      normalizedCentralParityPolynomial hp t.2 (2*M) r t.1)
      (fun t => canonicalParityProduct hp t.2 r t.1) atTop Set.univ := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro t _
  obtain ⟨U,ho,_,ht,_,hU⟩ := exists_uniform_canonicalParityProducts hp hp1 t.2
  exact ⟨closedBall t.1 1 ×ˢ U,
    nhdsWithin_le_nhds (prod_mem_nhds (closedBall_mem_nhds t.1 (by norm_num)) (ho.mem_nhds ht)),
    hU r hr _ (isCompact_closedBall _ _)⟩

end NLS.ZakharovShabat
