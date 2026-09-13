import NLS.ZakharovShabat.CanonicalPeriodicProductUniform

/-!
# Joint continuity of the canonical periodic product

Uniform convergence over potential neighborhoods yields joint local uniform
convergence. The eventual analytic finite approximants then give joint continuity.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The compact-by-neighborhood convergence theorem in the original potential space. -/
theorem exists_uniform_canonicalPeriodicProduct_pair (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ K : Set ℂ, IsCompact K →
        TendstoUniformlyOn (fun (M : ℕ) (t : ℂ × PairSpace p) =>
          normalizedCentralPeriodicPolynomial hp t.2 M t.1)
          (fun t => canonicalPeriodicProduct hp t.2 t.1) atTop (K ×ˢ U) := by
  obtain ⟨U,ho,hconv,hφ,h0,h⟩ := exists_uniform_canonicalPeriodicProduct hp hp1 SpectralWeight.one
    (unitBaseEquiv.symm φ)
  refine ⟨unitBaseEquiv.symm ⁻¹' U,ho.preimage unitBaseEquiv.symm.continuous,
    hconv.linear_preimage (unitBaseEquiv.symm.toContinuousLinearMap.restrictScalars ℝ).toLinearMap,
    hφ,by simpa only [Set.mem_preimage, map_zero] using h0,?_⟩
  have he (ψ : PairSpace p) : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm ψ) = ψ := by
    rw [← unitBaseEquiv_eq, ContinuousLinearEquiv.apply_symm_apply]
  intro K hK
  have ht := (h K hK).comp (fun t : ℂ × PairSpace p => (t.1,unitBaseEquiv.symm t.2))
  have hm := ht.mono (show K ×ˢ (unitBaseEquiv.symm ⁻¹' U) ⊆
      (fun t : ℂ × PairSpace p => (t.1,unitBaseEquiv.symm t.2)) ⁻¹' (K ×ˢ U) from
    fun _ hx => ⟨hx.1,hx.2⟩)
  simpa only [Function.comp_def, he] using hm

/-- The normalized finite products converge locally uniformly jointly in both variables. -/
theorem tendstoLocallyUniformlyOn_canonicalPeriodicProduct_joint (hp : p ≠ ⊤) (hp1 : 1 < p) :
    TendstoLocallyUniformlyOn (fun (M : ℕ) (t : ℂ × PairSpace p) =>
      normalizedCentralPeriodicPolynomial hp t.2 M t.1)
      (fun t => canonicalPeriodicProduct hp t.2 t.1) atTop Set.univ := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro t _
  obtain ⟨U,ho,_,ht,_,h⟩ := exists_uniform_canonicalPeriodicProduct_pair hp hp1 t.2
  exact ⟨closedBall t.1 1 ×ˢ U,
    nhdsWithin_le_nhds (prod_mem_nhds (closedBall_mem_nhds t.1 (by norm_num)) (ho.mem_nhds ht)),
    h _ (isCompact_closedBall _ _)⟩

/-- Joint continuity follows from uniform convergence of the eventual joint analytic approximants. -/
theorem continuous_canonicalPeriodicProduct_joint (hp : p ≠ ⊤) (hp1 : 1 < p) :
    Continuous (fun t : ℂ × PairSpace p => canonicalPeriodicProduct hp t.2 t.1) := by
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨N,U,_,ho,_,ht,_,ha⟩ := exists_uniform_analytic_normalizedCentralPolynomials hp t.2
  have hc : ContinuousOn (fun t : ℂ × PairSpace p => canonicalPeriodicProduct hp t.2 t.1)
      (Set.univ ×ˢ U) := by
    apply ((tendstoLocallyUniformlyOn_canonicalPeriodicProduct_joint hp hp1).mono
      (Set.subset_univ _)).continuousOn
    exact (eventually_ge_atTop N).mono (fun M hM => (ha M hM).continuousOn) |>.frequently
  exact (hc t ⟨Set.mem_univ _,ht⟩).continuousAt
    ((isOpen_univ.prod ho).mem_nhds ⟨Set.mem_univ _,ht⟩)

end NLS.ZakharovShabat
