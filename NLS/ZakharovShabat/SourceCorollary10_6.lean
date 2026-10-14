import NLS.ZakharovShabat.SourceSingleRootQuotientCommonDomain

/-!
# Corollary 10.6 on the unchanged common domain

All ℓᵖ root displacements are allowed, including collisions and zeros of
unomitted numerator factors. The literal unordered product equals the
analytic quotient. The same W, V, isolating disks and distance constant
as in Lemma 10.5 suffice for every omitted index simultaneously.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original local family with the analytic quotient on the printed domain and selected disk. -/
structure SourceSingleRootQuotientNeighborhoods (hp : p ≠ ⊤) (hp1 : 1 < p)
    (V : Set (CoeffPair p)) (D : ℤ → Set ℂ) (c : ℝ) : Prop extends
    SourceOmittedRootNeighborhoods hp hp1 V D c where
  quotient_joint : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceSingleRootQuotientJointProduct hp hp1 n)
    ((⋃ m : ℤ, ⋃ (_ : m ≠ n), closure (D m))ᶜ ×ˢ (univ ×ˢ V))
  literal_product : ∀ n : ℤ,
    AnalyticOnNhd ℂ (fun q : ℂ × (Coeff p × CoeffPair p) =>
      ∏' m : {m : ℤ // m ≠ n},
        (displacedRoots q.2.1 m-q.1)/sourceStandardRoot hp hp1 q.2.2 m q.1)
      ((⋃ m : ℤ, ⋃ (_ : m ≠ n), closure (D m))ᶜ ×ˢ (univ ×ˢ V))
  quotient_disk : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceSingleRootQuotientJointProduct hp hp1 n)
    (D n ×ˢ (univ ×ˢ V))

/-- Corollary 10.6 retains Lemma 10.5 and identifies both ordered cutoffs and the unordered product. -/
structure SourceCorollary10_6Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  roots : SourceLemma10_5Data hp hp1 W
  spectral : ∀ ψ ∈ W, ∀ a : Coeff p, ∀ n : ℤ,
    AnalyticOnNhd ℂ (fun z => sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ)))
      (sourceStandardRootOmittedDomain hp hp1 ψ n)
  joint : ∀ n : ℤ, IsOpen (sourceSingleRootQuotientJointDomain hp hp1 W n) ∧
    AnalyticOnNhd ℂ (sourceSingleRootQuotientJointProduct hp hp1 n)
      (sourceSingleRootQuotientJointDomain hp hp1 W n)
  locally_uniform : ∀ n : ℤ,
    TendstoLocallyUniformlyOn (sourceSingleRootQuotientPartialProduct hp hp1 n)
      (sourceSingleRootQuotientJointProduct hp hp1 n) atTop
      (sourceSingleRootQuotientJointDomain hp hp1 W n)
  absolute : ∀ ψ : CoeffPair p, ∀ a : Coeff p, ∀ z : ℂ, ∀ n : ℤ,
    Summable (fun m : ℤ => ‖sourceSingleRootQuotientFactor hp hp1 ψ a z n m-1‖)
  product : ∀ ψ : CoeffPair p, ∀ a : Coeff p, ∀ n : ℤ,
    ∀ z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n,
    HasProd (fun m : {m : ℤ // m ≠ n} =>
      (displacedRoots a m-z)/sourceStandardRoot hp hp1 ψ m z)
      (sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ)))
  neighborhoods : ∀ ψ ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ ψ ∈ V ∧ V ⊆ W ∧
    ∃ D c, SourceSingleRootQuotientNeighborhoods hp hp1 V D c

/-- Every Lemma 10.5 domain supports the full corollary with the same local isolating families. -/
theorem SourceLemma10_5Data.quotients
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) : SourceCorollary10_6Data hp hp1 W := by
  refine ⟨h,fun ψ hψ a n => h.quotientSpectral ψ hψ a n,h.quotientJoint,h.quotientLocallyUniform,
    summable_norm_sourceSingleRootQuotientFactor_sub_one hp hp1,
    fun ψ a n z hz => hasProd_sourceSingleRootQuotient_subtype hp hp1 ψ a z n hz,?_⟩
  intro ψ hψ
  obtain ⟨V,ho,hc,hψV,hVW,D,c,hD⟩ := h.neighborhoods ψ hψ
  exact ⟨V,ho,hc,hψV,hVW,D,c,hD,
    fun n => h.quotientClosedFixed hVW hD.toSourceIsolatingNeighborhoods n,
    fun n => h.quotientTprodClosedFixed hVW hD.toSourceIsolatingNeighborhoods n,
    fun n => h.quotientDisk hVW hD.toSourceIsolatingNeighborhoods n⟩

/-- Corollary 10.6 for every finite p>1 on one connected open neighborhood of the real source locus. -/
theorem sourceCorollary10_6 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceCorollary10_6Data hp hp1 W := by
  obtain ⟨W,ho,hc,hreal,h⟩ := sourceLemma10_5 hp hp1
  exact ⟨W,ho,hc,hreal,h.quotients⟩

end NLS.ZakharovShabat
