import NLS.ZakharovShabat.SourceAbelianUniformDiscFamily

/-! # Full complex spectral continuation on one common source ball

The same projected exterior primitive extends into every disjoint
isolating disc. Local finiteness makes the common exterior open, and
the exterior together with all cut discs covers the whole spectral
cut complement. No intersection of infinitely many source neighborhoods
is needed.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
/-- Restricting the joint projected differential to the spectral line. -/
theorem sourceAbelianProjectedPrimitive_hasDerivAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (z : ℂ) (ψ : CoeffPair p) (ht : (z,ψ) ∈ sourceAbelianProjectedDomain hp hp1 W) :
    HasDerivAt (fun w : ℂ => sourceAbelianProjectedPrimitive hp hp1 n (w,ψ))
      (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z := by
  have hg : HasFDerivAt (sourceAbelianProjectedPrimitive hp hp1 n)
      ((sourceCanonicalRoot hp hp1 ψ z)⁻¹ •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) (z,ψ)) (z,ψ) := by
    simpa only using! sourceAbelianProjectedPrimitive_hasFDerivAt hp hp1 W hD hroot n (z,ψ) ht
  have hinc : HasDerivAt (fun w : ℂ => (w,ψ)) (1,0) z := by
    simpa only using! (hasDerivAt_id z).prodMk (hasDerivAt_const z ψ)
  have h := hg.comp_hasDerivAt z hinc
  have he := deriv_spectral_section_eq_fderiv
    (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) z ψ
    (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,ψ) (mem_univ _)).differentiableAt
  simpa only [smul_apply,smul_eq_mul,← he,div_eq_inv_mul] using! h

namespace SourceAbelianUniformDiscFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- All disc continuations exist simultaneously at every source in
the single source ball, for each signed normalization index. -/
theorem exists_disc_primitives (D : SourceAbelianUniformDiscFamily hp hp1 W)
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (ψ : CoeffPair p) (hψ : ψ ∈ ball D.source.val D.sourceRadius) (n : ℤ) (j : ℤ) :
    ∃ F : ℂ → ℂ,
      EqOn F (fun z => sourceAbelianProjectedPrimitive hp hp1 n (z,ψ))
        (ball (D.center j) (D.outer j) \ closedBall (D.center j) (D.inner j)) ∧
      AnalyticOnNhd ℂ F (ball (D.center j) (D.outer j) \ sourcePeriodicSegment hp hp1 ψ j) ∧
      ∀ z ∈ ball (D.center j) (D.outer j) \ sourcePeriodicSegment hp hp1 ψ j,
        HasDerivAt F (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z := by
  have hG : ∀ z ∈ ball (D.center j) (D.outer j) \ closedBall (D.center j) (D.inner j),
      HasDerivAt (fun w : ℂ => sourceAbelianProjectedPrimitive hp hp1 n (w,ψ))
        (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z := by
    intro z hz
    have ht : (z,ψ) ∈ sourceAbelianProjectedDomain hp hp1 W :=
      D.exterior_product_subset_projected ⟨D.collar_subset_exterior j hz,hψ⟩
    simpa only using! sourceAbelianProjectedPrimitive_hasDerivAt hp hp1 W hD hroot n z ψ ht
  simpa only using! exists_sourceAbelian_complexDisc_from_annulus hp hp1 ψ j (D.center j) (D.inner j) (D.outer j)
    (D.inner_pos j).le (D.inner_lt j) (D.segment_subset ψ hψ j) (D.avoids_other ψ hψ j)
    (fun z => sourceAbelianProjectedPrimitive hp hp1 n (z,ψ)) hG


/-- A single spectral primitive extends the projected exterior to the
entire moving cut complement at any complex source in the common ball. -/
theorem exists_spectral_primitive (D : SourceAbelianUniformDiscFamily hp hp1 W)
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (ψ : CoeffPair p) (hψ : ψ ∈ ball D.source.val D.sourceRadius) (n : ℤ) :
    ∃ F : ℂ → ℂ,
      EqOn F (fun z => sourceAbelianProjectedPrimitive hp hp1 n (z,ψ)) D.exterior ∧
      AnalyticOnNhd ℂ F (sourceCanonicalRootDomain hp hp1 ψ) ∧
      ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
        HasDerivAt F (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z := by
  choose f hfeq hfa hfd using D.exists_disc_primitives hD hroot ψ hψ n
  let U : Option ℤ → Set ℂ := fun k => match k with
    | none => D.exterior
    | some j => ball (D.center j) (D.outer j) \ sourcePeriodicSegment hp hp1 ψ j
  let g : Option ℤ → ℂ → ℂ := fun k => match k with
    | none => fun z => sourceAbelianProjectedPrimitive hp hp1 n (z,ψ)
    | some j => f j
  have hopen (k : Option ℤ) : IsOpen (U k) := by
    cases k with
    | none => exact D.isOpen_exterior
    | some j => exact isOpen_sourceAbelian_complexDisc hp hp1 ψ j (D.center j) (D.outer j)
  have hcompat (k l : Option ℤ) : EqOn (g k) (g l) (U k ∩ U l) := by
    cases k with
    | none =>
      cases l with
      | none => intro z _; rfl
      | some j =>
        intro z hz
        exact (hfeq j ⟨hz.2.1,fun hj => hz.1 (mem_iUnion.mpr ⟨j,hj⟩)⟩).symm
    | some i =>
      cases l with
      | none =>
        intro z hz
        exact hfeq i ⟨hz.1.1,fun hi => hz.2 (mem_iUnion.mpr ⟨i,hi⟩)⟩
      | some j =>
        intro z hz
        by_cases hij : i = j
        · subst j; rfl
        · exact (Set.disjoint_left.mp (D.disjoint i j hij) hz.1.1 hz.2.1).elim
  have hcover : sourceCanonicalRootDomain hp hp1 ψ = ⋃ k, U k := by
    rw [D.rootDomain_eq_union ψ hψ]
    ext z
    simp only [mem_union,mem_iUnion]
    constructor
    · rintro (hz | ⟨j,hj⟩)
      · exact ⟨none,hz⟩
      · exact ⟨some j,hj⟩
    · rintro ⟨k,hk⟩
      cases k with
      | none => exact Or.inl hk
      | some j => exact Or.inr ⟨j,hk⟩
  have hga (k : Option ℤ) : AnalyticOnNhd ℂ (g k) (U k) := by
    cases k with
    | none =>
      intro z hz
      exact (sourceAbelianProjectedPrimitive_analytic hp hp1 W hD
        (sourceFloquetJointMultiplier_analyticOnNhd hp hp1 W hroot) n (z,ψ)
        (D.exterior_product_subset_projected ⟨hz,hψ⟩)).comp
          (f := fun w : ℂ => (w,ψ)) (analyticAt_id.prod analyticAt_const)
    | some j => exact hfa j
  have hgd (k : Option ℤ) (z : ℂ) (hz : z ∈ U k) :
      HasDerivAt (g k) (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z := by
    cases k with
    | none =>
      have ht : (z,ψ) ∈ sourceAbelianProjectedDomain hp hp1 W := D.exterior_product_subset_projected ⟨hz,hψ⟩
      simpa only using! sourceAbelianProjectedPrimitive_hasDerivAt hp hp1 W hD hroot n z ψ ht
    | some j => exact hfd j z hz
  refine ⟨glueHolomorphicCharts U g,glueHolomorphicCharts_eq_on U g hcompat none,?_,?_⟩
  · intro z hz
    obtain ⟨k,hk⟩ := mem_iUnion.mp (hcover ▸ hz)
    simpa only using! (hga k z hk).congr (glueHolomorphicCharts_eventuallyEq U g hopen hcompat k z hk).symm
  · intro z hz
    obtain ⟨k,hk⟩ := mem_iUnion.mp (hcover ▸ hz)
    simpa only using! (hgd k z hk).congr_of_eventuallyEq (glueHolomorphicCharts_eventuallyEq U g hopen hcompat k z hk)

/-- All normalizations can use the same spectral continuation, with
their exact signed-index shift everywhere, including every cut disc. -/
theorem exists_indexed_spectral_primitives (D : SourceAbelianUniformDiscFamily hp hp1 W)
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (ψ : CoeffPair p) (hψ : ψ ∈ ball D.source.val D.sourceRadius) :
    ∃ F : ℤ → ℂ → ℂ, ∀ n : ℤ,
      EqOn (F n) (fun z => sourceAbelianProjectedPrimitive hp hp1 n (z,ψ)) D.exterior ∧
      AnalyticOnNhd ℂ (F n) (sourceCanonicalRootDomain hp hp1 ψ) ∧
      (∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
        HasDerivAt (F n) (deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z) z) ∧
      ∀ z : ℂ, F n z = F 0 z+I*(Real.pi : ℂ)*n := by
  obtain ⟨f,heq,ha,hd⟩ := D.exists_spectral_primitive hD hroot ψ hψ 0
  refine ⟨fun n z => f z+I*(Real.pi : ℂ)*n,?_⟩
  intro n
  refine ⟨?_,fun z hz => (ha z hz).add analyticAt_const,fun z hz => (hd z hz).add_const _,?_⟩
  · intro z hz
    change f z+I*(Real.pi : ℂ)*n = sourceAbelianProjectedPrimitive hp hp1 n (z,ψ)
    rw [heq hz,sourceAbelianProjectedPrimitive_eq_zeroIndex_add hp hp1 n (z,ψ)]
  · intro z
    simp only [Int.cast_zero,mul_zero,add_zero]

end SourceAbelianUniformDiscFamily
end NLS.ZakharovShabat
