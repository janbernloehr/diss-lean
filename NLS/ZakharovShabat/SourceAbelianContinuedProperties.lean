import NLS.ZakharovShabat.SourceAbelianContinuedPrimitive

/-! # Values, derivatives and endpoints of the continued primitive

All previous exterior values, the exact real normalization, and the
interior endpoint limits belong to the same jointly analytic function.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceAbelianContinuedPrimitive_source_fderiv (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (z : ℂ) (ψ h : CoeffPair p) (ht : (z,ψ) ∈ sourceAbelianContinuedDomain hp hp1 W) :
    (fderiv ℂ (fun χ : CoeffPair p => sourceAbelianContinuedPrimitive hp hp1 W n (z,χ)) ψ) h =
      (fderiv ℂ (fun χ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential χ) z) ψ) h /
        sourceCanonicalRoot hp hp1 ψ z := by
  have hjoint := sourceAbelianContinuedPrimitive_hasFDerivAt hp hp1 W hD hroot n (z,ψ) ht
  rw [fderiv_source_section_eq_joint _ z ψ hjoint.differentiableAt,hjoint.fderiv,
    fderiv_source_section_eq_joint _ z ψ
      (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,ψ) (mem_univ _)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,div_eq_inv_mul]

theorem sourceAbelianContinuedPrimitive_spectral_deriv (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (z : ℂ) (ψ : CoeffPair p) (ht : (z,ψ) ∈ sourceAbelianContinuedDomain hp hp1 W) :
    deriv (fun w : ℂ => sourceAbelianContinuedPrimitive hp hp1 W n (w,ψ)) z =
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z := by
  have hjoint := sourceAbelianContinuedPrimitive_hasFDerivAt hp hp1 W hD hroot n (z,ψ) ht
  rw [deriv_spectral_section_eq_fderiv _ z ψ hjoint.differentiableAt,hjoint.fderiv]
  rw [deriv_spectral_section_eq_fderiv
    (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1)
    z ψ (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,ψ) (mem_univ _)).differentiableAt]
  simp only [smul_apply,smul_eq_mul,div_eq_inv_mul]

/-- Every established exterior product neighborhood remains available. -/
theorem sourceAbelianEnlargedDomain_subset_continued (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) :
    sourceAbelianEnlargedDomain hp hp1 W ⊆ sourceAbelianContinuedDomain hp hp1 W := subset_union_left

theorem sourceAbelianContinuedDomain_subset_rootDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianContinuedDomain hp hp1 W) :
    t.1 ∈ sourceCanonicalRootDomain hp hp1 t.2 := by
  rcases ht with ht | ht
  · exact sourceAbelianEnlargedDomain_subset_rootDomain hp hp1 W t ht
  · obtain ⟨D,ht⟩ := mem_iUnion.mp ht
    exact ht.2.2

theorem mem_sourceAbelianContinuedDomain_real_iff (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (φ : realTypeSourceSubmodule p) (z : ℂ) :
    (z,φ.val) ∈ sourceAbelianContinuedDomain hp hp1 W ↔ z ∈ sourceCanonicalRootDomain hp hp1 φ.val :=
  ⟨sourceAbelianContinuedDomain_subset_rootDomain hp hp1 W (z,φ.val),
    fun hz => Or.inl ((mem_sourceAbelianEnlargedDomain_real_iff hp hp1 W φ z).mpr hz)⟩

theorem sourceAbelianContinuedPrimitive_eq_real (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (φ : realTypeSourceSubmodule p) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ.val) :
    sourceAbelianContinuedPrimitive hp hp1 W n (z,φ.val) = sourceAbelianPrimitive hp hp1 φ.val φ.property z+I*(Real.pi : ℂ)*n :=
  (sourceAbelianContinuedPrimitive_eq_enlarged hp hp1 W hD hroot n
    ((mem_sourceAbelianEnlargedDomain_real_iff hp hp1 W φ z).mpr hz)).trans
    (sourceAbelianEnlargedPrimitive_eq_real hp hp1 W hD (sourceFloquetJointMultiplier_analyticOnNhd hp hp1 W hroot) n φ z hz)

theorem sourceAbelianContinuedPrimitive_exp (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianContinuedDomain hp hp1 W) :
    exp (sourceAbelianContinuedPrimitive hp hp1 W n t) = exp (I*(Real.pi : ℂ)*n)*sourceFloquetJointMultiplier hp hp1 t := by
  rcases ht with ht | ht
  · rw [sourceAbelianContinuedPrimitive_eq_enlarged hp hp1 W hD hroot n ht]
    exact sourceAbelianEnlargedPrimitive_exp hp hp1 W (sourceFloquetJointMultiplier_analyticOnNhd hp hp1 W hroot) n t ht
  · obtain ⟨D,ht⟩ := mem_iUnion.mp ht
    rw [sourceAbelianContinuedPrimitive_eq_disc hp hp1 W hD hroot n D ht]
    exact D.exp_toFun hD hroot n t ht

theorem sourceAbelianContinuedPrimitive_eq_zeroIndex_add (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianContinuedDomain hp hp1 W) :
    sourceAbelianContinuedPrimitive hp hp1 W n t = sourceAbelianContinuedPrimitive hp hp1 W 0 t+I*(Real.pi : ℂ)*n := by
  rcases ht with ht | ht
  · rw [sourceAbelianContinuedPrimitive_eq_enlarged hp hp1 W hD hroot n ht,
      sourceAbelianContinuedPrimitive_eq_enlarged hp hp1 W hD hroot 0 ht]
    exact sourceAbelianEnlargedPrimitive_eq_zeroIndex_add hp hp1 W n t ht
  · obtain ⟨D,ht⟩ := mem_iUnion.mp ht
    rw [sourceAbelianContinuedPrimitive_eq_disc hp hp1 W hD hroot n D ht,
      sourceAbelianContinuedPrimitive_eq_disc hp hp1 W hD hroot 0 D ht]
    exact D.cauchy.primitive_eq_zeroIndex_add n t

/-- The entire cut disc at every source in a chart belongs to the union. -/
theorem sourceAbelianDisc_subset_continued (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (D : SourceAbelianDiscJointChart hp hp1 W) (ψ : CoeffPair p)
    (hψ : ψ ∈ ball D.source.val D.sourceRadius) (z : ℂ)
    (hz : z ∈ ball D.cauchy.center D.cauchy.radius \ sourcePeriodicSegment hp hp1 ψ D.gap) :
    (z,ψ) ∈ sourceAbelianContinuedDomain hp hp1 W :=
  Or.inr (mem_iUnion.mpr ⟨D,(D.mem_domain_iff (z,ψ)).mpr ⟨hz.1,hψ,hz.2⟩⟩)

/-- Endpoint normalization survives gluing, at both endpoints and also
when the selected complex gap is collapsed. -/
theorem sourceAbelianContinuedPrimitive_endpoint_limit (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (D : SourceAbelianDiscJointChart hp hp1 W) (n : ℤ) (ψ : CoeffPair p)
    (hψ : ψ ∈ ball D.source.val D.sourceRadius) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) D.gap,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) D.gap} : Set ℂ)) :
    Tendsto (fun z => sourceAbelianContinuedPrimitive hp hp1 W n (z,ψ))
      (𝓝[ball D.cauchy.center D.cauchy.radius \ sourcePeriodicSegment hp hp1 ψ D.gap] a)
      (𝓝 (I*(Real.pi : ℂ)*(n-D.gap))) := by
  apply (D.cauchy.primitive_endpoint_limit n ψ (D.source_subset hψ).1 a ha).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (sourceAbelianContinuedPrimitive_eq_disc hp hp1 W hD hroot n D
    ((D.mem_domain_iff (z,ψ)).mpr ⟨hz.1,hψ,hz.2⟩)).symm

/-- The previous filled local square is the square of the single
continued primitive wherever that primitive is defined in this disc. -/
theorem sourceAbelianContinuedPrimitive_square (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (D : SourceAbelianDiscJointChart hp hp1 W) (t : ℂ × CoeffPair p) (ht : t ∈ D.domain) :
    (sourceAbelianContinuedPrimitive hp hp1 W D.gap t)^2 = D.cauchy.square t := by
  rw [sourceAbelianContinuedPrimitive_eq_disc hp hp1 W hD hroot D.gap D ht]
  exact (D.cauchy.square_eq_primitive_sq t.2 t.1 (ht.2.2 D.gap)).symm

end NLS.ZakharovShabat
