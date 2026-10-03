import NLS.ZakharovShabat.SourceAbelianProjectedCompatibility

/-! # The enlarged open joint domain and its single abelian primitive

The projected continuation agrees with the earlier glued primitive on
their complete overlap. Their open domains can therefore be united
without changing any established values or differentials.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAbelianEnlargedDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Set (ℂ × CoeffPair p) :=
  sourceAbelianJointDomain hp hp1 ∪ sourceAbelianProjectedDomain hp hp1 W

def sourceAbelianEnlargedPrimitive (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (n : ℤ) (t : ℂ × CoeffPair p) : ℂ := by
  classical
  exact if t ∈ sourceAbelianProjectedDomain hp hp1 W then sourceAbelianProjectedPrimitive hp hp1 n t
    else sourceAbelianJointPrimitive hp hp1 n t

theorem isOpen_sourceAbelianEnlargedDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W)) : IsOpen (sourceAbelianEnlargedDomain hp hp1 W) :=
  (isOpen_sourceAbelianJointDomain hp hp1).union (isOpen_sourceAbelianProjectedDomain hp hp1 W hD)

theorem sourceAbelianEnlargedPrimitive_eq_projected (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (n : ℤ) : EqOn (sourceAbelianEnlargedPrimitive hp hp1 W n) (sourceAbelianProjectedPrimitive hp hp1 n)
      (sourceAbelianProjectedDomain hp hp1 W) := by
  intro t ht
  simp only [sourceAbelianEnlargedPrimitive,if_pos ht]

/-- Every value of the previously constructed joint function is preserved. -/
theorem sourceAbelianEnlargedPrimitive_eq_joint (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) : EqOn (sourceAbelianEnlargedPrimitive hp hp1 W n) (sourceAbelianJointPrimitive hp hp1 n)
      (sourceAbelianJointDomain hp hp1) := by
  intro t ht
  classical
  unfold sourceAbelianEnlargedPrimitive
  split_ifs with hpj
  · exact sourceAbelianProjectedPrimitive_eq_joint hp hp1 W hD hM n ⟨hpj,ht⟩
  · rfl

theorem sourceAbelianEnlargedPrimitive_eventuallyEq_joint (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianJointDomain hp hp1) :
    sourceAbelianEnlargedPrimitive hp hp1 W n =ᶠ[𝓝 t] sourceAbelianJointPrimitive hp hp1 n := by
  filter_upwards [(isOpen_sourceAbelianJointDomain hp hp1).mem_nhds ht] with u hu
  exact sourceAbelianEnlargedPrimitive_eq_joint hp hp1 W hD hM n hu

theorem sourceAbelianEnlargedPrimitive_eventuallyEq_projected (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianProjectedDomain hp hp1 W) :
    sourceAbelianEnlargedPrimitive hp hp1 W n =ᶠ[𝓝 t] sourceAbelianProjectedPrimitive hp hp1 n := by
  filter_upwards [(isOpen_sourceAbelianProjectedDomain hp hp1 W hD).mem_nhds ht] with u hu
  exact sourceAbelianEnlargedPrimitive_eq_projected hp hp1 W n hu

theorem sourceAbelianEnlargedPrimitive_analytic (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) : AnalyticOnNhd ℂ (sourceAbelianEnlargedPrimitive hp hp1 W n) (sourceAbelianEnlargedDomain hp hp1 W) := by
  intro t ht
  rcases ht with ht | ht
  · exact (sourceAbelianJointPrimitive_analytic hp hp1 n t ht).congr
      (sourceAbelianEnlargedPrimitive_eventuallyEq_joint hp hp1 W hD hM n t ht).symm
  · exact (sourceAbelianProjectedPrimitive_analytic hp hp1 W hD hM n t ht).congr
      (sourceAbelianEnlargedPrimitive_eventuallyEq_projected hp hp1 W hD n t ht).symm

theorem sourceAbelianEnlargedPrimitive_hasFDerivAt (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianEnlargedDomain hp hp1 W) :
    HasFDerivAt (sourceAbelianEnlargedPrimitive hp hp1 W n)
      ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t := by
  rcases ht with ht | ht
  · exact (sourceAbelianJointPrimitive_hasFDerivAt hp hp1 n t ht).congr_of_eventuallyEq
      (sourceAbelianEnlargedPrimitive_eventuallyEq_joint hp hp1 W hD
        (sourceFloquetJointMultiplier_analyticOnNhd hp hp1 W hroot) n t ht)
  · exact (sourceAbelianProjectedPrimitive_hasFDerivAt hp hp1 W hD hroot n t ht).congr_of_eventuallyEq
      (sourceAbelianEnlargedPrimitive_eventuallyEq_projected hp hp1 W hD n t ht)

theorem sourceAbelianEnlargedPrimitive_eq_real (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (φ : realTypeSourceSubmodule p) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ.val) :
    sourceAbelianEnlargedPrimitive hp hp1 W n (z,φ.val) = sourceAbelianPrimitive hp hp1 φ.val φ.property z+I*(Real.pi : ℂ)*n :=
  (sourceAbelianEnlargedPrimitive_eq_joint hp hp1 W hD hM n ((mem_sourceAbelianJointDomain_real_iff hp hp1 φ z).mpr hz)).trans
    (sourceAbelianJointPrimitive_eq_real hp hp1 n φ z hz)

theorem sourceAbelianEnlargedPrimitive_source_fderiv (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (z : ℂ) (ψ h : CoeffPair p) (ht : (z,ψ) ∈ sourceAbelianEnlargedDomain hp hp1 W) :
    (fderiv ℂ (fun χ : CoeffPair p => sourceAbelianEnlargedPrimitive hp hp1 W n (z,χ)) ψ) h =
      (fderiv ℂ (fun χ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential χ) z) ψ) h /
        sourceCanonicalRoot hp hp1 ψ z := by
  have hjoint := sourceAbelianEnlargedPrimitive_hasFDerivAt hp hp1 W hD hroot n (z,ψ) ht
  rw [fderiv_source_section_eq_joint _ z ψ hjoint.differentiableAt,hjoint.fderiv,
    fderiv_source_section_eq_joint _ z ψ
      (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,ψ) (mem_univ _)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,div_eq_inv_mul]

/-- Enlarging the joint domain never introduces a point on a canonical cut. -/
theorem sourceAbelianEnlargedDomain_subset_rootDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianEnlargedDomain hp hp1 W) :
    t.1 ∈ sourceCanonicalRootDomain hp hp1 t.2 := by
  rcases ht with ht | ht
  · exact sourceAbelianJointDomain_subset_rootDomain hp hp1 t ht
  · exact (sourceAbelianProjectedDomain_end hp hp1 W ht).2

/-- Every real-source slice still contains exactly its entire cut complement. -/
theorem mem_sourceAbelianEnlargedDomain_real_iff (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (φ : realTypeSourceSubmodule p) (z : ℂ) :
    (z,φ.val) ∈ sourceAbelianEnlargedDomain hp hp1 W ↔ z ∈ sourceCanonicalRootDomain hp hp1 φ.val :=
  ⟨sourceAbelianEnlargedDomain_subset_rootDomain hp hp1 W (z,φ.val),
    fun hz => Or.inl ((mem_sourceAbelianJointDomain_real_iff hp hp1 φ z).mpr hz)⟩

/-- The signed normalization is unchanged on the entire enlarged domain. -/
theorem sourceAbelianEnlargedPrimitive_eq_zeroIndex_add (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianEnlargedDomain hp hp1 W) :
    sourceAbelianEnlargedPrimitive hp hp1 W n t = sourceAbelianEnlargedPrimitive hp hp1 W 0 t+I*(Real.pi : ℂ)*n := by
  classical
  unfold sourceAbelianEnlargedPrimitive
  split_ifs with hpj
  · exact sourceAbelianProjectedPrimitive_eq_zeroIndex_add hp hp1 n t
  · exact sourceAbelianJointPrimitive_eq_zeroIndex_add hp hp1 n t (ht.resolve_right hpj)

/-- The enlarged primitive retains the exact Floquet exponential identity. -/
theorem sourceAbelianEnlargedPrimitive_exp (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianEnlargedDomain hp hp1 W) :
    exp (sourceAbelianEnlargedPrimitive hp hp1 W n t) = exp (I*(Real.pi : ℂ)*n)*sourceFloquetJointMultiplier hp hp1 t := by
  classical
  unfold sourceAbelianEnlargedPrimitive
  split_ifs with hpj
  · exact sourceAbelianProjectedPrimitive_exp hp hp1 W hM n t hpj
  · exact sourceAbelianJointPrimitive_exp hp hp1 n t (ht.resolve_right hpj)

/-- The spectral derivative is the literal discriminant quotient also
at the new complex-source points of the enlarged domain. -/
theorem sourceAbelianEnlargedPrimitive_spectral_deriv (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (z : ℂ) (ψ : CoeffPair p) (ht : (z,ψ) ∈ sourceAbelianEnlargedDomain hp hp1 W) :
    deriv (fun w : ℂ => sourceAbelianEnlargedPrimitive hp hp1 W n (w,ψ)) z =
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z := by
  have hjoint := sourceAbelianEnlargedPrimitive_hasFDerivAt hp hp1 W hD hroot n (z,ψ) ht
  rw [deriv_spectral_section_eq_fderiv _ z ψ hjoint.differentiableAt,hjoint.fderiv]
  rw [deriv_spectral_section_eq_fderiv
    (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1)
    z ψ (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,ψ) (mem_univ _)).differentiableAt]
  simp only [smul_apply,smul_eq_mul,div_eq_inv_mul]

end NLS.ZakharovShabat
