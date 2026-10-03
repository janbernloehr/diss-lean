import NLS.ZakharovShabat.SourceAbelianDiscSquare

/-! # The squared normalized abelian primitive across a selected gap

A dense-limit construction makes the continuation independent of an
isolating chart. It agrees with the actual normalized square on the
original domain and is analytic on that domain union any isolating disc.
-/
noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- For a real source, the canonical cut complement is dense. -/
theorem dense_sourceCanonicalRootDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) : Dense (sourceCanonicalRootDomain hp hp1 φ) := by
  intro z
  exact mem_closure_iff_nhdsWithin_neBot.mpr (nhdsWithin_sourceCanonicalRootDomain_neBot hp hp1 φ hφ z)

/-- The square of `F_n`, continued across its selected cut by relative
limits from the canonical cut complement. -/
def sourceAbelianSquare (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) : ℂ → ℂ :=
  denseLimitExtension (fun z => (sourceAbelianPrimitive hp hp1 φ hφ z+I*(Real.pi : ℂ)*n)^2)
    (sourceCanonicalRootDomain hp hp1 φ)

/-- On the original enlarged domain, continuation preserves exactly
the square with its signed-index additive normalization. -/
theorem sourceAbelianSquare_eq_normalized_sq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    EqOn (sourceAbelianSquare hp hp1 φ hφ n)
      (fun z => (sourceAbelianPrimitive hp hp1 φ hφ z+I*(Real.pi : ℂ)*n)^2)
      (sourceOpenGapComplement hp hp1 φ) := by
  apply denseLimitExtension_eqOn_local _ _ _ _ (dense_sourceCanonicalRootDomain hp hp1 φ hφ)
    (isOpen_sourceOpenGapComplement_of_realType hp hp1 φ hφ)
    (((sourceAbelianPrimitive_analytic hp hp1 φ hφ).add analyticOnNhd_const).pow 2).continuousOn
  intro z _
  rfl

/-- Every isolating chart gives the same square, including on the
selected cut where the original primitive has opposite side values. -/
theorem sourceAbelianSquare_eq_disc
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) :
    EqOn (sourceAbelianSquare hp hp1 φ hφ n) D.squareExtension (ball D.center D.radius) :=
  denseLimitExtension_eqOn_local _ _ _ _ (dense_sourceCanonicalRootDomain hp hp1 φ hφ)
    isOpen_ball D.squareExtension_spec.1.continuousOn
    (fun z hz => D.squareExtension_eq_global_of_mem_rootDomain z hz.1 hz.2)

/-- The real-source continuation assertion in Lemma 19.1(iv): the
square is analytic after adjoining an entire isolating disc to the
plane with the remaining noncollapsed cuts removed. -/
theorem sourceAbelianSquare_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (D : SourceAbelianDiscPrimitive hp hp1 φ hφ n) :
    AnalyticOnNhd ℂ (sourceAbelianSquare hp hp1 φ hφ n)
      (sourceOpenGapComplement hp hp1 φ ∪ ball D.center D.radius) := by
  intro z hz
  rcases hz with hz | hz
  · apply ((((sourceAbelianPrimitive_analytic hp hp1 φ hφ).add analyticOnNhd_const).pow 2) z hz).congr
    filter_upwards [(isOpen_sourceOpenGapComplement_of_realType hp hp1 φ hφ).mem_nhds hz] with w hw
    exact (sourceAbelianSquare_eq_normalized_sq hp hp1 φ hφ n hw).symm
  · apply (D.squareExtension_spec.1 z hz).congr
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact (sourceAbelianSquare_eq_disc hp hp1 φ hφ n D hw).symm

/-- Both endpoints have value zero after analytic continuation,
without any open-gap hypothesis. -/
theorem sourceAbelianSquare_endpoints
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    sourceAbelianSquare hp hp1 φ hφ n
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n) = 0 ∧
    sourceAbelianSquare hp hp1 φ hφ n
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n) = 0 := by
  obtain ⟨D⟩ := nonempty_sourceAbelianDiscPrimitive hp hp1 φ hφ n
  constructor
  · rw [sourceAbelianSquare_eq_disc hp hp1 φ hφ n D (D.segment_subset (left_mem_segment ℝ _ _))]
    exact D.squareExtension_spec.2.2.1
  · rw [sourceAbelianSquare_eq_disc hp hp1 φ hφ n D (D.segment_subset (right_mem_segment ℝ _ _))]
    exact D.squareExtension_spec.2.2.2

/-- The continued square takes the squared real arcosh profile on the
whole closed gap. It is independent of the side used to reach the cut. -/
theorem sourceAbelianSquare_eq_arcosh_sq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re) :
    sourceAbelianSquare hp hp1 φ hφ n (x : ℂ) = (sourceRealGapArcoshProfile hp φ n x : ℂ)^2 := by
  obtain ⟨D⟩ := nonempty_sourceAbelianDiscPrimitive hp hp1 φ hφ n
  have hxB := D.segment_subset (sourcePeriodicSegment_mem_of_realIcc hp hp1 φ hφ n x hx)
  let := nhdsWithin_sourceAbelianHalfPlane_neBot true (x : ℂ) (ofReal_im x)
  have hcont : Tendsto (sourceAbelianSquare hp hp1 φ hφ n)
      (𝓝[sourceAbelianHalfPlane true] (x : ℂ))
      (𝓝 (sourceAbelianSquare hp hp1 φ hφ n (x : ℂ))) :=
    ((sourceAbelianSquare_analytic hp hp1 φ hφ n D _ (Or.inr hxB)).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  have hlim := (sourceAbelianPrimitive_gap_boundary_limit hp hp1 φ hφ n true x hx).pow 2
  simp only [ite_true] at hlim
  apply tendsto_nhds_unique hcont
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (sourceAbelianSquare_eq_normalized_sq hp hp1 φ hφ n
    (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ
      (sourceAbelianHalfPlane_subset_rootDomain hp hp1 φ hφ true hz))).symm

/-- The square is analytic at every point of the selected gap, without
requiring callers to supply a disc or an open-gap assumption. -/
theorem sourceAbelianSquare_analyticAt_of_mem_segment
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourcePeriodicSegment hp hp1 φ n) :
    AnalyticAt ℂ (sourceAbelianSquare hp hp1 φ hφ n) z := by
  obtain ⟨D⟩ := nonempty_sourceAbelianDiscPrimitive hp hp1 φ hφ n
  exact sourceAbelianSquare_analytic hp hp1 φ hφ n D z (Or.inr (D.segment_subset hz))

/-- At the zero potential the square is the exact entire quadratic,
including every collapsed free periodic point. -/
@[simp] theorem sourceAbelianSquare_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (z : ℂ) :
    sourceAbelianSquare hp hp1 (0 : CoeffPair p) (by simp) n z = -(z-(Real.pi : ℂ)*n)^2 := by
  rw [sourceAbelianSquare_eq_normalized_sq hp hp1 0 (by simp) n (by simp),sourceAbelianPrimitive_zero]
  change (-I*z+I*(Real.pi : ℂ)*n)^2 = _
  calc
    (-I*z+I*(Real.pi : ℂ)*n)^2 = I^2*(z-(Real.pi : ℂ)*n)^2 := by ring
    _ = -(z-(Real.pi : ℂ)*n)^2 := by rw [I_sq,neg_one_mul]

end NLS.ZakharovShabat
