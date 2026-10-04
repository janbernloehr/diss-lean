import NLS.ZakharovShabat.SourcePsiOpenGapQuotient
import NLS.ZakharovShabat.SourceAbelianMomentQuadraticShift
import NLS.ZakharovShabat.SourceFiniteGap
import NLS.ZakharovShabat.SourceFullAbelianCubicContourPoisson
import NLS.ComplexAnalysis.FiniteCircleHoleDecomposition

/-! # Large moment contours as finite sums around the open gaps

The filled psi quotient removes every closed gap. Cauchy's theorem on a
disc with finitely many holes then decomposes the large contour, and real
contour comparison identifies the small circles with the moment atlas.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

namespace SourceAbelianMomentAtlas

/-- Every sufficiently large circle avoiding the spectrum decomposes into
the atlas circles around precisely the open gaps. One threshold works for
all numerator indices, primitive indices and moment orders. -/
theorem exists_finiteGap_contour_decomposition
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sphere (0 : ℂ) R ⊆ sourceCanonicalRootDomain hp hp1 φ.val →
      ∀ n : ℤ, canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
        (periodOnePotential_mem φ.val) n ≠ 0 → ∀ j : ℤ, ∀ q : ℕ,
      sourceAbelianMomentCircle hp hp1 W n j q (s n φ.val) φ.val 0 R =
        ∑ k ∈ hf.toFinset, sourceAbelianMomentCircle hp hp1 W n j q (s n φ.val) φ.val
          ((A.localChart φ).center k) ((A.localChart φ).contourRadius k) := by
  classical
  have hφ : φ.val ∈ A.sourceBall φ := mem_ball_self (A.localChart φ).radius_pos
  obtain ⟨D⟩ := (A.localChart φ).charts φ.val hφ
  have hfamily := (A.localChart φ).family φ.val hφ
  obtain ⟨N, ε, _, _, U, _, _, hφU, hcluster, hdisj⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ.val φ.property
  have hgap (k : ℤ) := sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val φ.val N ε k
    (hcluster φ.val hφU k)
  obtain ⟨C⟩ := nonempty_sourcePsiIsolatingCircleFamily hp hp1 φ.val φ.val N ε hgap hdisj
  let c := sourceIsolatingCenter hp hp1 φ.val N
  let S : Finset ℤ := hf.toFinset
  have hS (k : ℤ) : k ∈ S ↔ canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0 := Set.Finite.mem_toFinset hf
  have hc : IsCompact (⋃ k ∈ S, closedBall (c k) (C.outer k)) :=
    S.finite_toSet.isCompact_biUnion fun k _ => isCompact_closedBall _ _
  obtain ⟨B, hB⟩ := hc.isBounded.exists_norm_le
  let T := max B 0 + 1
  have hT : 0 < T := by dsimp [T]; linarith [le_max_right B 0]
  refine ⟨T, hT, ?_⟩
  intro R hTR hcircle n hn j q
  have hR : 0 ≤ R := (hT.trans_le hTR).le
  let f := fun z => sourceFullAbelianPrimitive hp hp1 W j (z,φ.val)^q *
    sourcePsiFilledQuotient hp hp1 n (s n φ.val) φ.val z
  have heq (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ.val) :
      f z = sourceAbelianMomentIntegrand hp hp1 W n j q (z,((s n φ.val : Coeff p),φ.val)) := by
    dsimp only [f, sourceAbelianMomentIntegrand]
    rw [sourcePsiFilledQuotient_eq_contourIntegrand hp hp1 n _ _ z hz]
  have henclosed (k : ℤ) (hk : k ∈ S) : closedBall (c k) (C.outer k) ⊆ ball 0 R := by
    intro z hz
    have hb := hB z (Set.mem_iUnion₂.mpr ⟨k,hk,hz⟩)
    rw [mem_ball, dist_zero_right]
    dsimp [T] at hTR
    linarith [le_max_left B 0]
  have ha : AnalyticOnNhd ℂ f (circleHoleDomain 0 R S c C.inner) := by
    intro z hz
    have hzO : z ∈ sourceOpenGapComplement hp hp1 φ.val := by
      intro k hk hzk
      exact hz.2 k ((hS k).mpr hk) (C.gap_enclosed k hzk)
    exact ((sourceFullAbelianPrimitive_spectral_analytic D j z hzO).pow q).mul
      (hs.analytic_filledQuotient φ n hn z hzO)
  have hdec := circleIntegral_eq_sum_of_finite_holes 0 R hR S c C.inner C.outer f
    (fun k _ => C.inner_pos k) (fun k _ => C.collar k) henclosed
    (fun k _ l _ hkl => C.disjoint_discs k l hkl) ha
  have houter : (∮ z in C(0,R), f z) =
      sourceAbelianMomentCircle hp hp1 W n j q (s n φ.val) φ.val 0 R :=
    circleIntegral.integral_congr hR (fun z hz => heq z (hcircle hz))
  have hinner (k : ℤ) : (∮ z in C(c k,C.inner k), f z) =
      sourceAbelianMomentCircle hp hp1 W n j q (s n φ.val) φ.val
        ((A.localChart φ).center k) ((A.localChart φ).contourRadius k) := by
    have hC := C.contour_family
    calc
      _ = sourceAbelianMomentCircle hp hp1 W n j q (s n φ.val) φ.val (c k) (C.inner k) :=
        circleIntegral.integral_congr (C.inner_pos k).le (fun z hz => heq z ((hC.2 k).2.2.2 hz))
      _ = _ := sourceAbelianMomentCircle_eq_of_realCentered_enclosingCircles hp hp1 W j q n k
        (s n φ.val) φ.val D φ.property _ _ _ _ (hC.1 k) (hfamily.1 k)
        (hC.2 k).1 (hfamily.2 k).1 (hC.2 k).2.1 (hfamily.2 k).2.1
        (hC.2 k).2.2.1 (hfamily.2 k).2.2.1
  rw [houter] at hdec
  simpa only [hinner] using hdec

/-- The large unshifted quadratic contour has exactly the renormalized
second-moment sum required in Lemma 20.2. -/
theorem exists_finiteGap_quadratic_contour_formula
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sphere (0 : ℂ) R ⊆ sourceCanonicalRootDomain hp hp1 φ.val →
      ∀ n : ℤ, canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
        (periodOnePotential_mem φ.val) n ≠ 0 →
      -(4/(2*Real.pi) : ℂ)*sourceAbelianMomentCircle hp hp1 W n 0 2 (s n φ.val) φ.val 0 R -
        (2*(n : ℂ)*Real.pi)^2 = -(4/(2*Real.pi) : ℂ)*(∑' k : ℤ, A.moment n k 2 φ.val) := by
  classical
  obtain ⟨T,hT,hdec⟩ := A.exists_finiteGap_contour_decomposition hs φ hf
  refine ⟨T,hT,fun R hR hcircle n hn => ?_⟩
  rw [hdec R hR hcircle n hn 0 2]
  apply A.quadratic_contour_sum_renormalization φ φ.val
    (mem_ball_self (A.localChart φ).radius_pos) hf.toFinset
  · intro k hk
    by_contra hne
    exact hk ((Set.Finite.mem_toFinset hf).mpr hne)
  · exact (Set.Finite.mem_toFinset hf).mpr hn

end SourceAbelianMomentAtlas

namespace SourceAngularThetaCommonDomainData
variable {W₀ B U : Set (CoeffPair p)}

/-- The actual angle bracket of the cubic contour, after subtracting the
free frequency, equals the second-moment sum. Identifying this bracket
with the physical NLS frequency is a separate step. -/
theorem exists_finiteGap_cubicContour_moment_formula
    (E : SourceAngularThetaCommonDomainData hp hp1 W₀ B V s)
    (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sphere (0 : ℂ) R ⊆ sourceCanonicalRootDomain hp hp1 φ.val →
      ∀ n : ℤ, canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
        (periodOnePotential_mem φ.val) n ≠ 0 →
      sourceAngularThetaFunctionalBracket hp hp1 h2p n s
        (sourceFullAbelianCubicContour hp hp1 W 0 R) φ.val - (2*(n : ℂ)*Real.pi)^2 =
          -(4/(2*Real.pi) : ℂ)*(∑' k : ℤ, A.moment n k 2 φ.val) := by
  obtain ⟨T,hT,hformula⟩ := A.exists_finiteGap_quadratic_contour_formula
    E.psi.toSourcePsiNormalizedComplexExtension φ hf
  refine ⟨T,hT,fun R hR hcircle n hn => ?_⟩
  rw [E.theta_cubicContour_eq_quadratic D h2p n φ (D.real_subset φ.property) hn
    0 R (hT.trans_le hR).le hcircle]
  exact hformula R hR hcircle n hn

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
