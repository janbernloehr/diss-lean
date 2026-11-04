import NLS.ZakharovShabat.SourceAbelianMomentCubicShift
import NLS.ZakharovShabat.SourceAbelianMomentFiniteGapContour
import NLS.ZakharovShabat.SourceFullAbelianFourthContourPoisson

/-! # The quartic contour bracket as a weighted second-moment sum -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The large cubic psi contour has the exact H₄ weighted-sum normalization. -/
theorem SourceAbelianMomentAtlas.exists_finiteGap_cubic_contour_formula
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sphere (0:ℂ) R ⊆ sourceCanonicalRootDomain hp hp1 φ.val →
      ∀ n : ℤ, canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
        (periodOnePotential_mem φ.val) n ≠ 0 →
      -(4*I/Real.pi:ℂ)*sourceAbelianMomentCircle hp hp1 W n 0 3 (s n φ.val) φ.val 0 R-
        (2*(n:ℂ)*Real.pi)^3 = -12*(∑' k : ℤ, (k:ℂ)*A.moment n k 2 φ.val) := by
  classical
  obtain ⟨T,hT,hdec⟩ := A.exists_finiteGap_contour_decomposition hs φ hf
  refine ⟨T,hT,fun R hR hcircle n hn => ?_⟩
  rw [hdec R hR hcircle n hn 0 3]
  apply A.cubic_contour_sum_renormalization φ φ.val
    (mem_ball_self (A.localChart φ).radius_pos) hf.toFinset
  · intro k hk
    by_contra hne
    exact hk ((Set.Finite.mem_toFinset hf).mpr hne)
  · exact (Set.Finite.mem_toFinset hf).mpr hn

end NLS.ZakharovShabat
