import NLS.ZakharovShabat.SourcePrimitivePowerLocalChart
import NLS.ZakharovShabat.SourceGapContourComparison
import NLS.ComplexAnalysis.GlueHolomorphicCharts

/-! # Global primitive-power moments

Compatible fixed circles define the Section 21 moments on one open
neighborhood of every real source, simultaneously for all indices and
orders. The real-form identity theorem identifies complex overlaps.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Primitive powers have the same value on real-centered enclosing circles. -/
theorem sourcePrimitivePowerCircle_eq_of_realCentered_enclosingCircles
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (n : ℤ) (m : ℕ)
    (ψ : CoeffPair p) (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (hreal : IsRealType (CoeffPair.toMax p ψ))
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ) (hc₀ : c₀.im = 0) (hc₁ : c₁.im = 0)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₁ r₁)
    (hother₀ : closedBall c₀ r₀ ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hother₁ : closedBall c₁ r₁ ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourcePrimitivePowerCircle hp hp1 W n m ψ c₀ r₀ =
      sourcePrimitivePowerCircle hp hp1 W n m ψ c₁ r₁ := by
  unfold sourcePrimitivePowerCircle
  congr 1
  exact sourceGapCircleIntegral_eq_of_realCentered_enclosingCircles hp hp1 n ψ _
    (fun z hz => (sourceFullAbelianPrimitive_spectral_analytic D n z
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ hz)).pow m)
    hreal c₀ c₁ r₀ r₁ hc₀ hc₁ hr₀ hr₁ hseg₀ hseg₁ hother₀ hother₁

/-- The ambient primitive neighborhood does not affect a valid circle. -/
theorem sourcePrimitivePowerCircle_independent_neighborhood
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W V : Set (CoeffPair p)) (n : ℤ) (m : ℕ)
    (ψ : CoeffPair p) (D : SourceAbelianSpectralChart hp hp1 W ψ)
    (E : SourceAbelianSpectralChart hp hp1 V ψ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    sourcePrimitivePowerCircle hp hp1 W n m ψ c R =
      sourcePrimitivePowerCircle hp hp1 V n m ψ c R := by
  unfold sourcePrimitivePowerCircle
  congr 1
  apply circleIntegral.integral_congr hR
  intro z hz
  exact congrArg (fun v : ℂ => v^m) (sourceFullAbelianPrimitive_independent_neighborhood D E n z
    (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ (hc hz)))

structure SourcePrimitivePowerAtlas (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) where
  localChart : (φ : realTypeSourceLocus p) → SourcePrimitivePowerLocalChart hp hp1 W φ

namespace SourcePrimitivePowerAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (A : SourcePrimitivePowerAtlas hp hp1 W)

def sourceBall (φ : realTypeSourceLocus p) : Set (CoeffPair p) :=
  ball φ.val (A.localChart φ).radius

def domain : Set (CoeffPair p) := ⋃ φ, A.sourceBall φ

def localMoment (φ : realTypeSourceLocus p) (n : ℤ) (m : ℕ) (ψ : CoeffPair p) : ℂ :=
  sourcePrimitivePowerCircle hp hp1 W n m ψ
    ((A.localChart φ).center n) ((A.localChart φ).contourRadius n)

/-- The primitive-power Section 21 moment, independent of the local chart
used to evaluate it. Its off-domain default is zero. -/
def moment (n : ℤ) (m : ℕ) : CoeffPair p → ℂ :=
  NLS.ComplexAnalysis.glueHolomorphicCharts A.sourceBall (fun φ => A.localMoment φ n m)

theorem isOpen_domain : IsOpen A.domain := isOpen_iUnion (fun _ => isOpen_ball)

theorem realType_subset_domain : realTypeSourceLocus p ⊆ A.domain := by
  intro φ hφ
  exact mem_iUnion.mpr ⟨⟨φ,hφ⟩,mem_ball_self (A.localChart ⟨φ,hφ⟩).radius_pos⟩

/-- Different fixed contour families agree on their full complex
source-ball overlap, not just on the real locus. -/
theorem localMoment_eqOn (φ θ : realTypeSourceLocus p) (n : ℤ) (m : ℕ) :
    EqOn (A.localMoment φ n m) (A.localMoment θ n m) (A.sourceBall φ ∩ A.sourceBall θ) := by
  apply eqOn_sourceRealCenteredBalls_of_real_agreement hp φ θ _ _ _ _
    ((A.localChart φ).analytic n m).differentiableOn
    ((A.localChart θ).analytic n m).differentiableOn
  intro χ hχ
  obtain ⟨D⟩ := (A.localChart φ).charts χ.val hχ.1
  have hφ := (A.localChart φ).family χ.val hχ.1
  have hθ := (A.localChart θ).family χ.val hχ.2
  exact sourcePrimitivePowerCircle_eq_of_realCentered_enclosingCircles hp hp1 W n m
    χ.val D χ.property _ _ _ _ (hφ.1 n) (hθ.1 n)
    (hφ.2 n).1 (hθ.2 n).1 (hφ.2 n).2.1 (hθ.2 n).2.1 (hφ.2 n).2.2.1 (hθ.2 n).2.2.1

theorem moment_eq_local (n : ℤ) (m : ℕ) (φ : realTypeSourceLocus p) :
    EqOn (A.moment n m) (A.localMoment φ n m) (A.sourceBall φ) :=
  NLS.ComplexAnalysis.glueHolomorphicCharts_eq_on A.sourceBall _
    (fun χ θ => A.localMoment_eqOn χ θ n m) φ

/-- Lemma 21.1(i), including order zero, on one index-independent domain. -/
theorem analytic_moment (n : ℤ) (m : ℕ) : AnalyticOnNhd ℂ (A.moment n m) A.domain := by
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  have hnear := NLS.ComplexAnalysis.glueHolomorphicCharts_eventuallyEq A.sourceBall
    (fun χ => A.localMoment χ n m) (fun _ => isOpen_ball)
    (fun χ θ => A.localMoment_eqOn χ θ n m) φ ψ hφ
  exact ((A.localChart φ).analytic n m ψ hφ).congr hnear.symm

/-- One valid all-index family represents every order and index
at each source in the global domain. -/
theorem circle_representation (ψ : CoeffPair p) (hψ : ψ ∈ A.domain) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ, sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
      ∀ (n : ℤ) (m : ℕ), A.moment n m ψ =
        sourcePrimitivePowerCircle hp hp1 W n m ψ (c n) (R n) := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  exact ⟨(A.localChart φ).center,(A.localChart φ).contourRadius,
    (A.localChart φ).family ψ hφ,fun n m => A.moment_eq_local n m φ hφ⟩

/-- Every even moment vanishes, including order zero. -/
theorem moment_even (ψ : CoeffPair p) (hψ : ψ ∈ A.domain) (n : ℤ) (m : ℕ) :
    A.moment n (2*m) ψ = 0 := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  exact (A.moment_eq_local n (2*m) φ hφ).trans ((A.localChart φ).even ψ hφ n m)

/-- Every primitive-power moment vanishes at a collapsed gap. -/
theorem moment_of_collapsed (ψ : CoeffPair p) (hψ : ψ ∈ A.domain) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) (m : ℕ) :
    A.moment n m ψ = 0 := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  exact (A.moment_eq_local n m φ hφ).trans ((A.localChart φ).collapsed ψ hφ n hgap m)

/-- Neither atlas choice nor the primitive's ambient neighborhood
changes the moments on the overlap of the resulting source domains. -/
theorem moment_eqOn {V : Set (CoeffPair p)} (B : SourcePrimitivePowerAtlas hp hp1 V) (n : ℤ) (m : ℕ) :
    EqOn (A.moment n m) (B.moment n m) (A.domain ∩ B.domain) := by
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ.1
  obtain ⟨θ,hθ⟩ := mem_iUnion.mp hψ.2
  rw [A.moment_eq_local n m φ hφ,B.moment_eq_local n m θ hθ]
  have he := eqOn_sourceRealCenteredBalls_of_real_agreement hp φ θ _ _
    (A.localMoment φ n m) (B.localMoment θ n m)
    ((A.localChart φ).analytic n m).differentiableOn
    ((B.localChart θ).analytic n m).differentiableOn (by
      intro χ hχ
      obtain ⟨D⟩ := (A.localChart φ).charts χ.val hχ.1
      have hA := (A.localChart φ).family χ.val hχ.1
      have hB := (B.localChart θ).family χ.val hχ.2
      obtain ⟨E⟩ := (B.localChart θ).charts χ.val hχ.2
      exact (sourcePrimitivePowerCircle_eq_of_realCentered_enclosingCircles hp hp1 W n m
        χ.val D χ.property _ _ _ _ (hA.1 n) (hB.1 n)
        (hA.2 n).1 (hB.2 n).1 (hA.2 n).2.1 (hB.2 n).2.1 (hA.2 n).2.2.1 (hB.2 n).2.2.1).trans
          (sourcePrimitivePowerCircle_independent_neighborhood hp hp1 W V n m
            χ.val D E _ _ (hB.2 n).1.le (hB.2 n).2.2.2))
  exact he ⟨hφ,hθ⟩

end SourcePrimitivePowerAtlas

/-- An actual atlas, rather than an assumed family of moments, exists at
all finite source exponents above one. -/
theorem exists_sourcePrimitivePowerAtlas (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      Nonempty (SourcePrimitivePowerAtlas hp hp1 W) := by
  obtain ⟨W,hW,hreal,hL⟩ := exists_sourcePrimitivePower_localCharts hp hp1
  exact ⟨W,hW,hreal,⟨⟨fun φ => Classical.choice (hL φ)⟩⟩⟩

end NLS.ZakharovShabat
