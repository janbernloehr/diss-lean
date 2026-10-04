import NLS.ZakharovShabat.SourceAbelianMomentLocalChart
import NLS.ComplexAnalysis.GlueHolomorphicCharts

/-! # Global normalized moments from compatible local circles

Real-centered isolating circles give the same integral on real sources.
The real-form identity theorem propagates this equality across complex
source-ball overlaps. Gluing therefore defines all normalized moments
on one open neighborhood of the whole real source locus.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourceAbelianMomentAtlas (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) where
  localChart : (φ : realTypeSourceLocus p) → SourceAbelianMomentLocalChart hp hp1 W s φ

namespace SourceAbelianMomentAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (A : SourceAbelianMomentAtlas hp hp1 W s)

def sourceBall (φ : realTypeSourceLocus p) : Set (CoeffPair p) :=
  ball φ.val (A.localChart φ).radius

def domain : Set (CoeffPair p) := ⋃ φ, A.sourceBall φ

def localMoment (φ : realTypeSourceLocus p) (n k : ℤ) (m : ℕ) (ψ : CoeffPair p) : ℂ :=
  sourceAbelianMomentCircle hp hp1 W n k m (s n ψ : Coeff p) ψ
    ((A.localChart φ).center k) ((A.localChart φ).contourRadius k)

/-- The normalized Section 20 moment, independent of the local chart
used to evaluate it. Its off-domain default is zero. -/
def moment (n k : ℤ) (m : ℕ) : CoeffPair p → ℂ :=
  NLS.ComplexAnalysis.glueHolomorphicCharts A.sourceBall (fun φ => A.localMoment φ n k m)

theorem isOpen_domain : IsOpen A.domain := isOpen_iUnion (fun _ => isOpen_ball)

theorem realType_subset_domain : realTypeSourceLocus p ⊆ A.domain := by
  intro φ hφ
  exact mem_iUnion.mpr ⟨⟨φ,hφ⟩,mem_ball_self (A.localChart ⟨φ,hφ⟩).radius_pos⟩

/-- Different fixed contour families agree on their full complex
source-ball overlap, not just on the real locus. -/
theorem localMoment_eqOn (φ θ : realTypeSourceLocus p) (n k : ℤ) (m : ℕ) :
    EqOn (A.localMoment φ n k m) (A.localMoment θ n k m) (A.sourceBall φ ∩ A.sourceBall θ) := by
  apply eqOn_sourceRealCenteredBalls_of_real_agreement hp φ θ _ _ _ _
    ((A.localChart φ).analytic n k m).differentiableOn
    ((A.localChart θ).analytic n k m).differentiableOn
  intro χ hχ
  obtain ⟨D⟩ := (A.localChart φ).charts χ.val hχ.1
  have hφ := (A.localChart φ).family χ.val hχ.1
  have hθ := (A.localChart θ).family χ.val hχ.2
  exact sourceAbelianMomentCircle_eq_of_realCentered_enclosingCircles hp hp1 W k m n k
    (s n χ.val : Coeff p) χ.val D χ.property _ _ _ _ (hφ.1 k) (hθ.1 k)
    (hφ.2 k).1 (hθ.2 k).1 (hφ.2 k).2.1 (hθ.2 k).2.1 (hφ.2 k).2.2.1 (hθ.2 k).2.2.1

theorem moment_eq_local (n k : ℤ) (m : ℕ) (φ : realTypeSourceLocus p) :
    EqOn (A.moment n k m) (A.localMoment φ n k m) (A.sourceBall φ) :=
  NLS.ComplexAnalysis.glueHolomorphicCharts_eq_on A.sourceBall _
    (fun χ θ => A.localMoment_eqOn χ θ n k m) φ

/-- Lemma 20.1(ii), including order zero, on one index-independent domain. -/
theorem analytic_moment (n k : ℤ) (m : ℕ) : AnalyticOnNhd ℂ (A.moment n k m) A.domain := by
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  have hnear := NLS.ComplexAnalysis.glueHolomorphicCharts_eventuallyEq A.sourceBall
    (fun χ => A.localMoment χ n k m) (fun _ => isOpen_ball)
    (fun χ θ => A.localMoment_eqOn χ θ n k m) φ ψ hφ
  exact ((A.localChart φ).analytic n k m ψ hφ).congr hnear.symm

/-- One valid all-index family represents every order and numerator
at each source in the global domain. -/
theorem circle_representation (ψ : CoeffPair p) (hψ : ψ ∈ A.domain) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ, sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
      ∀ (n k : ℤ) (m : ℕ), A.moment n k m ψ =
        sourceAbelianMomentCircle hp hp1 W n k m (s n ψ : Coeff p) ψ (c k) (R k) := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  exact ⟨(A.localChart φ).center,(A.localChart φ).contourRadius,
    (A.localChart φ).family ψ hφ,fun n k m => A.moment_eq_local n k m φ hφ⟩

theorem moment_zero_order (ψ : CoeffPair p) (hψ : ψ ∈ A.domain) (n k : ℤ) :
    A.moment n k 0 ψ = (2*Real.pi : ℂ)*(if k = n then 1 else 0) := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  exact (A.moment_eq_local n k 0 φ hφ).trans ((A.localChart φ).zero_order ψ hφ n k)

theorem moment_odd (ψ : CoeffPair p) (hψ : ψ ∈ A.domain) (n k : ℤ) (l : ℕ) :
    A.moment n k (2*l+1) ψ = 0 := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  exact (A.moment_eq_local n k (2*l+1) φ hφ).trans ((A.localChart φ).odd ψ hφ n k l)

theorem moment_succ_of_collapsed (ψ : CoeffPair p) (hψ : ψ ∈ A.domain) (n k : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k = 0) (m : ℕ) :
    A.moment n k (m+1) ψ = 0 := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  exact (A.moment_eq_local n k (m+1) φ hφ).trans ((A.localChart φ).collapsed ψ hφ n k hgap m)

/-- Neither atlas choice nor the primitive's ambient neighborhood
changes the moments on the overlap of the resulting source domains. -/
theorem moment_eqOn {V : Set (CoeffPair p)} (B : SourceAbelianMomentAtlas hp hp1 V s) (n k : ℤ) (m : ℕ) :
    EqOn (A.moment n k m) (B.moment n k m) (A.domain ∩ B.domain) := by
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ.1
  obtain ⟨θ,hθ⟩ := mem_iUnion.mp hψ.2
  rw [A.moment_eq_local n k m φ hφ,B.moment_eq_local n k m θ hθ]
  have he := eqOn_sourceRealCenteredBalls_of_real_agreement hp φ θ _ _
    (A.localMoment φ n k m) (B.localMoment θ n k m)
    ((A.localChart φ).analytic n k m).differentiableOn
    ((B.localChart θ).analytic n k m).differentiableOn (by
      intro χ hχ
      obtain ⟨D⟩ := (A.localChart φ).charts χ.val hχ.1
      have hA := (A.localChart φ).family χ.val hχ.1
      have hB := (B.localChart θ).family χ.val hχ.2
      obtain ⟨E⟩ := (B.localChart θ).charts χ.val hχ.2
      exact (sourceAbelianMomentCircle_eq_of_realCentered_enclosingCircles hp hp1 W k m n k
        (s n χ.val : Coeff p) χ.val D χ.property _ _ _ _ (hA.1 k) (hB.1 k)
        (hA.2 k).1 (hB.2 k).1 (hA.2 k).2.1 (hB.2 k).2.1 (hA.2 k).2.2.1 (hB.2 k).2.2.1).trans
          (sourceAbelianMomentCircle_independent_neighborhood hp hp1 W V n k m
            (s n χ.val : Coeff p) χ.val D E _ _ (hB.2 k).1.le (hB.2 k).2.2.2))
  exact he ⟨hφ,hθ⟩

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
