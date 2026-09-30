import NLS.ZakharovShabat.SourcePsiAssignedCircleFamily
import NLS.ZakharovShabat.SourcePsiRealNormalization
import NLS.ZakharovShabat.SourcePsiComplexContourAnalytic
import NLS.ZakharovShabat.SourcePsiIsolatingComplexRootAtlas

/-!
# Exact psi orthogonality on complex isolating source balls

Each assigned contour is fixed on its entire real-centered source ball.
Its normalized period is holomorphic after composing with the analytic
root branch. Exact real orthogonality and the Banach real-form identity
therefore give the same Kronecker periods throughout that ball. The
glued all-index root atlas inherits these periods on its full domain.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Real agreement of an analytic root branch forces exact contour
orthogonality throughout a real-centered complex source ball with
fixed assigned gap discs. -/
theorem sourcePsi_orthogonality_on_isolating_ball
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) (δ : ℝ)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) (n : ℤ)
    (s : CoeffPair p → DeletedCoeff p n)
    (hs : AnalyticOnNhd ℂ s (ball φ.val δ))
    (hreal : ∀ χ : realTypeSourceLocus p, χ.val ∈ ball φ.val δ →
      s χ.val = sourcePsiGapRoot hp hp1 n χ)
    (hgap : ∀ ψ ∈ ball φ.val δ, ∀ m, sourcePeriodicSegment hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ.val N ε m)
    (hdisj : ∀ m k, m ≠ k → Disjoint (sourceIsolatingDisc hp hp1 φ.val N ε m)
      (sourceIsolatingDisc hp hp1 φ.val N ε k))
    (U : Set (CoeffPair p)) (hball : ball φ.val δ ⊆ U)
    (hD : IsOpen (sourcePsiContourJointDomain hp hp1 U))
    (hF : AnalyticOnNhd ℂ (sourcePsiContourIntegrandJoint hp hp1 n)
      (sourcePsiContourJointDomain hp hp1 U)) (m : ℤ) :
    EqOn (fun ψ => sourcePsiContour hp hp1 n (s ψ : Coeff p) ψ
      (sourceIsolatingCenter hp hp1 φ.val N m) (sourceIsolatingRadius hp hp1 φ.val N ε m))
      (fun _ => if m = n then (1 : ℂ) else 0) (ball φ.val δ) := by
  let f : CoeffPair p → ℂ := fun ψ => sourcePsiContour hp hp1 n (s ψ : Coeff p) ψ
    (sourceIsolatingCenter hp hp1 φ.val N m) (sourceIsolatingRadius hp hp1 φ.val N ε m)
  have hfamily ψ (hψ : ψ ∈ ball φ.val δ) :=
    sourcePsiAssignedCircleFamily hp hp1 φ.val ψ N ε hε (hgap ψ hψ) hdisj
  have hf : DifferentiableOn ℂ f (ball φ.val δ) := by
    intro ψ hψ
    let i : DeletedCoeff p n →L[ℂ] Coeff p := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL
    have hroot : AnalyticAt ℂ (fun χ => (s χ : Coeff p)) ψ :=
      (i.analyticAt _).comp (hs ψ hψ)
    have hpar : AnalyticAt ℂ (fun χ => ((s χ : Coeff p),χ)) ψ := hroot.prod analyticAt_id
    have hcontour := analyticAt_sourcePsiContour_of_contour_domain hp hp1 n
      (s ψ : Coeff p) ψ (sourceIsolatingCenter hp hp1 φ.val N m)
      (sourceIsolatingRadius hp hp1 φ.val N ε m) ((hfamily ψ hψ).2 m).1.le
      U (hball hψ) hD hF ((hfamily ψ hψ).2 m).2.2.2
    exact (hcontour.comp (f := fun χ => ((s χ : Coeff p),χ)) hpar).differentiableAt.differentiableWithinAt
  have heq := eqOn_sourceRealCenteredBalls_of_real_agreement hp φ φ δ δ f
    (fun _ => if m = n then (1 : ℂ) else 0) hf (differentiableOn_const _) (by
      intro χ hχ
      dsimp only [f]
      rw [hreal χ hχ.1]
      exact sourcePsiGapRoot_contour_orthogonality hp hp1 n χ _ _ (hfamily χ.val hχ.1) m)
  intro ψ hψ
  exact heq ⟨hψ,hψ⟩

namespace SourcePsiIsolatingComplexRootAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (CoeffPair p)}

/-- The original assigned circles give simultaneous exact Kronecker
periods for every deleted index on the atlas's entire complex domain. -/
theorem contour_orthogonality (A : SourcePsiIsolatingComplexRootAtlas hp hp1 U)
    (V : Set (CoeffPair p)) (hUV : U ⊆ V)
    (hdata : ∀ n, IsOpen (sourcePsiContourJointDomain hp hp1 V) ∧
      AnalyticOnNhd ℂ (sourcePsiContourIntegrandJoint hp hp1 n)
        (sourcePsiContourJointDomain hp hp1 V))
    (ψ : CoeffPair p) (hψ : ψ ∈ A.toSourcePsiComplexRootAtlas.domain) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
      ∀ n m, sourcePsiContour hp hp1 n (A.toSourcePsiComplexRootAtlas.branch n ψ : Coeff p)
        ψ (c m) (R m) = if m = n then 1 else 0 := by
  let B := A.toSourcePsiComplexRootAtlas
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  have hgap χ (hχ : χ ∈ B.sourceBall φ) (m : ℤ) :
      sourcePeriodicSegment hp hp1 χ m ⊆ sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) m :=
    sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val χ (A.cutoff φ) (A.enlargement φ) m
      (A.clusters φ χ hχ m)
  refine ⟨sourceIsolatingCenter hp hp1 φ.val (A.cutoff φ),
    sourceIsolatingRadius hp hp1 φ.val (A.cutoff φ) (A.enlargement φ),
    sourcePsiAssignedCircleFamily hp hp1 φ.val ψ (A.cutoff φ) (A.enlargement φ)
      (A.enlargement_pos φ) (hgap ψ hφ) (A.disjoint φ),?_⟩
  intro n m
  exact sourcePsi_orthogonality_on_isolating_ball hp hp1 φ (B.localBranch φ).sourceRadius
    (A.cutoff φ) (A.enlargement φ) (A.enlargement_pos φ) n (B.branch n)
    ((B.analytic n).mono (subset_iUnion B.sourceBall φ))
    (fun χ _ => B.eq_sourcePsiGapRoot_of_real n χ) hgap (A.disjoint φ)
    V ((A.sourceBall_subset φ).trans hUV) (hdata n).1 (hdata n).2 m hφ

end SourcePsiIsolatingComplexRootAtlas
end NLS.ZakharovShabat
