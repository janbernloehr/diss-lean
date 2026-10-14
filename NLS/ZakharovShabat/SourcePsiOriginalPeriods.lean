import NLS.ZakharovShabat.SourcePsiPiecewiseContour
import NLS.ZakharovShabat.SourcePsiIsolatingComplexNormalization

/-!
# Psi orthogonality on every original isolating family

The atlas's assigned disks have real centers and disjoint interiors.
Their original circles therefore have the projection separation needed
to compare them with any other original circle. The exact Kronecker
periods consequently hold on every original piecewise C¹ circuit.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourcePsiIsolatingComplexRootAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (CoeffPair p)}

/-- The atlas's assigned boundary has the geometry of an original period circle. -/
def assignedPeriodCircle (A : SourcePsiIsolatingComplexRootAtlas hp hp1 U)
    (φ : realTypeSourceLocus p) (ψ : CoeffPair p)
    (hψ : ψ ∈ A.toSourcePsiComplexRootAtlas.sourceBall φ) (m : ℤ) :
    SourceCriticalRootPeriodCircle hp hp1 ψ m := by
  let c := sourceIsolatingCenter hp hp1 φ.val (A.cutoff φ)
  let r := sourceIsolatingRadius hp hp1 φ.val (A.cutoff φ) (A.enlargement φ)
  have hc (k : ℤ) : ((c k).re:ℂ) = c k := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (sourceIsolatingCenter_im_eq_zero hp hp1 φ.val (A.cutoff φ) k).symm
  have hg (k : ℤ) : sourcePeriodicSegment hp hp1 ψ k ⊆ ball (c k) (r k) := by
    simpa only [sourceIsolatingDisc_eq_ball] using
      sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val ψ (A.cutoff φ) (A.enlargement φ) k
        (A.clusters φ ψ hψ k)
  have hr (k : ℤ) : 0 < r k := sourceIsolatingRadius_pos hp hp1 φ.val (A.cutoff φ)
    (A.enlargement φ) (A.enlargement_pos φ) k
  refine ⟨(c m).re,r m,hr m,by rw [hc]; exact hg m,?_⟩
  intro k hkm z hz
  have hd : Disjoint (ball ((c m).re:ℂ) (r m)) (ball ((c k).re:ℂ) (r k)) := by
    rw [hc,hc]
    simpa only [sourceIsolatingDisc_eq_ball] using A.disjoint φ m k hkm.symm
  exact re_separated_of_disjoint_realCenteredBalls (hr m) (hr k) hd (by rw [hc]; exact hg k hz)

/-- Every original period circle computes the atlas's normalized Kronecker period. -/
theorem periodCircle_orthogonality (A : SourcePsiIsolatingComplexRootAtlas hp hp1 U)
    (V : Set (CoeffPair p)) (hUV : U ⊆ V)
    (hdata : ∀ n, IsOpen (sourcePsiContourJointDomain hp hp1 V) ∧
      AnalyticOnNhd ℂ (sourcePsiContourIntegrandJoint hp hp1 n) (sourcePsiContourJointDomain hp hp1 V))
    (ψ : CoeffPair p) (hψ : ψ ∈ A.toSourcePsiComplexRootAtlas.domain) (n m : ℤ)
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    sourcePsiContour hp hp1 n (A.toSourcePsiComplexRootAtlas.branch n ψ : Coeff p)
      ψ (D.center:ℂ) D.radius = if m = n then 1 else 0 := by
  let B := A.toSourcePsiComplexRootAtlas
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  have hgap χ (hχ : χ ∈ B.sourceBall φ) (k : ℤ) :
      sourcePeriodicSegment hp hp1 χ k ⊆ sourceIsolatingDisc hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) k :=
    sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ.val χ (A.cutoff φ) (A.enlargement φ) k
      (A.clusters φ χ hχ k)
  rw [D.psiContour_eq (A.assignedPeriodCircle φ ψ hφ m) n]
  have hc : ((sourceIsolatingCenter hp hp1 φ.val (A.cutoff φ) m).re:ℂ) =
      sourceIsolatingCenter hp hp1 φ.val (A.cutoff φ) m := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (sourceIsolatingCenter_im_eq_zero hp hp1 φ.val (A.cutoff φ) m).symm
  change sourcePsiContour hp hp1 n (B.branch n ψ : Coeff p) ψ
    ((sourceIsolatingCenter hp hp1 φ.val (A.cutoff φ) m).re:ℂ)
      (sourceIsolatingRadius hp hp1 φ.val (A.cutoff φ) (A.enlargement φ) m) = _
  rw [hc]
  exact sourcePsi_orthogonality_on_isolating_ball hp hp1 φ (B.localBranch φ).sourceRadius
    (A.cutoff φ) (A.enlargement φ) (A.enlargement_pos φ) n (B.branch n)
    ((B.analytic n).mono (subset_iUnion B.sourceBall φ))
    (fun χ _ => B.eq_sourcePsiGapRoot_of_real n χ) hgap (A.disjoint φ)
    V ((A.sourceBall_subset φ).trans hUV) (hdata n).1 (hdata n).2 m hφ

/-- Arbitrary original circuits have the exact Kronecker period times their winding. -/
theorem circuit_orthogonality (A : SourcePsiIsolatingComplexRootAtlas hp hp1 U)
    (V : Set (CoeffPair p)) (hUV : U ⊆ V)
    (hdata : ∀ n, IsOpen (sourcePsiContourJointDomain hp hp1 V) ∧
      AnalyticOnNhd ℂ (sourcePsiContourIntegrandJoint hp hp1 n) (sourcePsiContourJointDomain hp hp1 V))
    {S : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 S D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ A.toSourcePsiComplexRootAtlas.domain) (hψS : ψ ∈ S)
    (n m : ℤ) (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (D m \ sourcePeriodicSegment hp hp1 ψ m)) :
    sourcePsiCircuit hp hp1 n (A.toSourcePsiComplexRootAtlas.branch n ψ : Coeff p) ψ Γ =
      (if m = n then 1 else 0)*Γ.windingIntegral
        (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) := by
  obtain ⟨a,r,hr,he⟩ := hD.discs m
  let P := hD.periodCircle ψ hψS m a r hr he
  rw [P.psiCircuit_eq_mul_winding n _ Γ (by
    change Γ.Inside (ball (a:ℂ) r \ sourcePeriodicSegment hp hp1 ψ m)
    rwa [← he]),A.periodCircle_orthogonality V hUV hdata ψ hψ n m P]

end SourcePsiIsolatingComplexRootAtlas
end NLS.ZakharovShabat
