import NLS.ZakharovShabat.SourceDiagonalLaurentGeometry
import NLS.ZakharovShabat.SourceLaurentActionAnalytic
import NLS.ZakharovShabat.SourceCriticalRootRatioJointAnalytic

/-! # All integer Laurent levels on one diagonal-centered source ball

The center is any real diagonal in the original coefficient space. One
source ball and one infinite family of actual circles support every
noncentral index and every integer level, including level zero.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceRealLaurentAction (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n k : ℤ) : ℂ :=
  (((canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n).re /
    Real.pi * ∫ θ in (0 : ℝ)..Real.pi,
      (realGapAffinePoint hp hp1 φ.val n (Real.cos θ))^(k-1) *
        (Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ) : ℝ) : ℂ)

structure SourceDiagonalLaurentLocalChart (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realDiagonalSourceLocus p) where
  radius : ℝ
  radius_pos : 0 < radius
  ambient : Set (CoeffPair p)
  cauchy : SourceFullAbelianUniformCauchyFamily hp hp1 ambient
  source_eq : cauchy.discs.source.val = φ.val
  source_subset : ball φ.val radius ⊆ ball cauchy.discs.source.val cauchy.discs.sourceRadius
  root_domain_open : IsOpen (sourceCanonicalRootJointDomain hp hp1 (ball φ.val radius))

namespace SourceDiagonalLaurentLocalChart
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : realDiagonalSourceLocus p}
variable (C : SourceDiagonalLaurentLocalChart hp hp1 φ)

def contourRadius (n : ℤ) : ℝ := (C.cauchy.discs.inner n+C.cauchy.discs.outer n)/2

theorem contourRadius_bounds (n : ℤ) :
    C.cauchy.discs.inner n ≤ C.contourRadius n ∧ C.contourRadius n < C.cauchy.discs.outer n := by
  dsimp only [contourRadius]
  constructor <;> linarith [C.cauchy.discs.inner_lt n]

theorem contourRadius_pos (n : ℤ) : 0 < C.contourRadius n :=
  (C.cauchy.discs.inner_pos n).trans_le (C.contourRadius_bounds n).1

theorem zero_not_mem_contour_disc (n : ℤ) (hn : n ≠ 0) :
    (0 : ℂ) ∉ closedBall (C.cauchy.discs.center n) (C.contourRadius n) := by
  have hd : C.cauchy.discs.source.val.fst = C.cauchy.discs.source.val.snd := by
    rw [C.source_eq]
    exact φ.property.2
  intro hz
  exact C.cauchy.zero_not_mem_noncentral_disc_of_diagonal hd n hn
    (closedBall_subset_closedBall (C.contourRadius_bounds n).2.le hz)

def action (n k : ℤ) (ψ : CoeffPair p) : ℂ :=
  sourceLaurentPrimitiveCircle hp hp1 C.ambient n k ψ (C.cauchy.discs.center n) (C.contourRadius n)

theorem analytic_action (n k : ℤ) (hn : n ≠ 0) :
    AnalyticOnNhd ℂ (C.action n k) (ball φ.val C.radius) := by
  apply sourceLaurentPrimitiveCircle_analyticOnNhd hp hp1 C.ambient _ n k isOpen_ball
    C.root_domain_open ((C.cauchy.full_analytic n).mono (fun t ht => ⟨C.source_subset ht.1,ht.2⟩))
    _ _ (C.contourRadius_pos n).le
    (fun ψ hψ => C.cauchy.intermediate_circle_root n ψ (C.source_subset hψ) _
      (C.contourRadius_bounds n).1 (C.contourRadius_bounds n).2)
  exact fun hz => C.zero_not_mem_contour_disc n hn (sphere_subset_closedBall hz)

theorem action_eq_real (ψ : realTypeSourceSubmodule p) (hψ : ψ.val ∈ ball φ.val C.radius)
    (n k : ℤ) (hn : n ≠ 0) :
    C.action n k ψ.val = sourceRealLaurentAction hp hp1 ψ n k :=
  C.cauchy.laurentPrimitiveCircle_eq_realIntegral n k ψ (C.source_subset hψ) _
    (C.contourRadius_bounds n).1 (C.contourRadius_bounds n).2 (C.zero_not_mem_contour_disc n hn)

theorem action_eq_real_contour (ψ : realTypeSourceSubmodule p)
    (hψ : ψ.val ∈ ball φ.val C.radius) (n k : ℤ) (hn : n ≠ 0) :
    C.action n k ψ.val = sourceLaurentActionContour hp hp1 ψ k
      (PiecewiseC1Loop.circle (C.cauchy.discs.center n) (C.contourRadius n)) := by
  obtain ⟨E⟩ := C.cauchy.charts ψ.val (C.source_subset hψ)
  exact (sourceLaurentActionContour_circle_eq_local hp hp1 C.ambient n k ψ E _ _
    (C.contourRadius_pos n).le
    (C.cauchy.intermediate_circle_root n ψ.val (C.source_subset hψ) _
      (C.contourRadius_bounds n).1 (C.contourRadius_bounds n).2)
    (C.zero_not_mem_contour_disc n hn)).symm

end SourceDiagonalLaurentLocalChart

theorem exists_sourceDiagonalLaurentLocalChart (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realDiagonalSourceLocus p) : Nonempty (SourceDiagonalLaurentLocalChart hp hp1 φ) := by
  obtain ⟨W,_,_,hC⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hCφ⟩ := hC ⟨φ.val,φ.property.1⟩
  obtain ⟨G,hG,_,hrealG,hD,_⟩ := exists_global_sourceCriticalRootRatio_jointAnalytic hp hp1
  have hφC : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hCφ]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨δ,hδ,hsub⟩ := Metric.isOpen_iff.mp (hG.inter isOpen_ball) φ.val
    ⟨hrealG φ.property.1,hφC⟩
  have hU : IsOpen (sourceCanonicalRootJointDomain hp hp1 (ball φ.val δ)) := by
    have he : sourceCanonicalRootJointDomain hp hp1 (ball φ.val δ) =
        sourceCanonicalRootJointDomain hp hp1 G ∩ (Prod.snd ⁻¹' ball φ.val δ) := by
      ext t
      exact ⟨fun ht => ⟨⟨(hsub ht.1).1,ht.2⟩,ht.1⟩,fun ht => ⟨ht.2,ht.1.2⟩⟩
    rw [he]
    exact hD.inter (isOpen_ball.preimage continuous_snd)
  exact ⟨⟨δ,hδ,W,C,congrArg Subtype.val hCφ,fun ψ hψ => (hsub hψ).2,hU⟩⟩

end NLS.ZakharovShabat
