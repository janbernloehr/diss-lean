import NLS.KdV.HillAbelianJointFrequencyDomain
import NLS.ComplexAnalysis.ParametricQuadraticCauchySolution
import NLS.ZakharovShabat.SourceAngularCauchyEquation

/-! Actual joint annular/Cauchy charts for Hill Abelian integration.
EVERY complex source and EVERY point in its original assigned disc is
covered. Each geometry/source chart precedes ALL numerator indices;
only the differential equation excludes the on-index nonzero period. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

structure HillAbelianCauchyChart (P : HillProductEquationPatch) (m : ℕ+) where
  source : Set PeriodOneHminusOne
  source_open : IsOpen source
  subset : source ⊆ P.source
  inner : ℝ
  outer : ℝ
  inner_pos : 0 < inner
  inner_lt_outer : inner < outer
  outer_lt_assigned : outer < P.radii ((m:ℕ):ℤ)
  gap_enclosed : ∀ q ∈ source, sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) ⊆
    ball (P.centers ((m:ℕ):ℤ):ℂ) inner

namespace HillAbelianCauchyChart
variable {P : HillProductEquationPatch} {m : ℕ+}

def solution (C : HillAbelianCauchyChart P m) (n : ℕ+) (ρ : ℝ) : ℂ × PeriodOneHminusOne → ℂ :=
  parametricQuadraticCauchySolution (P.abelianFrequencyDifferential n)
    (fun t => sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi t.2) ((m:ℕ):ℤ) t.1)
    (P.centers ((m:ℕ):ℤ):ℂ) C.inner C.outer ρ

theorem closed_annulus_mem_rootDomain (C : HillAbelianCauchyChart P m)
    (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ (closedBall (P.centers ((m:ℕ):ℤ):ℂ) C.outer \ ball (P.centers ((m:ℕ):ℤ):ℂ) C.inner) ×ˢ C.source) :
    t ∈ P.abelianJointFrequencyDomain := by
  refine ⟨C.subset ht.2,?_⟩
  let D := P.isolating.periodCircle (P.sourcePsi t.2) (P.image t.2 (C.subset ht.2)).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  intro j
  by_cases hj : j = ((m:ℕ):ℤ)
  · subst j
    exact fun h => ht.1.2 (C.gap_enclosed t.2 ht.2 h)
  · exact D.closedBall_subset_omittedDomain (closedBall_subset_closedBall C.outer_lt_assigned.le ht.1.1) j hj

theorem analytic_differential_annulus (C : HillAbelianCauchyChart P m) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.abelianFrequencyDifferential n)
      ((closedBall (P.centers ((m:ℕ):ℤ):ℂ) C.outer \ ball (P.centers ((m:ℕ):ℤ):ℂ) C.inner) ×ˢ C.source) :=
  (P.analytic_abelianFrequencyDifferential_joint n).mono C.closed_annulus_mem_rootDomain

theorem analytic_root_annulus (C : HillAbelianCauchyChart P m) :
    AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne => sourceStandardRoot (by norm_num) (by norm_num)
      (P.sourcePsi t.2) ((m:ℕ):ℤ) t.1)
      ((ball (P.centers ((m:ℕ):ℤ):ℂ) C.outer \ closedBall (P.centers ((m:ℕ):ℤ):ℂ) C.inner) ×ˢ C.source) := by
  intro t ht
  have hdom := C.closed_annulus_mem_rootDomain t ⟨⟨ball_subset_closedBall ht.1.1,fun h => ht.1.2 (ball_subset_closedBall h)⟩,ht.2⟩
  exact P.analytic_abelianSelectedRoot m t ⟨hdom.1,hdom.2 _⟩

theorem analytic_solution (C : HillAbelianCauchyChart P m) (n : ℕ+) (ρ : ℝ)
    (hrρ : C.inner < ρ) (hρR : ρ < C.outer) :
    AnalyticOnNhd ℂ (C.solution n ρ) (ball (P.centers ((m:ℕ):ℤ):ℂ) ρ ×ˢ C.source) := by
  apply analyticOnNhd_parametricQuadraticCauchySolution _ _ _ C.inner C.outer ρ C.inner_pos hrρ hρR
    C.source C.source_open (C.analytic_differential_annulus n) C.analytic_root_annulus
  intro t ht
  exact sourceStandardRoot_ne_zero_off_segment (by norm_num) (by norm_num) (P.sourcePsi t.2) ((m:ℕ):ℤ) t.1
    (fun h => ht.1.2 (ball_subset_closedBall (C.gap_enclosed t.2 ht.2 h)))

theorem solution_equation (C : HillAbelianCauchyChart P m) (n : ℕ+) (hmn : m ≠ n)
    (ρ : ℝ) (hrρ : C.inner < ρ) (hρR : ρ < C.outer) (q : PeriodOneHminusOne) (hq : q ∈ C.source)
    (z : ℂ) (hz : z ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) ρ) :
    sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z*
        deriv (fun w => C.solution n ρ (w,q)) z+
      (z-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))*C.solution n ρ (z,q) =
        P.abelianGapNumerator n m (z,q) := by
  apply parametricQuadraticCauchySolution_equation _ _ (P.abelianGapNumerator n m) _ _ _ C.inner C.outer ρ
    C.inner_pos hrρ hρR C.source C.source_open (C.analytic_differential_annulus n) C.analytic_root_annulus q hq
  · intro w hw
    exact sourceStandardRoot_ne_zero_off_segment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) w
      (fun h => hw.2 (ball_subset_closedBall (C.gap_enclosed q hq h)))
  · intro w hw
    change sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) w^2 =
      sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) w
    rw [sourceAngularSelectedPolynomial_eq_endpoint_factor]
    exact sourceStandardRoot_sq_of_not_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) w
      (fun h => hw.2 (ball_subset_closedBall (C.gap_enclosed q hq h)))
  · intro w hw
    exact P.abelianFrequencyDifferential_eq_gap_quotient n m (w,q)
      (C.closed_annulus_mem_rootDomain (w,q) ⟨⟨ball_subset_closedBall hw.1,fun h => hw.2 (ball_subset_closedBall h)⟩,hq⟩).2
  · intro w hw
    exact (P.analytic_abelianGapNumerator_on_patch n m (w,q)
      ⟨closedBall_subset_closedBall (hρR.trans C.outer_lt_assigned).le hw,C.subset hq⟩).comp
      (f := fun t : ℂ => (t,q)) (analyticAt_id.prod analyticAt_const)
  · let D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) := {
      center := P.centers ((m:ℕ):ℤ)
      radius := C.inner
      radius_pos := C.inner_pos
      gap := C.gap_enclosed q hq
      other := by
        intro j hj w hw
        let E := P.isolating.periodCircle (P.sourcePsi q) (P.image q (C.subset hq)).2 ((m:ℕ):ℤ)
          (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
        rcases E.other j hj w hw with h | h
        · change w.re < P.centers ((m:ℕ):ℤ)-P.radii ((m:ℕ):ℤ) at h
          exact Or.inl (by linarith [C.inner_lt_outer,C.outer_lt_assigned])
        · change P.centers ((m:ℕ):ℤ)+P.radii ((m:ℕ):ℤ) < w.re at h
          exact Or.inr (by linarith [C.inner_lt_outer,C.outer_lt_assigned]) }
    have hp := P.abelianFrequencyDifferential_period n m q (C.subset hq) D
    rw [if_neg hmn] at hp
    exact (mul_eq_zero.mp hp).resolve_left (inv_ne_zero (by simp [Real.pi_ne_zero]))
  · exact hz

end HillAbelianCauchyChart

theorem exists_hillAbelianCauchyChart (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (z : ℂ)
    (hz : z ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) :
    ∃ C : HillAbelianCauchyChart P m, q ∈ C.source ∧ ∃ ρ : ℝ, C.inner < ρ ∧ ρ < C.outer ∧
      z ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) ρ := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  obtain ⟨a,b,ha,hab,hbT,hseg⟩ := exists_nested_radii_of_segment_subset_ball _ _ (D.center:ℂ) D.radius D.gap
  let s := max a (dist z (D.center:ℂ))
  have hsT : s < D.radius := max_lt (hab.trans hbT) hz
  have hs : 0 < s := ha.trans_le (le_max_left _ _)
  let r := (s+D.radius)/2
  let R := (r+D.radius)/2
  have hsr : s < r := by dsimp [r]; linarith
  have hrT : r < D.radius := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [R]; linarith
  have hRT : R < D.radius := by dsimp [R]; linarith
  have hgapr := hseg.trans (ball_subset_ball ((le_max_left _ _).trans hsr.le))
  have hsphere := sourceCanonicalRootDomain_of_enclosingCircle (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)
    (D.center:ℂ) r hgapr ((closedBall_subset_closedBall hrT.le).trans D.closedBall_subset_omittedDomain)
  have hev := P.eventually_abelian_gap_subset_ball m q hq (D.center:ℂ) r hgapr hsphere
  obtain ⟨U,hUsub,hU,hqU⟩ := _root_.mem_nhds_iff.mp (hev.and (P.source_open.mem_nhds hq))
  let C : HillAbelianCauchyChart P m := ⟨U,hU,fun y hy => (hUsub hy).2,r,R,hs.trans hsr,hrR,hRT,fun y hy => (hUsub hy).1⟩
  refine ⟨C,hqU,(r+R)/2,by dsimp [C]; linarith,by dsimp [C]; linarith,?_⟩
  exact mem_ball.mpr ((le_max_right _ _).trans_lt (hsr.trans (by linarith : r < (r+R)/2)))

end NLS.KdV
