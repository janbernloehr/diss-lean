import NLS.KdV.HillCompletePhaseReality
import NLS.KdV.HillAbelianCartesian

/-! A single-valued actual complete phase square on the original
open selected-gap locus. It includes the complete intrinsic correction
and equals the doubled exponential of every actual local phase chart. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

def hillHminusCompletePhaseDomain (n : ℕ+) : Set PeriodOneHminusOne :=
  {q | q ∈ hillHminusOffIndexAnalyticDomain ∧ hillHminusCanonicalGapSquare n q ≠ 0}

def hillHminusCompletePhaseSquare (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  hillHminusAbelianCartesianPlus n q/hillHminusAbelianCartesianMinus n q

theorem isOpen_hillHminusCompletePhaseDomain (n : ℕ+) : IsOpen (hillHminusCompletePhaseDomain n) :=
  ((analyticOnNhd_hillHminusCanonicalGapSquare n).mono
    (hillHminusOffIndexAnalyticDomain_subset_physical.trans hillHminusPhysicalAbelianDomain_subset_gapDomain)).continuousOn.isOpen_inter_preimage
      isOpen_hillHminusOffIndexAnalyticDomain (isOpen_ne (x := (0:ℂ)))

theorem hillHminusAbelianCartesian_ne_zero_on_completePhaseDomain (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCompletePhaseDomain n) :
    hillHminusAbelianCartesianPlus n q ≠ 0 ∧ hillHminusAbelianCartesianMinus n q ≠ 0 :=
  mul_ne_zero_iff.mp ((hillHminusAbelianCartesian_product n q hq.1).symm ▸ hq.2)

theorem analyticOnNhd_hillHminusCompletePhaseSquare (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCompletePhaseSquare n) (hillHminusCompletePhaseDomain n) := by
  intro q hq
  exact (analyticOnNhd_hillHminusAbelianCartesianPlus n q hq.1).div
    (analyticOnNhd_hillHminusAbelianCartesianMinus n q hq.1)
    (hillHminusAbelianCartesian_ne_zero_on_completePhaseDomain n q hq).2

theorem hillHminusCompletePhaseSquare_ne_zero (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCompletePhaseDomain n) : hillHminusCompletePhaseSquare n q ≠ 0 :=
  div_ne_zero (hillHminusAbelianCartesian_ne_zero_on_completePhaseDomain n q hq).1
    (hillHminusAbelianCartesian_ne_zero_on_completePhaseDomain n q hq).2

namespace HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+}

theorem real_mem_completePhaseDomain (C : HillPhysicalOnIndexPhaseChart P n)
    (q : PeriodOneHminusOne) (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q) :
    q ∈ hillHminusCompletePhaseDomain n :=
  ⟨real_mem_hillHminusOffIndexAnalyticDomain q hr,C.original_gap_ne_zero_of_real q hq hr⟩

theorem eventually_completePhaseSquare_eq_exp (C : HillPhysicalOnIndexPhaseChart P n)
    (q : PeriodOneHminusOne) (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q) :
    hillHminusCompletePhaseSquare n =ᶠ[𝓝 q] (fun p => Complex.exp (2*I*C.completePhase p)) := by
  obtain ⟨r,hrpos,hsub,heq⟩ := exists_common_intrinsic_diagonal_Cartesian_patch_ball P q (C.subset hq).1 hr
  filter_upwards [isOpen_ball.mem_nhds (show q ∈ ball q r from mem_ball_self hrpos),
    C.source_open.mem_nhds hq,(isOpen_hillHminusCompletePhaseDomain n).mem_nhds
      (C.real_mem_completePhaseDomain q hq hr)] with p hp hC hdom
  rcases C.identities p hC with ⟨_,hpoint,hroot,hphase,_⟩
  have hs := P.physicalOnIndexPhaseSquare_eq_exp_on_cover n p (C.subset hC) hdom.2
    (C.halfGap p) (C.angle p) hpoint hroot
  rw [← hphase] at hs
  have hPhi : hillHminusCompletePhaseSquare n p = P.physicalOnIndexPhaseSquare n p*
      Complex.exp (2*I*hillHminusOffIndexAbelianCorrection n p) := by
    dsimp only [hillHminusCompletePhaseSquare,hillHminusAbelianCartesianPlus,hillHminusAbelianCartesianMinus]
    rw [(heq n p hp).1,(heq n p hp).2]
    rw [show 2*I*hillHminusOffIndexAbelianCorrection n p =
      I*hillHminusOffIndexAbelianCorrection n p-(-I*hillHminusOffIndexAbelianCorrection n p) by ring,Complex.exp_sub]
    dsimp only [HillProductEquationPatch.physicalOnIndexPhaseSquare]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hPhi,hs,← Complex.exp_add]
  congr 1
  dsimp only [completePhase]
  ring

end HillPhysicalOnIndexPhaseChart
end NLS.KdV
