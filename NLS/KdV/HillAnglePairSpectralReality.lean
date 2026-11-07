import NLS.KdV.HillCompletePhaseReality
import NLS.KdV.HillDiscriminantRealForm
import NLS.KdV.HillAnglePairDiscriminantPeriods

/-! The actual complete phase cotangents, phase-pair bracket and
its real-energy discriminant variation are physically real. Their
frequency pullback is entire and odd, with no reality assumption
on its cotangents left to the caller. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV.HillPhysicalOnIndexPhaseChart
variable {P Q : HillProductEquationPatch} {n m : ℕ+}

theorem completePhase_Hamiltonian_real (C : HillPhysicalOnIndexPhaseChart P n)
    (q : PeriodOneHminusOne) (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q) :
    IsRealPeriodOneHminusOne (NLS.Poisson.gardnerHamiltonianVector C.completePhase q) := by
  apply NLS.Poisson.gardnerHamiltonianVector_real_of_eventually_real C.completePhase q hr
    (C.analytic_completePhase q ⟨hq,real_mem_hillHminusOffIndexAnalyticDomain q hr⟩)
  filter_upwards [C.source_open.mem_nhds hq] with p hp hpr
  exact C.completePhase_im_eq_zero_of_real p hp hpr

theorem completePhasePairBracket_im_eq_zero_of_real
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne q) : (C.completePhasePairBracket D q).im=0 := by
  apply NLS.Poisson.hminusGardnerBracket_real_of_eventually_real C.completePhase D.completePhase q hr
    (C.analytic_completePhase q ⟨hqC,real_mem_hillHminusOffIndexAnalyticDomain q hr⟩)
    (D.analytic_completePhase q ⟨hqD,real_mem_hillHminusOffIndexAnalyticDomain q hr⟩)
  · filter_upwards [C.source_open.mem_nhds hqC] with p hp hpr
    exact C.completePhase_im_eq_zero_of_real p hp hpr
  · filter_upwards [D.source_open.mem_nhds hqD] with p hp hpr
    exact D.completePhase_im_eq_zero_of_real p hp hpr

theorem completePhasePairDiscriminantBracket_im_eq_zero_of_real
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne q) (E : ℝ) :
    (C.completePhasePairDiscriminantBracket D q (E:ℂ)).im=0 := by
  apply NLS.Poisson.hminusGardnerBracket_real_of_eventually_real (C.completePhasePairBracket D)
    (fun p => hillHminusDiscriminant p (E:ℂ)) q hr
    (C.analytic_completePhasePairBracket D q ⟨⟨hqC,hqD⟩,real_mem_hillHminusOffIndexAnalyticDomain q hr⟩)
    (analyticOnNhd_hillHminusDiscriminant_source (E:ℂ) q (mem_univ _))
  · filter_upwards [(C.source_open.inter D.source_open).mem_nhds ⟨hqC,hqD⟩] with p hp hpr
    exact C.completePhasePairBracket_im_eq_zero_of_real D p hp.1 hp.2 hpr
  · exact Eventually.of_forall (fun p hpr => hillHminusDiscriminant_im_eq_zero_of_real p hpr E)

def completePhasePairFrequencyVariation (C : HillPhysicalOnIndexPhaseChart P n)
    (D : HillPhysicalOnIndexPhaseChart Q m) (q : PeriodOneHminusOne) (z : ℂ) : ℂ :=
  z*C.completePhasePairDiscriminantBracket D q (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))

theorem analytic_completePhasePairFrequencyVariation (C : HillPhysicalOnIndexPhaseChart P n)
    (D : HillPhysicalOnIndexPhaseChart Q m) (q : PeriodOneHminusOne) :
    AnalyticOnNhd ℂ (C.completePhasePairFrequencyVariation D q) univ := by
  intro z _
  exact analyticAt_id.mul ((C.analytic_completePhasePairDiscriminantBracket_energy D q
    (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ)) (mem_univ _)).comp
    (f := fun w : ℂ => w^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ))
      ((analyticAt_id.pow 2).sub analyticAt_const))

theorem completePhasePairFrequencyVariation_neg (C : HillPhysicalOnIndexPhaseChart P n)
    (D : HillPhysicalOnIndexPhaseChart Q m) (q : PeriodOneHminusOne) (z : ℂ) :
    C.completePhasePairFrequencyVariation D q (-z) = -C.completePhasePairFrequencyVariation D q z := by
  simp only [completePhasePairFrequencyVariation,neg_sq,neg_mul]

theorem completePhasePairFrequencyVariation_im_eq_zero_of_real
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne q) (x : ℝ) :
    (C.completePhasePairFrequencyVariation D q (x:ℂ)).im=0 := by
  have he : (x:ℂ)^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ) =
      ((x^2-P.parent.parent.miuraBall.actionBall.shift:ℝ):ℂ) := by push_cast; rfl
  simp only [completePhasePairFrequencyVariation,he,mul_im,ofReal_im,ofReal_re,zero_mul,add_zero,
    C.completePhasePairDiscriminantBracket_im_eq_zero_of_real D q hqC hqD hr _,mul_zero]

end NLS.KdV.HillPhysicalOnIndexPhaseChart
