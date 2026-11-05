import NLS.KdV.HillMiuraL2Discriminant
import NLS.SequenceSpaces.PeriodOneHminusOneDensity

/-! # The actual Hill discriminant extended to all complex H^-1 potentials

Local analytic Miura lifts define energy-shifted diagonal L2 traces.
For L2 potentials, lift regularity identifies each trace with the actual
physical Hill monodromy. L2 density forces agreement on open overlaps.
The resulting single trace is jointly entire in energy and H^-1 potential.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

structure HillHminusMiuraChart where
  domain : Set PeriodOneHminusOne
  domain_open : IsOpen domain
  energyShift : ℂ
  lift : PeriodOneHminusOne → Coeff 2
  lift_analytic : AnalyticOnNhd ℂ lift domain
  image : ∀ q ∈ domain, periodOneMiura (lift q) =
    q+periodOneL2Inclusion (lp.single 2 0 energyShift)

theorem exists_hillHminusMiuraChart (q : PeriodOneHminusOne) :
    ∃ C : HillHminusMiuraChart, q ∈ C.domain := by
  obtain ⟨m,U,hU,hq,u,hu,himage⟩ := exists_periodOneMiura_energyChart q
  exact ⟨⟨U,hU,(((m : ℝ)+1 : ℝ)/2 : ℂ)^2,u,hu,himage⟩,hq⟩

namespace HillHminusMiuraChart

def trace (C : HillHminusMiuraChart) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  hillMiuraL2Discriminant (C.lift t.2) (t.1+C.energyShift)

theorem analyticOnNhd_trace (C : HillHminusMiuraChart) :
    AnalyticOnNhd ℂ C.trace (univ ×ˢ C.domain) := by
  intro t ht
  have hu : AnalyticAt ℂ (fun p : ℂ × PeriodOneHminusOne => C.lift p.2) t :=
    (C.lift_analytic t.2 ht.2).comp analyticAt_snd
  have he : AnalyticAt ℂ (fun p : ℂ × PeriodOneHminusOne => p.1+C.energyShift) t :=
    analyticAt_fst.add analyticAt_const
  exact (analyticOnNhd_hillMiuraL2Discriminant_joint
    (t.1+C.energyShift,C.lift t.2) (mem_univ _)).comp
      (f := fun p : ℂ × PeriodOneHminusOne => (p.1+C.energyShift,C.lift p.2)) (he.prod hu)

theorem analyticAt_trace_potential (C : HillHminusMiuraChart) (lambda : ℂ)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) :
    AnalyticAt ℂ (fun r => C.trace (lambda,r)) q :=
  (C.analyticOnNhd_trace (lambda,q) ⟨mem_univ _,hq⟩).comp
    (f := fun r : PeriodOneHminusOne => (lambda,r)) (analyticAt_const.prod analyticAt_id)

/-- Every local chart gives the independently constructed physical L2 trace. -/
theorem trace_eq_hillL2 (C : HillHminusMiuraChart) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ C.domain) (lambda : ℂ) :
    C.trace (lambda,periodOneL2Inclusion q) = hillL2Discriminant (Coeff.periodDouble q) lambda := by
  apply hillMiuraL2Discriminant_eq_hillL2_of_shifted_image
  rw [map_add]
  exact C.image _ hq

/-- Independence of both the local inverse branch and the mass on every overlap. -/
theorem trace_eqOn_overlap (C D : HillHminusMiuraChart) (lambda : ℂ) :
    EqOn (fun q => C.trace (lambda,q)) (fun q => D.trace (lambda,q)) (C.domain ∩ D.domain) := by
  apply eqOn_of_eqOn_periodOneL2Inclusion (C.domain_open.inter D.domain_open)
  · intro q hq
    exact (C.analyticAt_trace_potential lambda q hq.1).continuousAt.continuousWithinAt
  · intro q hq
    exact (D.analyticAt_trace_potential lambda q hq.2).continuousAt.continuousWithinAt
  · intro q hq
    rw [C.trace_eq_hillL2 q hq.1,D.trace_eq_hillL2 q hq.2]

end HillHminusMiuraChart

def hillHminusMiuraChartAt (q : PeriodOneHminusOne) : HillHminusMiuraChart :=
  (exists_hillHminusMiuraChart q).choose

theorem mem_hillHminusMiuraChartAt (q : PeriodOneHminusOne) :
    q ∈ (hillHminusMiuraChartAt q).domain := (exists_hillHminusMiuraChart q).choose_spec

/-- The unit-period H^-1 Hill discriminant, independent of all Miura chart choices. -/
def hillHminusDiscriminant (q : PeriodOneHminusOne) (lambda : ℂ) : ℂ :=
  (hillHminusMiuraChartAt q).trace (lambda,q)

theorem hillHminusDiscriminant_eq_chart (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (lambda : ℂ) :
    hillHminusDiscriminant q lambda = C.trace (lambda,q) :=
  (hillHminusMiuraChartAt q).trace_eqOn_overlap C lambda ⟨mem_hillHminusMiuraChartAt q,hq⟩

/-- The extension is jointly entire, including zero energy and arbitrary complex potentials. -/
theorem analyticOnNhd_hillHminusDiscriminant_joint :
    AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne => hillHminusDiscriminant t.2 t.1) univ := by
  intro t _
  let C := hillHminusMiuraChartAt t.2
  have ht : t ∈ univ ×ˢ C.domain := ⟨mem_univ _,mem_hillHminusMiuraChartAt _⟩
  have hnh : univ ×ˢ C.domain ∈ 𝓝 t := (isOpen_univ.prod C.domain_open).mem_nhds ht
  apply (C.analyticOnNhd_trace t ht).congr
  filter_upwards [hnh] with p hp
  exact (hillHminusDiscriminant_eq_chart C p.2 hp.2 p.1).symm

theorem hillHminusDiscriminant_eq_hillL2 (q : Coeff 2) (lambda : ℂ) :
    hillHminusDiscriminant (periodOneL2Inclusion q) lambda =
      hillL2Discriminant (Coeff.periodDouble q) lambda :=
  (hillHminusMiuraChartAt _).trace_eq_hillL2 q (mem_hillHminusMiuraChartAt _) lambda

/-- Any continuous extension of the physical L2 trace is this same H^-1 trace. -/
theorem hillHminusDiscriminant_unique (D : PeriodOneHminusOne → ℂ) (lambda : ℂ)
    (hD : Continuous D)
    (hagree : ∀ q : Coeff 2, D (periodOneL2Inclusion q) =
      hillL2Discriminant (Coeff.periodDouble q) lambda) :
    D = fun q => hillHminusDiscriminant q lambda := by
  have hc : Continuous (fun q => hillHminusDiscriminant q lambda) := by
    have h : Continuous (fun t : ℂ × PeriodOneHminusOne => hillHminusDiscriminant t.2 t.1) :=
      analyticOnNhd_hillHminusDiscriminant_joint.continuous
    have hm : Continuous (fun q : PeriodOneHminusOne => (lambda,q)) :=
      continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using h.comp hm
  exact denseRange_periodOneL2Inclusion.equalizer hD hc (by
    funext q
    exact (hagree q).trans (hillHminusDiscriminant_eq_hillL2 q lambda).symm)

end NLS.KdV
