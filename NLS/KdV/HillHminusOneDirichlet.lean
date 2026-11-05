import NLS.KdV.HillHminusOneDiscriminant
import NLS.MKdV.MiuraL2HillDirichlet

/-! The original scalar Dirichlet characteristic extended to every complex
H-minus-one potential. Local analytic shifted Miura realizations agree on
open overlaps by the physical L2 comparison and L2 density. The resulting
family is jointly entire in energy and potential, including zero energy.
Identification of its zeros with the full rough Dirichlet operator remains
a separate statement. -/
noncomputable section
open Set Complex Filter Topology NLS.MKdV
open scoped ENNReal
namespace NLS.KdV

namespace HillHminusMiuraChart

def dirichlet (C : HillHminusMiuraChart) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  quasiHillL2Dirichlet (C.lift t.2) (t.1+C.energyShift)

theorem analyticOnNhd_dirichlet (C : HillHminusMiuraChart) :
    AnalyticOnNhd ℂ C.dirichlet (univ ×ˢ C.domain) := by
  intro t ht
  have hu : AnalyticAt ℂ (fun p : ℂ × PeriodOneHminusOne => C.lift p.2) t :=
    (C.lift_analytic t.2 ht.2).comp analyticAt_snd
  have he : AnalyticAt ℂ (fun p : ℂ × PeriodOneHminusOne => p.1+C.energyShift) t :=
    analyticAt_fst.add analyticAt_const
  exact (analyticOnNhd_quasiHillL2Dirichlet_joint
    (t.1+C.energyShift,C.lift t.2) (mem_univ _)).comp
      (f := fun p : ℂ × PeriodOneHminusOne => (p.1+C.energyShift,C.lift p.2)) (he.prod hu)

theorem analyticAt_dirichlet_potential (C : HillHminusMiuraChart) (lambda : ℂ)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) :
    AnalyticAt ℂ (fun r => C.dirichlet (lambda,r)) q :=
  (C.analyticOnNhd_dirichlet (lambda,q) ⟨mem_univ _,hq⟩).comp
    (f := fun r : PeriodOneHminusOne => (lambda,r)) (analyticAt_const.prod analyticAt_id)

/-- Every local chart gives the independently constructed physical L2 dirichlet. -/
theorem dirichlet_eq_hillL2 (C : HillHminusMiuraChart) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ C.domain) (lambda : ℂ) :
    C.dirichlet (lambda,periodOneL2Inclusion q) = hillL2Dirichlet (Coeff.periodDouble q) lambda := by
  apply quasiHillL2Dirichlet_eq_hillL2_of_shifted_image
  rw [map_add]
  exact C.image _ hq

/-- Independence of both the local inverse branch and the mass on every overlap. -/
theorem dirichlet_eqOn_overlap (C D : HillHminusMiuraChart) (lambda : ℂ) :
    EqOn (fun q => C.dirichlet (lambda,q)) (fun q => D.dirichlet (lambda,q)) (C.domain ∩ D.domain) := by
  apply eqOn_of_eqOn_periodOneL2Inclusion (C.domain_open.inter D.domain_open)
  · intro q hq
    exact (C.analyticAt_dirichlet_potential lambda q hq.1).continuousAt.continuousWithinAt
  · intro q hq
    exact (D.analyticAt_dirichlet_potential lambda q hq.2).continuousAt.continuousWithinAt
  · intro q hq
    rw [C.dirichlet_eq_hillL2 q hq.1,D.dirichlet_eq_hillL2 q hq.2]

end HillHminusMiuraChart

/-- The unit-period H-minus-one Dirichlet characteristic, independent of all Miura chart choices. -/
def hillHminusDirichlet (q : PeriodOneHminusOne) (lambda : ℂ) : ℂ :=
  (hillHminusMiuraChartAt q).dirichlet (lambda,q)

theorem hillHminusDirichlet_eq_chart (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (lambda : ℂ) :
    hillHminusDirichlet q lambda = C.dirichlet (lambda,q) :=
  (hillHminusMiuraChartAt q).dirichlet_eqOn_overlap C lambda ⟨mem_hillHminusMiuraChartAt q,hq⟩

/-- The extension is jointly entire, including zero energy and arbitrary complex potentials. -/
theorem analyticOnNhd_hillHminusDirichlet_joint :
    AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne => hillHminusDirichlet t.2 t.1) univ := by
  intro t _
  let C := hillHminusMiuraChartAt t.2
  have ht : t ∈ univ ×ˢ C.domain := ⟨mem_univ _,mem_hillHminusMiuraChartAt _⟩
  have hnh : univ ×ˢ C.domain ∈ 𝓝 t := (isOpen_univ.prod C.domain_open).mem_nhds ht
  apply (C.analyticOnNhd_dirichlet t ht).congr
  filter_upwards [hnh] with p hp
  exact (hillHminusDirichlet_eq_chart C p.2 hp.2 p.1).symm

theorem hillHminusDirichlet_eq_hillL2 (q : Coeff 2) (lambda : ℂ) :
    hillHminusDirichlet (periodOneL2Inclusion q) lambda =
      hillL2Dirichlet (Coeff.periodDouble q) lambda :=
  (hillHminusMiuraChartAt _).dirichlet_eq_hillL2 q (mem_hillHminusMiuraChartAt _) lambda

/-- The original H-minus-one extension preserves the free zero-energy normalization. -/
theorem hillHminusDirichlet_free_zero : hillHminusDirichlet 0 0 = 1 := by
  have h := hillHminusDirichlet_eq_hillL2 (0:Coeff 2) 0
  simpa only [map_zero,hillL2Dirichlet_free_zero] using h

/-- Any continuous extension of the physical L2 dirichlet is this same H^-1 dirichlet. -/
theorem hillHminusDirichlet_unique (D : PeriodOneHminusOne → ℂ) (lambda : ℂ)
    (hD : Continuous D)
    (hagree : ∀ q : Coeff 2, D (periodOneL2Inclusion q) =
      hillL2Dirichlet (Coeff.periodDouble q) lambda) :
    D = fun q => hillHminusDirichlet q lambda := by
  have hc : Continuous (fun q => hillHminusDirichlet q lambda) := by
    have h : Continuous (fun t : ℂ × PeriodOneHminusOne => hillHminusDirichlet t.2 t.1) :=
      analyticOnNhd_hillHminusDirichlet_joint.continuous
    have hm : Continuous (fun q : PeriodOneHminusOne => (lambda,q)) :=
      continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using h.comp hm
  exact denseRange_periodOneL2Inclusion.equalizer hD hc (by
    funext q
    exact (hagree q).trans (hillHminusDirichlet_eq_hillL2 q lambda).symm)


end NLS.KdV
