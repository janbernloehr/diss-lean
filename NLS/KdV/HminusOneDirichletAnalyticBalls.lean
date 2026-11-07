import NLS.KdV.HminusOneDirichletAllGaps
import NLS.KdV.HillHminusOneCanonicalQuotients
import NLS.KdV.HminusOneDirichletUniformSimplicity
import NLS.ZakharovShabat.SourceBoundaryRootsAnalyticNeighborhood
import NLS.ZakharovShabat.SourcePhaseCompatibility
import NLS.ComplexAnalysis.JointSpectralDerivative

/-! # Common analytic simple Dirichlet divisor balls at every real source

The actual scalar energies of ALL positive auxiliary Miura coordinates
are analytic on one complex ball. A uniform native high cutoff is chosen
before the FINITELY many remaining derivative neighborhoods. Thus every
scalar Dirichlet coordinate is simple on the SAME ball, including the low
indices, and agrees with the ORIGINAL real Dirichlet label on its real form.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

def HillHminusMiuraGapBall.dirichletEnergy (B : HillHminusMiuraGapBall) (n : ℕ+)
    (q : PeriodOneHminusOne) : ℂ := hillMiuraDirichletEnergy (B.actionBall.lift q) B.actionBall.shift (n : ℕ)

theorem HillHminusMiuraGapBall.dirichletEnergy_eq_real (B : HillHminusMiuraGapBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hreal : IsRealPeriodOneHminusOne q) :
    B.dirichletEnergy n q = (hillHminusDirichletLabels q hreal n : ℂ) := by
  let u : PeriodOneRealL2 := ⟨B.actionBall.lift q,B.actionBall.lift_real q hq hreal⟩
  have he := congrFun (hillHminusDirichletLabels_eq_miura q hreal u B.actionBall.shift (B.actionBall.image q hq)) n
  exact (hillMiuraDirichletEnergy_ofReal_re u B.actionBall.shift (n : ℕ)).symm.trans (congrArg ofReal he).symm

structure HillHminusDirichletBall where
  miuraBall : HillHminusMiuraGapBall
  subset_ratio : miuraBall.source ⊆ hillHminusCanonicalRatioDomain
  auxiliary_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ
    (fun q => hillMiuraDiracDirichlet (miuraBall.actionBall.lift q) n) miuraBall.source
  cutoff : ℕ
  control : ∀ q ∈ miuraBall.source, HillHminusDirichletComplexControl q
    (miuraBall.actionBall.lift q) miuraBall.actionBall.shift cutoff
  excluded_shift : ∀ q ∈ miuraBall.source,
    hillHminusDirichlet q (-(miuraBall.actionBall.shift : ℂ)) ≠ 0
  simple : ∀ n : ℕ+, ∀ q ∈ miuraBall.source,
    deriv (hillHminusDirichlet q) (miuraBall.dirichletEnergy n q) ≠ 0

namespace HillHminusDirichletBall

def source (B : HillHminusDirichletBall) : Set PeriodOneHminusOne := B.miuraBall.source
def energy (B : HillHminusDirichletBall) (n : ℕ+) : PeriodOneHminusOne → ℂ := B.miuraBall.dirichletEnergy n

theorem source_open (B : HillHminusDirichletBall) : IsOpen B.source := B.miuraBall.source_open

theorem analytic_energy (B : HillHminusDirichletBall) (n : ℕ+) :
    AnalyticOnNhd ℂ (B.energy n) B.source := by
  intro q hq
  exact ((B.auxiliary_analytic (n : ℕ) q hq).pow 2).sub analyticAt_const

theorem energy_eq_real (B : HillHminusDirichletBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hreal : IsRealPeriodOneHminusOne q) :
    B.energy n q = (hillHminusDirichletLabels q hreal n : ℂ) := B.miuraBall.dirichletEnergy_eq_real n q hq hreal

theorem energy_is_root (B : HillHminusDirichletBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) : hillHminusDirichlet q (B.energy n q) = 0 := by
  let F : PeriodOneHminusOne → ℂ := fun a => hillHminusDirichlet a (B.energy n a)
  have ha : AnalyticOnNhd ℂ F B.source := fun a ha =>
    (analyticOnNhd_hillHminusDirichlet_joint (B.energy n a,a) (mem_univ _)).comp
      (f := fun b => (B.energy n b,b)) ((B.analytic_energy n a ha).prod analyticAt_id)
  have he : EqOn F (fun _ => (0 : ℂ)) B.source :=
    analytic_eqOn_of_real_periodOneHminus B.source B.source_open
      (convex_ball B.miuraBall.actionBall.center B.miuraBall.actionBall.radius).isPreconnected
      ⟨B.miuraBall.actionBall.center,mem_ball_self B.miuraBall.actionBall.radius_pos,B.miuraBall.actionBall.center_real⟩
      F _ ha analyticOnNhd_const (by
        intro a ha har
        dsimp [F]
        rw [B.energy_eq_real n a ha har]
        exact hillHminusDirichletLabels_is_root a har n)
  exact he hq

theorem energy_eq_high (B : HillHminusDirichletBall) (n : ℕ+) (hn : B.cutoff < (n : ℕ))
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    B.energy n q = hillHminusDirichletComplexLabels q n :=
  (hillHminusDirichletComplexLabels_eq_tail_of_control q _ _ B.cutoff (B.control q hq) n hn).symm

theorem energy_eq_on_overlap (B C : HillHminusDirichletBall) (n : ℕ+) :
    EqOn (B.energy n) (C.energy n) (B.source ∩ C.source) := by
  intro q hq
  have hreal : ∃ a ∈ B.source ∩ C.source, IsRealPeriodOneHminusOne a :=
    exists_real_mem_periodOneHminus_ball_inter B.miuraBall.actionBall.center C.miuraBall.actionBall.center
      B.miuraBall.actionBall.center_real C.miuraBall.actionBall.center_real
      B.miuraBall.actionBall.radius C.miuraBall.actionBall.radius ⟨q,hq⟩
  exact analytic_eqOn_of_real_periodOneHminus (B.source ∩ C.source) (B.source_open.inter C.source_open)
    ((convex_ball B.miuraBall.actionBall.center B.miuraBall.actionBall.radius).inter
      (convex_ball C.miuraBall.actionBall.center C.miuraBall.actionBall.radius)).isPreconnected hreal
    _ _ ((B.analytic_energy n).mono inter_subset_left) ((C.analytic_energy n).mono inter_subset_right)
    (fun a ha har => (B.energy_eq_real n a ha.1 har).trans (C.energy_eq_real n a ha.2 har).symm) hq

end HillHminusDirichletBall

theorem exists_hillHminusDirichletBall (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ B : HillHminusDirichletBall, q ∈ B.source := by
  obtain ⟨B,hB⟩ := exists_hillHminusMiuraGapBall q hq
  let C : HillHminusMiuraChart := {
    domain := B.source
    domain_open := B.source_open
    energyShift := B.actionBall.shift
    lift := B.actionBall.lift
    lift_analytic := B.actionBall.lift_analytic
    image := B.actionBall.image }
  obtain ⟨N,T,_,hT,hqT,_,hcontrol,_⟩ := C.exists_uniform_analytic_dirichletControl q hB
  let f : PeriodOneHminusOne → CoeffPair 2 := fun a => sourcePhase (hillMiuraDiagonal (B.actionBall.lift a))
  have hf : AnalyticOnNhd ℂ f B.source := fun a ha =>
    ((sourcePhase (p := 2)).analyticAt _).comp
      (f := fun b : PeriodOneHminusOne => hillMiuraDiagonal (B.actionBall.lift b))
      ((hillMiuraDiagonal.analyticAt _).comp (f := B.actionBall.lift) (B.actionBall.lift_analytic a ha))
  have hreal : IsRealType (CoeffPair.toMax 2 (f q)) :=
    isRealType_sourcePhase _ (isRealType_hillMiuraDiagonal ⟨B.actionBall.lift q,B.actionBall.lift_real q hB hq⟩)
  obtain ⟨A,hA,hqA,haux⟩ := exists_local_source_allBoundaryRoots_analytic (p := 2) (by simp) (by norm_num) (f q) hreal
  let Y := B.source ∩ (f ⁻¹' A ∩ (T ∩ hillHminusCanonicalRatioDomain))
  have hY : IsOpen Y := by
    simpa only [Y,inter_assoc] using (hf.continuousOn.isOpen_inter_preimage B.source_open hA).inter
      (hT.inter isOpen_hillHminusCanonicalRatioDomain)
  have hqY : q ∈ Y := ⟨hB,hqA,hqT,real_mem_hillHminusCanonicalRatioDomain q hq⟩
  have han : ∀ n : ℤ, AnalyticOnNhd ℂ
      (fun a => hillMiuraDiracDirichlet (B.actionBall.lift a) n) Y := by
    intro n a ha
    have he : (fun b => hillMiuraDiracDirichlet (B.actionBall.lift b) n) =
        fun b => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet (f b) n :=
      funext (fun b => congrFun (canonicalAuxiliaryPeriodOneRoots_eq_sourcePhase
        (by simp) (by norm_num) .dirichlet (hillMiuraDiagonal (B.actionBall.lift b))) n)
    rw [he]
    exact (haux .dirichlet n (f a) ha.2.1).comp (f := f) (hf a ha.1)
  have he : ∀ n : ℕ+, AnalyticOnNhd ℂ (B.dirichletEnergy n) Y :=
    fun n a ha => ((han (n : ℕ) a ha).pow 2).sub analyticAt_const
  have hd : Continuous (fun t : ℂ × PeriodOneHminusOne => deriv (hillHminusDirichlet t.2) t.1) :=
    continuousOn_univ.mp (continuousOn_spectral_deriv_of_analyticOnNhd
      (fun t : ℂ × PeriodOneHminusOne => hillHminusDirichlet t.2 t.1) univ isOpen_univ
      analyticOnNhd_hillHminusDirichlet_joint)
  have hsimple (n : ℕ+) : ∀ᶠ a in 𝓝 q, deriv (hillHminusDirichlet a) (B.dirichletEnergy n a) ≠ 0 := by
    have hc := hd.continuousAt.comp ((he n q hqY).continuousAt.prodMk continuousAt_id)
    apply hc.eventually_ne
    apply deriv_hillHminusDirichlet_ne_zero_of_real q hq
    change hillHminusDirichlet q (B.dirichletEnergy n q) = 0
    rw [B.dirichletEnergy_eq_real n q hB hq]
    exact hillHminusDirichletLabels_is_root q hq n
  have hfinite : ∀ᶠ a in 𝓝 q, ∀ k ∈ Finset.range (N+1), ∀ hk : 0 < k,
      deriv (hillHminusDirichlet a) (B.dirichletEnergy ⟨k,hk⟩ a) ≠ 0 := by
    rw [Finset.eventually_all]
    intro k _
    by_cases hk : 0 < k
    · filter_upwards [hsimple ⟨k,hk⟩] with a ha
      intro _
      exact ha
    · exact Filter.Eventually.of_forall (fun _ hk' => (hk hk').elim)
  have hbottom : hillHminusDirichlet q (-(B.actionBall.shift : ℂ)) ≠ 0 := by
    intro hz
    let u : PeriodOneRealL2 := ⟨B.actionBall.lift q,B.actionBall.lift_real q hB hq⟩
    have hp := hillHminusDirichlet_root_above_shift q u B.actionBall.shift
      (B.actionBall.image q hB) (-(B.actionBall.shift : ℂ)) hz
    simp only [neg_re,ofReal_re] at hp
    linarith
  have hbottomNear := (continuous_hillHminusDirichlet_potential (-(B.actionBall.shift : ℂ))).continuousAt.eventually_ne hbottom
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hY.mem_nhds hqY) (hfinite.and hbottomNear))
  let D : HillHminusMiuraActionBall := {
    center := q
    center_real := hq
    radius := r
    radius_pos := hr
    shift := B.actionBall.shift
    lift := B.actionBall.lift
    lift_analytic := B.actionBall.lift_analytic.mono (fun a ha => (hball ha).1.1)
    lift_real := fun a ha => B.actionBall.lift_real a (hball ha).1.1
    image := fun a ha => B.actionBall.image a (hball ha).1.1
    outside := fun a ha => B.actionBall.outside a (hball ha).1.1
    action_analytic := fun n => (B.actionBall.action_analytic n).mono (fun a ha => (hball ha).1.1) }
  let G : HillHminusMiuraGapBall := {
    actionBall := D
    highNeighborhood := B.highNeighborhood
    high_subset := fun a ha => B.high_subset (hball ha).1.1
    midpoint_analytic := fun n => (B.midpoint_analytic n).mono (fun a ha => (hball ha).1.1)
    dirac_gap_square_analytic := fun n => (B.dirac_gap_square_analytic n).mono (fun a ha => (hball ha).1.1) }
  let E : HillHminusDirichletBall := {
    miuraBall := G
    subset_ratio := fun a ha => (hball ha).1.2.2.2
    auxiliary_analytic := fun n => (han n).mono (fun a ha => (hball ha).1)
    cutoff := N
    control := fun a ha => hcontrol a (hball ha).1.2.2.1
    excluded_shift := fun a ha => (hball ha).2.2
    simple := by
      intro n a ha
      change deriv (hillHminusDirichlet a) (B.dirichletEnergy n a) ≠ 0
      by_cases hn : N < (n : ℕ)
      · have hc := hcontrol a (hball ha).1.2.2.1
        have hm := hillHminusDirichletComplexLabels_multiplicity_one_of_control a _ _ N hc n hn
        have heq := hillHminusDirichletComplexLabels_eq_tail_of_control a _ _ N hc n hn
        change deriv (hillHminusDirichlet a) (hillMiuraDirichletEnergy (C.lift a) C.energyShift (n : ℕ)) ≠ 0
        rw [← heq]
        exact deriv_hillHminusDirichlet_ne_zero_of_multiplicity_one a _ hm
      · exact (hball ha).2.1 (n : ℕ) (Finset.mem_range.mpr (by omega)) n.pos }
  exact ⟨E,mem_ball_self hr⟩

end NLS.KdV
