import NLS.KdV.HillHminusOneDirichletGapExistence
import NLS.KdV.HillHminusOneDirichletGapUniqueness

/-! # Intrinsic Dirichlet labels in every positive canonical H^-1 gap

Every positive gap, including a collapsed gap, contains exactly one
actual normalized Dirichlet zero. These intrinsic labels strictly
increase and agree locally with a complex analytic branch in the original
H^-1 norm. No independent root enumeration or global coordinate map is
assumed. Exhaustion of every Dirichlet zero in the lower exterior is
not asserted by the gap labeling alone.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

def hillHminusDirichletEnergy (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) : ℝ :=
  (exists_hillHminusDirichlet_zero_in_gap q hr (n : ℕ) n.property).choose

theorem hillHminusDirichletEnergy_mem_gap (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusDirichletEnergy q hr n ∈
      Icc (hillHminusRealLabels q hr (2*(n : ℕ)-1)) (hillHminusRealLabels q hr (2*(n : ℕ))) :=
  (exists_hillHminusDirichlet_zero_in_gap q hr (n : ℕ) n.property).choose_spec.1

theorem hillHminusDirichletEnergy_zero (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    hillHminusDirichlet q (hillHminusDirichletEnergy q hr n) = 0 :=
  (exists_hillHminusDirichlet_zero_in_gap q hr (n : ℕ) n.property).choose_spec.2

theorem hillHminusDirichletEnergy_eq_of_zero_in_gap
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (x : ℝ)
    (hx : x ∈ Icc (hillHminusRealLabels q hr (2*(n : ℕ)-1)) (hillHminusRealLabels q hr (2*(n : ℕ))))
    (hz : hillHminusDirichlet q x = 0) : hillHminusDirichletEnergy q hr n = x :=
  hillHminusDirichlet_zero_unique_in_gap q hr (n : ℕ) n.property _ x
    (hillHminusDirichletEnergy_mem_gap q hr n) hx (hillHminusDirichletEnergy_zero q hr n) hz

theorem hillHminusDirichletEnergy_eq_of_closed_gap
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+)
    (h : hillHminusRealLabels q hr (2*(n : ℕ)-1) = hillHminusRealLabels q hr (2*(n : ℕ))) :
    hillHminusDirichletEnergy q hr n = hillHminusRealLabels q hr (2*(n : ℕ)) := by
  have hm := hillHminusDirichletEnergy_mem_gap q hr n
  rw [h] at hm
  exact le_antisymm hm.2 hm.1

theorem strictMono_hillHminusDirichletEnergy (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    StrictMono (hillHminusDirichletEnergy q hr) := by
  intro n m hnm
  have hn := hillHminusDirichletEnergy_mem_gap q hr n
  have hm := hillHminusDirichletEnergy_mem_gap q hr m
  have hband := hillHminusRealLabels_band_strict q hr (n : ℕ)
  have hind : 2*(n : ℕ)+1 ≤ 2*(m : ℕ)-1 := by
    have hval : (n : ℕ) < (m : ℕ) := hnm
    omega
  exact lt_of_le_of_lt hn.2 (lt_of_lt_of_le hband
    ((monotone_hillHminusRealLabels q hr hind).trans hm.1))

theorem hillHminusDirichletEnergy_zero_potential (hr : IsRealPeriodOneHminusOne 0) (n : ℕ+) :
    hillHminusDirichletEnergy 0 hr n = freeHillValue (n : ℕ) := by
  apply hillHminusDirichletEnergy_eq_of_zero_in_gap
  · simp only [hillHminusRealLabels_zero]
    have hl : (2*(n : ℕ)-1+1)/2 = (n : ℕ) := by have hp := n.property; omega
    have hu : (2*(n : ℕ)+1)/2 = (n : ℕ) := by omega
    simp [hl,hu]
  · exact hillHminusDirichlet_free_nat_root (n : ℕ) n.property

theorem eventually_hillHminusDirichletEnergy_eq_branch_family
    {T : Type*} [TopologicalSpace T] (Q : T → PeriodOneHminusOne) (hQ : Continuous Q)
    (hr : ∀ t, IsRealPeriodOneHminusOne (Q t)) (n : ℕ+) (t0 : T) (a : T → ℂ)
    (ha : ContinuousAt a t0) (ha0 : a t0 = (hillHminusDirichletEnergy (Q t0) (hr t0) n : ℂ))
    (hz : ∀ᶠ t in 𝓝 t0, hillHminusDirichlet (Q t) (a t) = 0) :
    ∀ᶠ t in 𝓝 t0, (hillHminusDirichletEnergy (Q t) (hr t) n : ℂ) = a t := by
  let L (j : ℕ) (t : T) := hillHminusRealLabels (Q t) (hr t) j
  have hL (j : ℕ) : Continuous (L j) := continuous_hillHminusRealLabels_family Q hQ hr j
  have hm := hillHminusDirichletEnergy_mem_gap (Q t0) (hr t0) n
  have hpn : 1 ≤ (n : ℕ) := n.property
  have hac : ContinuousAt (fun t => (a t).re) t0 := Complex.continuous_re.continuousAt.comp ha
  have hl : L (2*(n : ℕ)-2) t0 < (a t0).re := by
    rw [ha0,ofReal_re]
    have hb := hillHminusRealLabels_band_strict (Q t0) (hr t0) ((n : ℕ)-1)
    rw [show 2*((n : ℕ)-1) = 2*(n : ℕ)-2 by omega,
      show 2*(n : ℕ)-2+1 = 2*(n : ℕ)-1 by omega] at hb
    exact lt_of_lt_of_le hb hm.1
  have hu : (a t0).re < L (2*(n : ℕ)+1) t0 := by
    rw [ha0,ofReal_re]
    exact lt_of_le_of_lt hm.2 (hillHminusRealLabels_band_strict (Q t0) (hr t0) (n : ℕ))
  have hc : ∀ᶠ t in 𝓝 t0, (a t).re ∈ Ioo (L (2*(n : ℕ)-2) t) (L (2*(n : ℕ)+1) t) :=
    ((hL _).continuousAt.eventually_lt hac hl).and (hac.eventually_lt (hL _).continuousAt hu)
  filter_upwards [hz,hc] with t ht hct
  have hreal := hillHminusDirichlet_zero_energy_im_zero (Q t) (hr t) (a t) ht
  have he : ((a t).re : ℂ) = a t := by apply Complex.ext <;> simp [hreal]
  have hz' : hillHminusDirichlet (Q t) ((a t).re) = 0 := by rw [he]; exact ht
  have hmem := hillHminusDirichlet_zero_mem_gap_of_between_neighbor_bands
    (Q t) (hr t) (n : ℕ) n.property _ hct hz'
  rw [hillHminusDirichletEnergy_eq_of_zero_in_gap (Q t) (hr t) n _ hmem hz',he]

theorem exists_hillHminusDirichletEnergy_analytic_extension (q : PeriodOneRealHminusOne) (n : ℕ+) :
    ∃ a : PeriodOneHminusOne → ℂ, AnalyticAt ℂ a q.val ∧
      a q.val = (hillHminusDirichletEnergy q.val q.property n : ℂ) ∧
      (∀ᶠ p in 𝓝 q.val, hillHminusDirichlet p (a p) = 0) ∧
      ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 q,
        a p.val = (hillHminusDirichletEnergy p.val p.property n : ℂ) := by
  obtain ⟨a,ha,hax,hroot⟩ := exists_hillHminusDirichlet_analytic_root_branch q.val q.property _
    (hillHminusDirichletEnergy_zero q.val q.property n)
  refine ⟨a,ha,hax,hroot,?_⟩
  have hmatch := eventually_hillHminusDirichletEnergy_eq_branch_family Subtype.val continuous_subtype_val
    (fun p : PeriodOneRealHminusOne => p.property) n q (fun p => a p.val)
    (ha.continuousAt.comp continuous_subtype_val.continuousAt) hax
    (continuous_subtype_val.continuousAt.tendsto.eventually hroot)
  exact hmatch.mono (fun _ hp => hp.symm)

theorem continuous_hillHminusDirichletEnergy (n : ℕ+) :
    Continuous (fun q : PeriodOneRealHminusOne => hillHminusDirichletEnergy q.val q.property n) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨a,ha,_,_,he⟩ := exists_hillHminusDirichletEnergy_analytic_extension q n
  have heq : (fun p : PeriodOneRealHminusOne => (hillHminusDirichletEnergy p.val p.property n : ℂ)) =ᶠ[𝓝 q]
      (fun p : PeriodOneRealHminusOne => a p.val) := he.mono (fun _ hp => hp.symm)
  have hc : ContinuousAt (fun p : PeriodOneRealHminusOne => (hillHminusDirichletEnergy p.val p.property n : ℂ)) q :=
    (ha.continuousAt.comp continuous_subtype_val.continuousAt).congr_of_eventuallyEq heq
  have hcre := Complex.continuous_re.continuousAt.comp hc
  simpa only [Function.comp_def,ofReal_re] using! hcre

end NLS.KdV
