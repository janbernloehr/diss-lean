import NLS.KdV.HillHminusOneDirichletBands
import NLS.KdV.HillHminusOneDirichletRootBranches
import NLS.KdV.HillHminusOneFreeDirichlet
import NLS.ComplexAnalysis.ClosedIntervalRoots
import NLS.KdV.HillHminusOneLabelContinuity

/-! # Every canonical H^-1 gap contains an actual Dirichlet zero

The existence set is closed by compact variable-interval projection and
open by the simple analytic root branch and exclusion of neighboring
open bands. The real scalar path from the free potential proves existence
at every real H^-1 potential, including every closed canonical gap.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusDirichlet_zero_mem_gap_of_between_neighbor_bands
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Ioo (hillHminusRealLabels q hr (2*n-2)) (hillHminusRealLabels q hr (2*n+1)))
    (hz : hillHminusDirichlet q x = 0) :
    x ∈ Icc (hillHminusRealLabels q hr (2*n-1)) (hillHminusRealLabels q hr (2*n)) := by
  constructor
  · by_contra! hl
    apply hillHminusDirichlet_ne_zero_on_open_band q hr (n-1) x ?_ hz
    rw [show 2*(n-1) = 2*n-2 by omega,show 2*n-2+1 = 2*n-1 by omega]
    exact ⟨hx.1,hl⟩
  · by_contra! hu
    exact hillHminusDirichlet_ne_zero_on_open_band q hr n x ⟨hu,hx.2⟩ hz

theorem isClopen_hillHminusDirichlet_gap_root_family
    {T : Type*} [TopologicalSpace T] (Q : T → PeriodOneHminusOne) (hQ : Continuous Q)
    (hr : ∀ t, IsRealPeriodOneHminusOne (Q t)) (n : ℕ) (hn : 1 ≤ n) :
    IsClopen {t : T | ∃ x ∈ Icc (hillHminusRealLabels (Q t) (hr t) (2*n-1))
      (hillHminusRealLabels (Q t) (hr t) (2*n)), hillHminusDirichlet (Q t) x = 0} := by
  let L (j : ℕ) (t : T) := hillHminusRealLabels (Q t) (hr t) j
  have hL (j : ℕ) : Continuous (L j) := continuous_hillHminusRealLabels_family Q hQ hr j
  have hF : Continuous (fun p : T × ℝ => hillHminusDirichlet (Q p.1) p.2) := by
    have hm : Continuous (fun p : T × ℝ => ((p.2 : ℂ),Q p.1)) :=
      (Complex.continuous_ofReal.comp continuous_snd).prodMk (hQ.comp continuous_fst)
    have hc : Continuous (fun p : ℂ × PeriodOneHminusOne => hillHminusDirichlet p.2 p.1) :=
      analyticOnNhd_hillHminusDirichlet_joint.continuous
    exact Continuous.comp (g := fun p : ℂ × PeriodOneHminusOne => hillHminusDirichlet p.2 p.1)
      (f := fun p : T × ℝ => ((p.2 : ℂ),Q p.1)) hc hm
  constructor
  · exact isClosed_exists_zero_in_variable_Icc _ (L (2*n-1)) (L (2*n)) hF
      (hL _) (hL _) (fun t => monotone_hillHminusRealLabels (Q t) (hr t) (by omega))
  · apply isOpen_iff_mem_nhds.mpr
    rintro t0 ⟨x,hx,hzero⟩
    obtain ⟨a,ha,hax,he⟩ := exists_hillHminusDirichlet_analytic_real_root_branch (Q t0) (hr t0) x hzero
    have hbranch : ∀ᶠ t in 𝓝 t0, hillHminusDirichlet (Q t) (a (Q t)) = 0 ∧ (a (Q t)).im = 0 := by
      filter_upwards [hQ.continuousAt.tendsto.eventually he] with t ht
      exact ⟨ht.1,ht.2 (hr t)⟩
    have hac : ContinuousAt (fun t => (a (Q t)).re) t0 :=
      Complex.continuous_re.continuousAt.comp (ha.continuousAt.comp hQ.continuousAt)
    have hleft : L (2*n-2) t0 < (a (Q t0)).re := by
      have hb := hillHminusRealLabels_band_strict (Q t0) (hr t0) (n-1)
      rw [show 2*(n-1) = 2*n-2 by omega,show 2*n-2+1 = 2*n-1 by omega] at hb
      rw [hax,ofReal_re]
      exact lt_of_lt_of_le hb hx.1
    have hright : (a (Q t0)).re < L (2*n+1) t0 := by
      rw [hax,ofReal_re]
      exact lt_of_le_of_lt hx.2 (hillHminusRealLabels_band_strict (Q t0) (hr t0) n)
    have hcollar : ∀ᶠ t in 𝓝 t0, (a (Q t)).re ∈ Ioo (L (2*n-2) t) (L (2*n+1) t) :=
      ((hL _).continuousAt.eventually_lt hac hleft).and
        (hac.eventually_lt (hL _).continuousAt hright)
    filter_upwards [hbranch,hcollar] with t ht hc
    have heq : ((a (Q t)).re : ℂ) = a (Q t) := by apply Complex.ext <;> simp [ht.2]
    have hz : hillHminusDirichlet (Q t) ((a (Q t)).re) = 0 := by rw [heq]; exact ht.1
    exact ⟨(a (Q t)).re,hillHminusDirichlet_zero_mem_gap_of_between_neighbor_bands
      (Q t) (hr t) n hn _ hc hz,hz⟩

theorem exists_hillHminusDirichlet_zero_in_gap
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) :
    ∃ x ∈ Icc (hillHminusRealLabels q hr (2*n-1)) (hillHminusRealLabels q hr (2*n)),
      hillHminusDirichlet q x = 0 := by
  let Q : ℝ → PeriodOneHminusOne := fun t => (t : ℂ) • q
  have hQ : Continuous Q := Complex.continuous_ofReal.smul continuous_const
  have hQr (t : ℝ) : IsRealPeriodOneHminusOne (Q t) := hr.smul_real t
  have hc := isClopen_hillHminusDirichlet_gap_root_family Q hQ hQr n hn
  have hzero : (0 : ℝ) ∈ {t : ℝ | ∃ x ∈ Icc
      (hillHminusRealLabels (Q t) (hQr t) (2*n-1)) (hillHminusRealLabels (Q t) (hQr t) (2*n)),
      hillHminusDirichlet (Q t) x = 0} := by
    have hQ0 : Q 0 = 0 := by simp [Q]
    refine ⟨freeHillValue n,?_,?_⟩
    · simp only [hQ0,hillHminusRealLabels_zero]
      have hl : (2*n-1+1)/2 = n := by omega
      have hu : (2*n+1)/2 = n := by omega
      simp [hl,hu]
    · rw [hQ0]
      exact hillHminusDirichlet_free_nat_root n hn
  have hall := hc.eq_univ ⟨0,hzero⟩
  have h1 : (1 : ℝ) ∈ {t : ℝ | ∃ x ∈ Icc
      (hillHminusRealLabels (Q t) (hQr t) (2*n-1)) (hillHminusRealLabels (Q t) (hQr t) (2*n)),
      hillHminusDirichlet (Q t) x = 0} := by rw [hall]; trivial
  simpa only [Q,ofReal_one,one_smul,mem_ofPred_eq] using h1

end NLS.KdV
