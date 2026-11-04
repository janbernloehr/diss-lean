import NLS.KdV.HillHminusOneDirichletLowerBound
import NLS.KdV.HillHminusOneFreeDirichletLower
import NLS.KdV.HillHminusOneDirichletGapExistence

/-! # The actual H^-1 Dirichlet spectrum lies strictly above the periodic ground

For a real continuous family, existence of a Dirichlet zero at or below
the lowest periodic label is both open and closed. Local real Miura
factorization bounds its roots strictly from below, giving compactness.
The simple analytic branch and lowest open-band exclusion give openness.
The free characteristic then excludes this entire lower exterior by
the real scalar homotopy, including equality with the periodic ground.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem isClopen_hillHminusDirichlet_lower_root_family
    {T : Type*} [TopologicalSpace T] (Q : T → PeriodOneHminusOne) (hQ : Continuous Q)
    (hr : ∀ t, IsRealPeriodOneHminusOne (Q t)) :
    IsClopen {t : T | ∃ x : ℝ, x ≤ hillHminusRealLabels (Q t) (hr t) 0 ∧ hillHminusDirichlet (Q t) x = 0} := by
  let b : T → ℝ := fun t => hillHminusRealLabels (Q t) (hr t) 0
  let A : Set T := {t | ∃ x : ℝ, x ≤ b t ∧ hillHminusDirichlet (Q t) x = 0}
  have hb : Continuous b := continuous_hillHminusRealLabels_family Q hQ hr 0
  have hF : Continuous (fun p : T × ℝ => hillHminusDirichlet (Q p.1) p.2) := by
    have hc : Continuous (fun p : ℂ × PeriodOneHminusOne => hillHminusDirichlet p.2 p.1) :=
      analyticOnNhd_hillHminusDirichlet_joint.continuous
    exact Continuous.comp (g := fun p : ℂ × PeriodOneHminusOne => hillHminusDirichlet p.2 p.1)
      (f := fun p : T × ℝ => ((p.2 : ℂ),Q p.1)) hc
      ((Complex.continuous_ofReal.comp continuous_snd).prodMk (hQ.comp continuous_fst))
  constructor
  · change IsClosed A
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro t0 ht0
    obtain ⟨U,hU,hqU,L,hlower⟩ := exists_hillHminusDirichlet_local_uniform_lower_bound (Q t0) (hr t0)
    let K : Set T := {t | ∃ x ∈ Icc L (max L (b t)), hillHminusDirichlet (Q t) x = 0}
    have hK : IsClosed K := isClosed_exists_zero_in_variable_Icc _ (fun _ => L) (fun t => max L (b t))
      hF continuous_const (continuous_const.max hb) (fun _ => le_max_left _ _)
    have hlocal (t : T) (ht : Q t ∈ U) : t ∈ A ↔ t ∈ K := by
      constructor
      · rintro ⟨x,hx,hz⟩
        exact ⟨x,⟨(hlower (Q t) ht (hr t) x hz).le,hx.trans (le_max_right _ _)⟩,hz⟩
      · rintro ⟨x,hx,hz⟩
        have hl := hlower (Q t) ht (hr t) x hz
        have hx' : x ≤ b t := by
          rcases (le_max_iff.mp hx.2) with h | h
          · exact False.elim (not_le_of_gt hl h)
          · exact h
        exact ⟨x,hx',hz⟩
    have htK : t0 ∉ K := fun h => ht0 ((hlocal t0 hqU).mpr h)
    have hN := ((hU.preimage hQ).inter hK.isOpen_compl).mem_nhds ⟨hqU,htK⟩
    apply Filter.mem_of_superset hN
    intro t ht hA
    exact ht.2 ((hlocal t ht.1).mp hA)
  · change IsOpen A
    apply isOpen_iff_mem_nhds.mpr
    rintro t0 ⟨x,hx,hz⟩
    obtain ⟨a,ha,hax,he⟩ := exists_hillHminusDirichlet_analytic_real_root_branch (Q t0) (hr t0) x hz
    have hbranch : ∀ᶠ t in 𝓝 t0, hillHminusDirichlet (Q t) (a (Q t)) = 0 ∧ (a (Q t)).im = 0 := by
      filter_upwards [hQ.continuousAt.tendsto.eventually he] with t ht
      exact ⟨ht.1,ht.2 (hr t)⟩
    have hac : ContinuousAt (fun t => (a (Q t)).re) t0 :=
      Complex.continuous_re.continuousAt.comp (ha.continuousAt.comp hQ.continuousAt)
    have htop : (a (Q t0)).re < hillHminusRealLabels (Q t0) (hr t0) 1 := by
      rw [hax,ofReal_re]
      exact lt_of_le_of_lt hx (hillHminusRealLabels_band_strict (Q t0) (hr t0) 0)
    have hcollar : ∀ᶠ t in 𝓝 t0, (a (Q t)).re < hillHminusRealLabels (Q t) (hr t) 1 :=
      hac.eventually_lt (continuous_hillHminusRealLabels_family Q hQ hr 1).continuousAt htop
    filter_upwards [hbranch,hcollar] with t ht hlt
    have heq : ((a (Q t)).re : ℂ) = a (Q t) := by apply Complex.ext <;> simp [ht.2]
    have hzero : hillHminusDirichlet (Q t) ((a (Q t)).re) = 0 := by rw [heq]; exact ht.1
    refine ⟨(a (Q t)).re,?_,hzero⟩
    by_contra! hbad
    exact hillHminusDirichlet_ne_zero_on_open_band (Q t) (hr t) 0 _ ⟨hbad,hlt⟩ hzero

theorem hillHminusDirichlet_ne_zero_at_or_below_lowest
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (x : ℝ)
    (hx : x ≤ hillHminusRealLabels q hr 0) : hillHminusDirichlet q x ≠ 0 := by
  intro hz
  let Q : ℝ → PeriodOneHminusOne := fun t => (t : ℂ) • q
  have hQ : Continuous Q := Complex.continuous_ofReal.smul continuous_const
  have hQr (t : ℝ) : IsRealPeriodOneHminusOne (Q t) := hr.smul_real t
  have hc := isClopen_hillHminusDirichlet_lower_root_family Q hQ hQr
  have h1 : (1 : ℝ) ∈ {t : ℝ | ∃ a : ℝ, a ≤ hillHminusRealLabels (Q t) (hQr t) 0 ∧
      hillHminusDirichlet (Q t) a = 0} := by
    simpa only [Q,ofReal_one,one_smul,mem_ofPred_eq] using (show ∃ a : ℝ,
      a ≤ hillHminusRealLabels q hr 0 ∧ hillHminusDirichlet q a = 0 from ⟨x,hx,hz⟩)
  have hall := hc.eq_univ ⟨1,h1⟩
  have h0 : (0 : ℝ) ∈ {t : ℝ | ∃ a : ℝ, a ≤ hillHminusRealLabels (Q t) (hQr t) 0 ∧
      hillHminusDirichlet (Q t) a = 0} := by rw [hall]; trivial
  obtain ⟨a,ha,haz⟩ := h0
  have hQ0 : Q 0 = 0 := by simp [Q]
  simp only [Q, ofReal_zero, zero_smul, hillHminusRealLabels_zero] at ha
  have han : a ≤ 0 := by simpa [freeHillValue] using ha
  rw [hQ0] at haz
  exact hillHminusDirichlet_free_ne_zero_of_nonpos a han haz

end NLS.KdV
