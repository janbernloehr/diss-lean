import NLS.KdV.HillDirichletRootBranches
import NLS.KdV.HillFreeDirichlet
import NLS.ComplexAnalysis.ClosedIntervalRoots
import NLS.KdV.HillLabelContinuity

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem isClopen_hillDirichlet_gap_root_family
    {T : Type*} [TopologicalSpace T]
    (Q : T → WeightedCoeff SpectralWeight.one.toWeight 2) (hQ : Continuous Q)
    (hq : ∀ t, SpectralWeight.one.toCoeff (Q t) ∈ Coeff.paritySubspace 0)
    (hr : ∀ t, IsRealHillPotential (SpectralWeight.one.toCoeff (Q t)))
    (n : ℕ) (hn : 1≤n) :
    IsClopen {t : T | ∃ x∈Icc (hillRealLabels (Q t) (hq t) (hr t) (2*n-1))
      (hillRealLabels (Q t) (hq t) (hr t) (2*n)),
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (Q t)) x=0} := by
  let L (j : ℕ) (t : T) := hillRealLabels (Q t) (hq t) (hr t) j
  let P (t : T) := SpectralWeight.one.toCoeff (Q t)
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp hQ
  have hL (j : ℕ) : Continuous (L j) := continuous_hillRealLabels_family Q hQ hq hr j
  have hF : Continuous (fun p : T × ℝ => hillL2DirichletCharacteristic (P p.1) p.2) := by
    have hc : Continuous (fun p : ℂ × Coeff 2 => hillL2DirichletCharacteristic p.2 p.1) :=
      continuous_iff_continuousAt.mpr (fun p =>
        (analyticOnNhd_hillL2DirichletCharacteristic_joint p (mem_univ _)).continuousAt)
    have hm : Continuous (fun p : T × ℝ => ((p.2 : ℂ),P p.1)) :=
      (Complex.continuous_ofReal.comp continuous_snd).prodMk (hP.comp continuous_fst)
    convert! hc.comp hm using 1
  constructor
  · convert! isClosed_exists_zero_in_variable_Icc _ (L (2*n-1)) (L (2*n)) hF
      (hL _) (hL _) (fun t => monotone_hillRealLabels (Q t) (hq t) (hr t) (by omega)) using 1
  · apply isOpen_iff_mem_nhds.mpr
    rintro t0 ⟨x,hx,hzero⟩
    obtain ⟨a,ha,hax,he⟩ := exists_hillL2Dirichlet_analytic_real_root_branch (P t0) (hr t0) x hzero
    have hbranch : ∀ᶠ t in 𝓝 t0,
        hillL2DirichletCharacteristic (P t) (a (P t))=0 ∧ (a (P t)).im=0 := by
      filter_upwards [hP.continuousAt.tendsto.eventually he] with t ht
      exact ⟨ht.1,ht.2 (hr t)⟩
    have hac : ContinuousAt (fun t => (a (P t)).re) t0 :=
      Complex.continuous_re.continuousAt.comp (ha.continuousAt.comp hP.continuousAt)
    have hleft : L (2*n-2) t0 < (a (P t0)).re := by
      have hb := hillRealLabels_band_strict (Q t0) (hq t0) (hr t0) (n-1)
      rw [show 2*(n-1)=2*n-2 by omega,show 2*n-2+1=2*n-1 by omega] at hb
      rw [hax,Complex.ofReal_re]
      exact lt_of_lt_of_le hb hx.1
    have hright : (a (P t0)).re < L (2*n+1) t0 := by
      rw [hax,Complex.ofReal_re]
      exact lt_of_le_of_lt hx.2 (hillRealLabels_band_strict (Q t0) (hq t0) (hr t0) n)
    have hcollar : ∀ᶠ t in 𝓝 t0, (a (P t)).re ∈ Ioo (L (2*n-2) t) (L (2*n+1) t) :=
      ((hL _).continuousAt.eventually_lt hac hleft).and
        (hac.eventually_lt (hL _).continuousAt hright)
    filter_upwards [hbranch,hcollar] with t ht hc
    have heq : ((a (P t)).re : ℂ)=a (P t) := by
      apply Complex.ext <;> simp [ht.2]
    have hz : hillL2DirichletCharacteristic (P t) ((a (P t)).re)=0 := by rw [heq];exact ht.1
    exact ⟨(a (P t)).re,
      hillDirichlet_zero_mem_gap_of_between_neighbor_bands (Q t) (hq t) (hr t) n hn _ hc hz,hz⟩

theorem exists_hillL2Dirichlet_zero_in_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) :
    ∃ x∈Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)),
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) x=0 := by
  let Q : ℝ → WeightedCoeff SpectralWeight.one.toWeight 2 := fun t => (t : ℂ) • q
  have hQ : Continuous Q := Complex.continuous_ofReal.smul continuous_const
  have hqp (t : ℝ) : SpectralWeight.one.toCoeff (Q t) ∈ Coeff.paritySubspace 0 := by
    rw [map_smul]
    exact (Coeff.paritySubspace 0).smul_mem _ hq
  have hQr (t : ℝ) : IsRealHillPotential (SpectralWeight.one.toCoeff (Q t)) := by
    rw [map_smul]
    exact hr.smul_real t
  have hc := isClopen_hillDirichlet_gap_root_family Q hQ hqp hQr n hn
  have hzero : (0 : ℝ) ∈ {t : ℝ | ∃ x∈Icc
      (hillRealLabels (Q t) (hqp t) (hQr t) (2*n-1))
      (hillRealLabels (Q t) (hqp t) (hQr t) (2*n)),
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (Q t)) x=0} := by
    have hQ0 : Q 0=0 := by simp [Q]
    simp only [Set.mem_ofPred_eq]
    refine ⟨freeHillValue n,?_,?_⟩
    · simp only [hQ0,hillRealLabels_zero]
      have hl : (2*n-1+1)/2=n := by omega
      have hu : (2*n+1)/2=n := by omega
      simp [hl,hu]
    · rw [hQ0,map_zero]
      convert! hillL2DirichletCharacteristic_free_nat_root n hn using 1
      congr 1
      unfold freeHillValue
      push_cast
      ring
  have hall := hc.eq_univ ⟨0,hzero⟩
  have h1 : (1 : ℝ) ∈ {t : ℝ | ∃ x∈Icc
      (hillRealLabels (Q t) (hqp t) (hQr t) (2*n-1))
      (hillRealLabels (Q t) (hqp t) (hQr t) (2*n)),
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (Q t)) x=0} := by rw [hall];trivial
  simpa only [Q,Complex.ofReal_one,one_smul,mem_ofPred_eq] using h1

end NLS.KdV
