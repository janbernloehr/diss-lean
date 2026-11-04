import NLS.KdV.HillHminusOneDirichletMiuraLabels

/-! # One complex H^-1 neighborhood for all actual Dirichlet branches

The original NLS Dirichlet displacement is Banach analytic in ell2.
The exact phase-rotated Miura comparison and all-index ordered matching
turn its positive frequencies into the actual Hill Dirichlet energies.
Uniformly small high displacements and finitely many nonzero low roots
give one complex domain before every index, including collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem exists_hillHminusDirichlet_common_analytic_branches
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ c : ℝ, 0 < c ∧ ∃ V : Set PeriodOneHminusOne,
      ∃ mu : ℕ+ → PeriodOneHminusOne → ℂ, ∃ d : PeriodOneHminusOne → Coeff 2,
      IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ d V ∧
      (∀ n, AnalyticOnNhd ℂ (mu n) V) ∧
      (∀ p ∈ V, ∀ n, hillHminusDirichlet p (mu n p) = 0) ∧
      (∀ p ∈ V, ∀ hp : IsRealPeriodOneHminusOne p, ∀ n,
        mu n p = (hillHminusDirichletEnergy p hp n : ℂ)) ∧
      ∀ p ∈ V, ∀ n, mu n p = ((Real.pi : ℂ)*(n : ℕ)+d p (n : ℤ))^2-(c : ℂ)^2 := by
  classical
  obtain ⟨C,hqC,c,hcpos,hc,hreal⟩ := exists_hillHminus_real_Miura_chart q hr
  let F : PeriodOneHminusOne → CoeffPair 2 := fun p => hillDirichletMiuraSource (C.lift p)
  have hF : AnalyticOnNhd ℂ F C.domain := fun p hp =>
    (hillDirichletMiuraSource.analyticAt _).comp (C.lift_analytic p hp)
  have hFreal : IsRealType (CoeffPair.toMax 2 (F q)) := C.dirichlet_source_real q (hreal q hqC hr)
  obtain ⟨W,hW,hrealW,hdisp⟩ := exists_sourceBoundaryDisplacement_analytic_common_domain
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num)
  let V0 := C.domain ∩ F ⁻¹' W
  have hV0 : IsOpen V0 := hF.continuousOn.isOpen_inter_preimage C.domain_open hW
  have hqV0 : q ∈ V0 := ⟨hqC,hrealW hFreal⟩
  let d : PeriodOneHminusOne → Coeff 2 := fun p => sourceBoundaryDisplacement (by simp) (by norm_num) .dirichlet (F p)
  have hd : AnalyticOnNhd ℂ d V0 := fun p hp =>
    (hdisp .dirichlet _ hp.2).comp (f := F) (hF p hp.1)
  let a : ℤ → PeriodOneHminusOne → ℂ := fun n p =>
    canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet (F p) n
  have ha (n : ℤ) : AnalyticOnNhd ℂ (a n) V0 := by
    intro p hp
    have hh := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).analyticAt _).comp (hd p hp)
    have hh' : AnalyticAt ℂ (fun r => d r n+(Real.pi : ℂ)*n) p := hh.add analyticAt_const
    simpa only [d,sourceBoundaryDisplacement_apply,sub_add_cancel] using! hh'
  have haq (k : ℕ) (hk : 0 < k) : a (k : ℤ) q ≠ 0 := by
    have hpos := (canonicalDirichletMiuraRoot_re_pos_iff (C.lift q)
      (C.lift_real_of_profile_real q (hreal q hqC hr)) (k : ℤ)).mpr (by exact_mod_cast hk)
    intro hz
    change 0 < (a (k : ℤ) q).re at hpos
    rw [hz,zero_re] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨K,T,hT,hqT,htail⟩ := exists_local_sourceBoundaryRoots_small_tail
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num) .dirichlet (F q) hFreal
    (Real.pi/2) (by positivity)
  have hhead : ∀ᶠ p in 𝓝 q, ∀ k ∈ Finset.Icc 1 K, a (k : ℤ) p ≠ 0 := by
    rw [Finset.eventually_all]
    intro k hk
    exact ((ha (k : ℤ) q hqV0).continuousAt).eventually_ne (haq k (by simp only [Finset.mem_Icc] at hk; omega))
  obtain ⟨H,hHsub,hH,hqH⟩ := _root_.mem_nhds_iff.mp hhead
  let VT := C.domain ∩ F ⁻¹' T
  have hVT : IsOpen VT := hF.continuousOn.isOpen_inter_preimage C.domain_open hT
  let V := V0 ∩ (VT ∩ H)
  have hV : IsOpen V := hV0.inter (hVT.inter hH)
  have hVsub : V ⊆ V0 := inter_subset_left
  have hnonzero (p : PeriodOneHminusOne) (hp : p ∈ V) (n : ℕ+) : a (n : ℤ) p ≠ 0 := by
    by_cases hn : (n : ℕ) ≤ K
    · exact hHsub hp.2.2 (n : ℕ) (by simp only [Finset.mem_Icc]; exact ⟨n.property,hn⟩)
    · have ht := htail (F p) hp.2.1.2 (n : ℤ) (by simpa only [Int.natAbs_natCast] using lt_of_not_ge hn)
      intro hz
      change a (n : ℤ) p ∈ Metric.ball ((Real.pi : ℂ)*(n : ℤ)) (Real.pi/2) at ht
      rw [hz] at ht
      have hb : Real.pi*(n : ℝ) < Real.pi/2 := by
        simpa [Metric.mem_ball,dist_zero_left,norm_mul,Complex.norm_real,abs_of_pos Real.pi_pos] using ht
      have hpn : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.property
      nlinarith [Real.pi_pos]
  let mu : ℕ+ → PeriodOneHminusOne → ℂ := fun n p => a (n : ℤ) p^2-C.energyShift
  refine ⟨c,hcpos,V,mu,d,hV,⟨hqV0,⟨hqC,hqT⟩,hqH⟩,hd.mono hVsub,
    fun n => ((ha (n : ℤ)).mono hVsub).pow 2 |>.sub analyticOnNhd_const,?_,?_,?_⟩
  · intro p hp n
    apply (C.dirichlet_source_zero_iff p hp.1.1 _ (hnonzero p hp n)).mp
    apply (periodOneBoundaryCharacteristic_eq_zero_iff (by simp) (by norm_num) .dirichlet (F p) _).mpr
    exact (canonicalPeriodOneBoundaryRoots_exhaustive (by simp) (by norm_num) .dirichlet (F p) _).mpr ⟨(n : ℤ),rfl⟩
  · intro p hp hpr n
    exact (C.dirichletEnergy_eq_source_root_sq p hp.1.1 hpr c hc (hreal p hp.1.1 hpr) n).symm
  intro p _ n
  dsimp only [mu,d,a]
  rw [sourceBoundaryDisplacement_apply,hc]
  simp only [Int.cast_natCast]
  ring

end NLS.KdV
