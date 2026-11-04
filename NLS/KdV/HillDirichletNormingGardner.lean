import NLS.KdV.HillFilledMixedGardner
import NLS.KdV.HillDirichletSheetNontrivial
import NLS.Poisson.GardnerSpectralCalculus

/-! The ACTUAL Dirichlet eigenvalue/multiplier Gardner matrix.
The trace identity and resonant mixed bracket fix the normalization
-rho/2. Analytic continuation retains it at every closed periodic gap. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem hillHminus_Dirichlet_norming_Gardner_trace_relation
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    (1-((hillHminusDirichletNorming m q)^2)⁻¹)*
      NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) (hillHminusDirichletNorming m) q=
      (if n=m then hillHminusDirichletSheet m q/2 else 0) := by
  let T : PeriodOneHminusOne → ℂ := fun p => hillHminusDiscriminant p (hillHminusCanonicalDirichlet m p)
  let R : PeriodOneHminusOne → ℂ := fun p => (hillHminusDirichletNorming m p)⁻¹+hillHminusDirichletNorming m p
  have he : T =ᶠ[𝓝 q] R := by
    filter_upwards [isOpen_hillHminusCanonicalDirichletDomain.mem_nhds hq] with p hp
    exact hillHminusDiscriminant_at_canonicalDirichlet m p hp
  have hbr : NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) T q=
      NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) R q := by
    change NLS.Poisson.gardnerCotangentBivector (fderiv ℂ (hillHminusCanonicalDirichlet n) q) (fderiv ℂ T q)=
      NLS.Poisson.gardnerCotangentBivector (fderiv ℂ (hillHminusCanonicalDirichlet n) q) (fderiv ℂ R q)
    rw [he.fderiv_eq]
  have hrel := hbr.trans (NLS.Poisson.hminusGardnerBracket_inv_add_right
    (hillHminusCanonicalDirichlet n) (hillHminusDirichletNorming m) q
    (analyticOnNhd_hillHminusDirichletNorming m q hq).differentiableAt
    (hillHminusDirichletNorming_ne_zero m q hq))
  let D : ℂ × PeriodOneHminusOne → ℂ := fun t => hillHminusDiscriminant t.2 t.1
  have hmove := NLS.Poisson.hminusGardnerBracket_moving_spectral_right
    (hillHminusCanonicalDirichlet n) D (hillHminusCanonicalDirichlet m) q
    (analyticOnNhd_hillHminusDiscriminant_joint (hillHminusCanonicalDirichlet m q,q) (mem_univ _)).differentiableAt
    (analyticOnNhd_hillHminusCanonicalDirichlet m q hq).differentiableAt
  change NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) T q=
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n)
      (fun p => hillHminusDiscriminant p (hillHminusCanonicalDirichlet m q)) q+
    deriv (hillHminusDiscriminant q) (hillHminusCanonicalDirichlet m q)*
      NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) (hillHminusCanonicalDirichlet m) q at hmove
  rw [hmove,hillHminusCanonicalDirichlets_Gardner_commute n m q hq,mul_zero,add_zero,
    NLS.Poisson.hminusGardnerBracket_antisymm,hillHminus_discriminant_at_Dirichlet_Gardner_matrix n m q hq] at hrel
  rw [← hrel]
  by_cases hnm : n=m
  · subst m
    simp
    ring
  · simp [hnm]

theorem hillHminusDirichletNorming_trace_coefficient
    (m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    (1-((hillHminusDirichletNorming m q)^2)⁻¹)*hillHminusDirichletNorming m q=
      -hillHminusDirichletSheet m q := by
  rw [hillHminusDirichletSheet]
  have hn := hillHminusDirichletNorming_ne_zero m q hq
  field_simp
  ring

theorem hillHminus_Dirichlet_norming_Gardner_matrix
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) (hillHminusDirichletNorming m) q=
      (if n=m then -hillHminusDirichletNorming m q/2 else 0) := by
  let U := hillHminusCanonicalDirichletDomain
  let f : PeriodOneHminusOne → ℂ :=
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) (hillHminusDirichletNorming m)
  let g : PeriodOneHminusOne → ℂ := fun p => if n=m then -hillHminusDirichletNorming m p/2 else 0
  let h : PeriodOneHminusOne → ℂ := fun p => 1-((hillHminusDirichletNorming m p)^2)⁻¹
  have hf : AnalyticOnNhd ℂ f U := NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
    (analyticOnNhd_hillHminusCanonicalDirichlet n) (analyticOnNhd_hillHminusDirichletNorming m)
  have hg : AnalyticOnNhd ℂ g U := by
    by_cases hnm : n=m
    · have H : AnalyticOnNhd ℂ (fun p : PeriodOneHminusOne => -hillHminusDirichletNorming m p/2) U :=
        fun p hp => ((analyticOnNhd_hillHminusDirichletNorming m p hp).neg).div analyticAt_const (by norm_num)
      simpa only [g,if_pos hnm] using H
    · simpa only [g,if_neg hnm] using (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : PeriodOneHminusOne => (0:ℂ)) U)
  have hh : AnalyticOnNhd ℂ h U := by
    intro p hp
    exact analyticAt_const.sub (((analyticOnNhd_hillHminusDirichletNorming m p hp).pow 2).inv
      (pow_ne_zero 2 (hillHminusDirichletNorming_ne_zero m p hp)))
  obtain ⟨a,ha,hsa⟩ := exists_hillHminusDirichletSheet_ne_zero m
  have hne : h a ≠ 0 := by
    intro hz
    have ht := hillHminusDirichletNorming_trace_coefficient m a ha
    change h a*hillHminusDirichletNorming m a= -hillHminusDirichletSheet m a at ht
    rw [hz,zero_mul] at ht
    exact hsa (neg_eq_zero.mp ht.symm)
  have hprod (p : PeriodOneHminusOne) (hp : p ∈ U) : h p*(f p-g p)=0 := by
    have ht := hillHminus_Dirichlet_norming_Gardner_trace_relation n m p hp
    have hc := hillHminusDirichletNorming_trace_coefficient m p hp
    change h p*f p=(if n=m then hillHminusDirichletSheet m p/2 else 0) at ht
    change h p*hillHminusDirichletNorming m p= -hillHminusDirichletSheet m p at hc
    by_cases hnm : n=m
    · change h p*(f p-(if n=m then -hillHminusDirichletNorming m p/2 else 0))=0
      rw [if_pos hnm] at ht ⊢
      linear_combination ht+(1/2:ℂ)*hc
    · change h p*(f p-(if n=m then -hillHminusDirichletNorming m p/2 else 0))=0
      rw [if_neg hnm] at ht ⊢
      simpa only [sub_zero] using ht
  exact analytic_eqOn_of_mul_sub_eq_zero U isOpen_hillHminusCanonicalDirichletDomain
    isConnected_hillHminusCanonicalDirichletDomain.isPreconnected f g h hf hg hh a ha hne hprod hq

end NLS.KdV
