import NLS.KdV.HillDirichletSpectralLocalFlow

/-! Actual terminal equations along native indexed curves, including
branch endpoints. Other terminal data remain fixed, and the intrinsic
angle-pair scalar is constant wherever its two original gaps stay open. -/
noncomputable section
open Set Complex
namespace NLS.KdV

theorem hasDerivAt_hillHminusDirichlet_on_spectralCurve (j k : ℕ+)
    (γ : ℝ → PeriodOneHminusOne) (t : ℝ)
    (hγ : HasDerivAt γ (hillHminusDirichletSpectralVector k (γ t)) t)
    (hq : γ t ∈ hillHminusCanonicalDirichletDomain) :
    HasDerivAt (fun τ => hillHminusCanonicalDirichlet j (γ τ))
      (if j=k then hillHminusDirichletSheet j (γ t)/2 else 0) t := by
  have hc := ((analyticOnNhd_hillHminusCanonicalDirichlet j (γ t) hq).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hγ
  change HasDerivAt (fun τ => hillHminusCanonicalDirichlet j (γ τ))
    ((fderiv ℂ (hillHminusCanonicalDirichlet j) (γ t)) (hillHminusDirichletSpectralVector k (γ t))) t at hc
  rw [fderiv_hillHminusDirichlet_spectralVector j k (γ t) hq] at hc
  exact hc

theorem hasDerivAt_hillHminusNorming_on_spectralCurve (j k : ℕ+)
    (γ : ℝ → PeriodOneHminusOne) (t : ℝ)
    (hγ : HasDerivAt γ (hillHminusDirichletSpectralVector k (γ t)) t)
    (hq : γ t ∈ hillHminusCanonicalDirichletDomain) :
    HasDerivAt (fun τ => hillHminusDirichletNorming j (γ τ))
      (if j=k then -hillHminusDirichletNorming j (γ t)*
        deriv (hillHminusDiscriminant (γ t)) (hillHminusCanonicalDirichlet j (γ t))/2 else 0) t := by
  have hc := ((analyticOnNhd_hillHminusDirichletNorming j (γ t) hq).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hγ
  change HasDerivAt (fun τ => hillHminusDirichletNorming j (γ τ))
    ((fderiv ℂ (hillHminusDirichletNorming j) (γ t)) (hillHminusDirichletSpectralVector k (γ t))) t at hc
  rw [fderiv_hillHminusDirichletNorming_spectralVector j k (γ t) hq] at hc
  exact hc

theorem hasDerivAt_hillHminusSheet_on_spectralCurve (j k : ℕ+)
    (γ : ℝ → PeriodOneHminusOne) (t : ℝ)
    (hγ : HasDerivAt γ (hillHminusDirichletSpectralVector k (γ t)) t)
    (hq : γ t ∈ hillHminusCanonicalDirichletDomain) :
    HasDerivAt (fun τ => hillHminusDirichletSheet j (γ τ))
      (if j=k then hillHminusDiscriminant (γ t) (hillHminusCanonicalDirichlet j (γ t))*
        deriv (hillHminusDiscriminant (γ t)) (hillHminusCanonicalDirichlet j (γ t))/2 else 0) t := by
  have hc := ((analyticOnNhd_hillHminusDirichletSheet j (γ t) hq).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hγ
  change HasDerivAt (fun τ => hillHminusDirichletSheet j (γ τ))
    ((fderiv ℂ (hillHminusDirichletSheet j) (γ t)) (hillHminusDirichletSpectralVector k (γ t))) t at hc
  rw [fderiv_hillHminusDirichletSheet_spectralVector j k (γ t) hq] at hc
  exact hc

theorem hillHminus_other_terminal_eq_on_spectralCurve (j k : ℕ+) (hjk : j ≠ k)
    (γ : ℝ → PeriodOneHminusOne) (a b : ℝ)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (hillHminusDirichletSpectralVector k (γ t)) t)
    (hq : ∀ t ∈ Ioo a b, γ t ∈ hillHminusCanonicalDirichletDomain)
    (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) :
    (hillHminusCanonicalDirichlet j (γ u),hillHminusDirichletNorming j (γ u),hillHminusDirichletSheet j (γ u))=
      (hillHminusCanonicalDirichlet j (γ v),hillHminusDirichletNorming j (γ v),hillHminusDirichletSheet j (γ v)) := by
  have hd (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun τ => (hillHminusCanonicalDirichlet j (γ τ),
        hillHminusDirichletNorming j (γ τ),hillHminusDirichletSheet j (γ τ))) 0 t := by
    simpa only [if_neg hjk,Prod.zero_eq_mk] using
      (hasDerivAt_hillHminusDirichlet_on_spectralCurve j k γ t (hγ t ht) (hq t ht)).prodMk
        ((hasDerivAt_hillHminusNorming_on_spectralCurve j k γ t (hγ t ht) (hq t ht)).prodMk
          (hasDerivAt_hillHminusSheet_on_spectralCurve j k γ t (hγ t ht) (hq t ht)))
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hu hv

theorem hillHminusCompletePhasePair_eq_on_spectralCurve (n m k : ℕ+)
    (γ : ℝ → PeriodOneHminusOne) (a b : ℝ)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (hillHminusDirichletSpectralVector k (γ t)) t)
    (hr : ∀ t ∈ Ioo a b, IsRealPeriodOneHminusOne (γ t))
    (hn : ∀ t ∈ Ioo a b, hillHminusCanonicalGapSquare n (γ t) ≠ 0)
    (hm : ∀ t ∈ Ioo a b, hillHminusCanonicalGapSquare m (γ t) ≠ 0)
    (u v : ℝ) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) :
    hillHminusCompletePhasePairBracket n m (γ u)=hillHminusCompletePhasePairBracket n m (γ v) := by
  have hd (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun τ => hillHminusCompletePhasePairBracket n m (γ τ)) 0 t := by
    have hc := ((analyticOnNhd_hillHminusCompletePhasePairBracket n m (γ t)
      ⟨⟨real_mem_hillHminusOffIndexAnalyticDomain _ (hr t ht),hn t ht⟩,
        ⟨real_mem_hillHminusOffIndexAnalyticDomain _ (hr t ht),hm t ht⟩⟩).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hγ t ht)
    change HasDerivAt (fun τ => hillHminusCompletePhasePairBracket n m (γ τ))
      ((fderiv ℂ (hillHminusCompletePhasePairBracket n m) (γ t)) (hillHminusDirichletSpectralVector k (γ t))) t at hc
    rw [fderiv_hillHminusCompletePhasePair_spectralVector_eq_zero n m k (γ t) (hr t ht) (hn t ht) (hm t ht)] at hc
    exact hc
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hu hv

end NLS.KdV
