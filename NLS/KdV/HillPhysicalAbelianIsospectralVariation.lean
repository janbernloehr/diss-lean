import NLS.KdV.HillAbelianCauchyIsospectral
import NLS.KdV.HillPhysicalOffIndexAbelianValue
import NLS.ComplexAnalysis.MovingQuadraticSheetTerminalFDeriv

/-! Actual off-index Abelian divisor variation in native isospectral
directions. The physical sheet is retained as a factor; the equation
holds at branch terminals and collapsed periodic gaps. The frequency
motion is converted to the actual original Dirichlet energy motion. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

theorem fderiv_physicalDirichletFrequency_energy (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (h : PeriodOneHminusOne) :
    (fderiv ℂ (hillHminusCanonicalDirichlet m) q) h =
      2*P.physicalDirichletFrequency ((m:ℕ):ℤ) q*
        ((fderiv ℂ (P.physicalDirichletFrequency ((m:ℕ):ℤ)) q) h) := by
  have hd := (((P.analytic_physicalDirichletFrequency ((m:ℕ):ℤ) q hq).differentiableAt.hasFDerivAt.pow 2).sub_const
    (P.parent.parent.miuraBall.actionBall.shift:ℂ)).fderiv
  change fderiv ℂ (fun a => P.physicalDirichletFrequency ((m:ℕ):ℤ) a^2-
    (P.parent.parent.miuraBall.actionBall.shift:ℂ)) q = _ at hd
  have he : (fun a => P.physicalDirichletFrequency ((m:ℕ):ℤ) a^2-
      (P.parent.parent.miuraBall.actionBall.shift:ℂ)) =ᶠ[𝓝 q] hillHminusCanonicalDirichlet m := by
    filter_upwards [P.source_open.mem_nhds hq] with a ha
    exact P.physicalDirichletFrequency_energy m a ha
  rw [he.fderiv_eq] at hd
  have hv := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h) hd
  simpa only [smul_apply,smul_eq_mul,Nat.reduceSub,pow_one,nsmul_eq_mul,Nat.cast_ofNat] using hv

theorem fderiv_physicalOffIndexAbelianValue_isospectral_frequency_cleared
    (P : HillProductEquationPatch) (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource)
    (hr : IsRealPeriodOneHminusOne q) (h : PeriodOneHminusOne)
    (hiso : ∀ E : ℂ, hillHminusDiscriminantCotangent E q h = 0) :
    hillHminusDirichletSheet m q*((fderiv ℂ (P.physicalOffIndexAbelianValue n m) q) h) =
      P.abelianGapRootMultiplier m (P.physicalDirichletFrequency ((m:ℕ):ℤ) q,q)*
        P.abelianGapNumerator n m (P.physicalDirichletFrequency ((m:ℕ):ℤ) q,q)*
          ((fderiv ℂ (P.physicalDirichletFrequency ((m:ℕ):ℤ)) q) h) := by
  let μ := P.physicalDirichletFrequency ((m:ℕ):ℤ)
  let H := P.offIndexAbelianFilledQuotient n m
  let M : PeriodOneHminusOne → ℂ := fun a => sourceStandardRootMidpoint
    (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)
  let G : PeriodOneHminusOne → ℂ := fun a => (canonicalPeriodicGap (by norm_num) (by norm_num)
    (periodOnePotential (P.sourcePsi a)) (periodOnePotential_mem _) ((m:ℕ):ℤ))^2
  let δ := hillHminusDirichletSheet m
  let K : PeriodOneHminusOne → ℂ := fun a => P.abelianGapRootMultiplier m (μ a,a)
  have hdisc : μ q ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) :=
    P.physicalDirichletFrequency_mem_disc q hq _
  have hμ := (P.analytic_physicalDirichletFrequency ((m:ℕ):ℤ) q hq.1).differentiableAt
  have hH := (P.analytic_offIndexAbelianFilledQuotient n m hmn (μ q,q) ⟨hdisc,hq.1⟩).differentiableAt
  have hM : DifferentiableAt ℂ M q :=
    (P.parent.parent.miuraBall.midpoint_analytic ((m:ℕ):ℤ) q
      (P.parent.subset (P.subset hq.1)).1).differentiableAt
  have hG : DifferentiableAt ℂ G q :=
    (P.parent.parent.miuraBall.dirac_gap_square_analytic ((m:ℕ):ℤ) q
      (P.parent.subset (P.subset hq.1)).1).differentiableAt
  have hδ := (analyticOnNhd_hillHminusDirichletSheet m q (P.source_subset_canonicalDirichlet hq.1)).differentiableAt
  have hK : DifferentiableAt ℂ K q :=
    (P.analytic_abelianGapRootMultiplier m (μ q,q) ⟨hdisc,hq.1⟩).differentiableAt.comp q
      (f := fun a : PeriodOneHminusOne => (μ a,a)) (hμ.prodMk differentiableAt_id)
  have hKne : K q ≠ 0 := P.abelianGapRootMultiplier_ne_zero m (μ q,q) ⟨hdisc,hq.1⟩
  have hsq : (fun a => δ a^2) =ᶠ[𝓝 q] (fun a => K a^2*((μ a-M a)^2-G a/4)) := by
    filter_upwards [P.physicalDirichletSource_open.mem_nhds hq] with a ha
    have hd := P.physicalDirichletFrequency_mem_disc a ha ((m:ℕ):ℤ)
    have hk : K a ≠ 0 := P.abelianGapRootMultiplier_ne_zero m (μ a,a) ⟨hd,ha.1⟩
    have hs := P.physicalDirichletRootCoefficient_sq m a ha
    change (δ a/K a)^2 = (μ a-M a)^2-G a/4 at hs
    rw [div_pow] at hs
    have he := (div_eq_iff (pow_ne_zero 2 hk)).mp hs
    linear_combination he
  exact fderiv_moving_quadratic_sheet_terminal_cleared H μ M G δ K
    (P.physicalOffIndexAbelianValue n m) q h (P.abelianGapNumerator n m (μ q,q))
    hH hμ hM hG hδ hK hKne
    (P.fderiv_symmetric_isospectral_eq_zero q hq.1 hr h hiso ((m:ℕ):ℤ))
    (P.fderiv_offIndexAbelianFilledQuotient_isospectral_eq_zero n m hmn q hq.1 hr h hiso (μ q) hdisc)
    hsq (Filter.Eventually.of_forall (fun _ => rfl))
    (P.offIndexAbelianFilledQuotient_equation n m hmn q hq.1 (μ q) hdisc)

theorem fderiv_physicalOffIndexAbelianValue_isospectral_cleared
    (P : HillProductEquationPatch) (n m : ℕ+) (hmn : m ≠ n)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource)
    (hr : IsRealPeriodOneHminusOne q) (h : PeriodOneHminusOne)
    (hiso : ∀ E : ℂ, hillHminusDiscriminantCotangent E q h = 0) :
    hillHminusDirichletSheet m q*((fderiv ℂ (P.physicalOffIndexAbelianValue n m) q) h) =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*
        ((fderiv ℂ (hillHminusCanonicalDirichlet m) q) h) := by
  let μ := P.physicalDirichletFrequency ((m:ℕ):ℤ) q
  let K := P.abelianGapRootMultiplier m (μ,q)
  have hK : K ≠ 0 := P.abelianGapRootMultiplier_ne_zero m (μ,q)
    ⟨P.physicalDirichletFrequency_mem_disc q hq _,hq.1⟩
  have hg : K*P.abelianGapNumerator n m (μ,q) =
      2*μ*hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q) := by
    change K*((2*μ*hillHminusCanonicalPsi n
      (μ^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q))/K) = _
    rw [mul_div_cancel₀ _ hK,P.physicalDirichletFrequency_energy m q hq.1]
  have hv := P.fderiv_physicalOffIndexAbelianValue_isospectral_frequency_cleared n m hmn q hq hr h hiso
  change hillHminusDirichletSheet m q*((fderiv ℂ (P.physicalOffIndexAbelianValue n m) q) h) =
    K*P.abelianGapNumerator n m (μ,q)*
      ((fderiv ℂ (P.physicalDirichletFrequency ((m:ℕ):ℤ)) q) h) at hv
  rw [hg] at hv
  rw [P.fderiv_physicalDirichletFrequency_energy m q hq.1 h]
  linear_combination hv

end NLS.KdV.HillProductEquationPatch
