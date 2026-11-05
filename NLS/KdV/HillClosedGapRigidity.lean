import NLS.KdV.HillHminusOneMiuraOutsideShift
import NLS.KdV.HillHminusOneMiuraCanonicalGaps
import NLS.KdV.HillHminusOneCanonicalGapSquares
import NLS.KdV.MiuraCanonicalRootReflection
import NLS.ZakharovShabat.SourceCentralGapConstant

/-! Borg rigidity for the ACTUAL original real Hminus-one Hill potential.
All closed positive Hill gaps force the actual shifted real Miura lift to
have only its central Dirac gap possibly open. The verified Dirac spatial
stationarity theorem forces that SAME scalar lift to be constant. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem periodOneMiura_constant (c : ℂ) :
    periodOneMiura (lp.single 2 0 c)=periodOneL2Inclusion (lp.single 2 0 (c^2)) := by
  rw [periodOneMiura,periodOneShiftedMiura,periodOneMassOperator_single,periodOneMiuraProduct_single]
  have he : periodOneL2Inclusion (lp.single 2 0 c)+c • periodOneL2Inclusion (lp.single 2 0 c)-
      periodOneL2Inclusion (lp.single 2 0 c)=c • periodOneL2Inclusion (lp.single 2 0 c) := by abel
  rw [he,← map_smul]
  congr 1
  ext k
  simp [lp.single_apply,Pi.single_apply,pow_two]

/-- Every genuine shifted real Miura lift of a real closed-gap Hill source
has all ACTUAL noncentral signed Dirac gaps closed. -/
theorem hillMiura_noncentral_gaps_closed_of_Hill_gapSquares_zero
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (hgap : ∀ n : ℕ+, hillHminusCanonicalGapSquare n q=0)
    (u : PeriodOneRealL2) (c : ℝ)
    (hu : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) :
    ∀ k : ℤ, k ≠ 0 → canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (hillMiuraRealSource u).val) (periodOnePotential_mem _) k=0 := by
  have hpos (n : ℕ) (hn : 0<n) : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (hillMiuraRealSource u).val) (periodOnePotential_mem _) (n:ℤ)=0 := by
    apply (hillHminus_gap_eq_zero_iff_miuraDirac_gap q hq u c hu hc n hn).mp
    have hs := hillHminusCanonicalGapSquare_eq_real q hq ⟨n,hn⟩
    have hz := hgap ⟨n,hn⟩
    rw [hs] at hz
    have hroot := (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp hz
    change ((hillHminusLabels q hq (2*n):ℂ)-(hillHminusLabels q hq (2*n-1):ℂ))=0 at hroot
    simpa only [Complex.ofReal_sub] using hroot
  intro k hk
  by_cases hkp : 0<k
  · have hn : (k.toNat:ℤ)=k := Int.toNat_of_nonneg hkp.le
    exact hn ▸ hpos k.toNat (by omega)
  · have hn : ((-k).toNat:ℤ)= -k := Int.toNat_of_nonneg (by omega)
    have hneg := (sourcePeriodicReflection_hillMiuraDiagonal u.val).gap_neg (-k)
    simp only [neg_neg] at hneg
    exact hneg.trans (hn ▸ hpos (-k).toNat (by omega))

/-- ACTUAL real closed-gap Hill potentials are constants, in the FULL
original Hminus-one domain, without assuming classical regularity. -/
theorem hillHminus_constant_of_all_gapSquares_zero
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (hgap : ∀ n : ℕ+, hillHminusCanonicalGapSquare n q=0) :
    ∃ d : ℂ, q=periodOneL2Inclusion (lp.single 2 0 d) := by
  obtain ⟨c,_,_,u,hu,houtside⟩ := exists_real_periodOneMiura_shift_outside_spectrum q hq 0
  have hu' : periodOneMiura u.val=q+periodOneL2Inclusion (lp.single 2 0 ((c^2:ℝ):ℂ)) := by
    simpa only [Complex.ofReal_pow] using hu
  have ho : -((c^2:ℝ):ℂ) ∉ singularHillSpectrum (periodOneOriginal q) := by
    simpa only [Complex.ofReal_pow] using houtside
  have hclosed := hillMiura_noncentral_gaps_closed_of_Hill_gapSquares_zero q hq hgap u (c^2) hu' ho
  have hconst : u.val=lp.single 2 0 (u.val 0) := by
    ext k
    by_cases hk : k=0
    · subst k; simp [lp.single_apply]
    · have h := (source_nonzero_coefficients_eq_zero_of_noncentral_gaps_closed (hillMiuraRealSource u) hclosed k hk).1
      have h' : u.val k=0 := by simpa only [hillMiuraRealSource,hillMiuraDiagonal_fst] using h
      simpa only [lp.single_apply,Pi.single_apply,if_neg hk] using h'
  have hm : periodOneMiura u.val=periodOneL2Inclusion (lp.single 2 0 ((u.val 0)^2)) := by
    exact (congrArg periodOneMiura hconst).trans (periodOneMiura_constant (u.val 0))
  refine ⟨(u.val 0)^2-(c:ℂ)^2,?_⟩
  apply Subtype.ext
  funext k
  have he := congrArg (fun a : PeriodOneHminusOne => a.val k) (hm.symm.trans hu)
  simp only [WeightedCoeff.add_val,periodOneL2Inclusion_apply] at he
  rw [periodOneL2Inclusion_apply]
  by_cases hk : k=0
  · subst k
    simp only [lp.single_apply,Pi.single_apply,ite_true] at he ⊢
    linear_combination -he
  · simp only [lp.single_apply,Pi.single_apply,if_neg hk] at he ⊢
    simpa only [add_zero] using he.symm

/-- Borg's zero-mean conclusion for the actual physical Hminus-one source. -/
theorem hillHminus_eq_zero_of_mean_zero_all_gapSquares_zero
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hz : q.val 0=0)
    (hgap : ∀ n : ℕ+, hillHminusCanonicalGapSquare n q=0) : q=0 := by
  obtain ⟨d,hd⟩ := hillHminus_constant_of_all_gapSquares_zero q hq hgap
  have h0 := congrArg (fun a : PeriodOneHminusOne => a.val 0) hd
  simp only [hz,periodOneL2Inclusion_apply,lp.single_apply,Pi.single_apply,ite_true] at h0
  rw [← h0] at hd
  simpa only [lp.single_zero,map_zero] using hd

end NLS.KdV
