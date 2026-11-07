import NLS.KdV.HillActionAmplitudeUniformBound
import NLS.KdV.HillAbelianCartesian

/-! ACTUAL action-normalized scalar factors, including the full Abelian
phase and the positive action amplitude. Their product is EXACTLY 2I.
Sequence regularity and Gardner canonicality are further obligations. -/
noncomputable section
open Set Complex
open scoped Classical
namespace NLS.KdV

def hillHminusActionAngleFactorPlus (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  hillHminusCanonicalActionAmplitude n q*hillHminusAbelianCartesianPlus n q

def hillHminusActionAngleFactorMinus (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  hillHminusCanonicalActionAmplitude n q*hillHminusAbelianCartesianMinus n q

theorem analyticOnNhd_hillHminusActionAngleFactorPlus (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusActionAngleFactorPlus n) hillHminusActionAmplitudeDomain := by
  intro q hq
  exact (analyticOnNhd_hillHminusCanonicalActionAmplitude n q hq).mul
    (analyticOnNhd_hillHminusAbelianCartesianPlus n q
      (hillHminusOffIndexBoundedDomain_subset_analytic (hillHminusActionAmplitudeDomain_subset_bounded hq)))

theorem analyticOnNhd_hillHminusActionAngleFactorMinus (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusActionAngleFactorMinus n) hillHminusActionAmplitudeDomain := by
  intro q hq
  exact (analyticOnNhd_hillHminusCanonicalActionAmplitude n q hq).mul
    (analyticOnNhd_hillHminusAbelianCartesianMinus n q
      (hillHminusOffIndexBoundedDomain_subset_analytic (hillHminusActionAmplitudeDomain_subset_bounded hq)))

theorem hillHminusActionAngleFactor_product (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAmplitudeDomain) :
    hillHminusActionAngleFactorPlus n q*hillHminusActionAngleFactorMinus n q = 2*hillHminusCanonicalAction n q := by
  unfold hillHminusActionAngleFactorPlus hillHminusActionAngleFactorMinus
  calc
    _ = (hillHminusCanonicalActionAmplitude n q)^2*
      (hillHminusAbelianCartesianPlus n q*hillHminusAbelianCartesianMinus n q) := by ring
    _ = (hillHminusCanonicalActionRatio n q/(4*((Real.pi:ℂ)*(n:ℕ))))*hillHminusCanonicalGapSquare n q := by
      rw [hillHminusCanonicalActionAmplitude_sq,hillHminusAbelianCartesian_product n q
        (hillHminusOffIndexBoundedDomain_subset_analytic (hillHminusActionAmplitudeDomain_subset_bounded hq))]
    _ = _ := by
      rw [hillHminusCanonicalAction_gap_factorization n q (hillHminusActionAmplitudeDomain_subset_ratio hq)]
      have hπ : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hn : ((n:ℕ):ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
      field_simp [hπ,hn]
      ring

theorem hillHminusActionAngleFactor_conjugate_of_real (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    hillHminusActionAngleFactorMinus n q = star (hillHminusActionAngleFactorPlus n q) := by
  have hi := (hillHminusCanonicalActionAmplitude_real_positive n q hr).1
  unfold hillHminusActionAngleFactorPlus hillHminusActionAngleFactorMinus
  rw [hillHminusAbelianCartesian_conjugate_of_real n q hr]
  change _ = (starRingEnd ℂ) _
  rw [map_mul,Complex.conj_eq_iff_im.mpr hi]
  rfl

theorem norm_hillHminusActionAngleFactor_of_real (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    ‖hillHminusActionAngleFactorPlus n q‖ = Real.sqrt (2*(hillHminusCanonicalAction n q).re) ∧
      ‖hillHminusActionAngleFactorMinus n q‖ = Real.sqrt (2*(hillHminusCanonicalAction n q).re) := by
  have hm := hillHminusActionAngleFactor_conjugate_of_real n q hr
  have hp := hillHminusActionAngleFactor_product n q (real_mem_hillHminusActionAmplitudeDomain q hr)
  change hillHminusActionAngleFactorMinus n q = (starRingEnd ℂ) (hillHminusActionAngleFactorPlus n q) at hm
  rw [hm,Complex.mul_conj] at hp
  have hs := congrArg Complex.re hp
  have htwo : (2*hillHminusCanonicalAction n q).re = 2*(hillHminusCanonicalAction n q).re := by simp
  rw [Complex.ofReal_re,Complex.normSq_eq_norm_sq,htwo] at hs
  have hn : ‖hillHminusActionAngleFactorPlus n q‖ = Real.sqrt (2*(hillHminusCanonicalAction n q).re) := by
    rw [← hs,Real.sqrt_sq (norm_nonneg _)]
  exact ⟨hn,by rw [hm,Complex.norm_conj]; exact hn⟩

end NLS.KdV
