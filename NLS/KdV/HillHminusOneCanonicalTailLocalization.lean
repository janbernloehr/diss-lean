import NLS.KdV.HillHminusOneCanonicalRealLabels
import NLS.KdV.HillHminusOneRealGapSquares

/-! # Uniform small localization of the actual canonical H^-1 tail

The intrinsic labels equal every ordered local high pair, independently
of its disc radius. The sharply confined physical pair therefore places
both canonical endpoints within n/8 of the free energy on one common
complex H^-1 neighborhood, with the estimate at every real input.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

theorem exists_hillHminus_canonical_tail_small_localization (q : PeriodOneHminusOne) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ ha : IsRealPeriodOneHminusOne a, ∀ n : ℕ, N ≤ n →
        |hillHminusRealLabels a ha (2*n-1)-freeHillValue n| ≤ (n : ℝ)/8 ∧
        |hillHminusRealLabels a ha (2*n)-freeHillValue n| ≤ (n : ℝ)/8 := by
  obtain ⟨r,hr,hrpi,Np,Vp,_,hVp,hqp,hpairs⟩ := exists_hillHminus_nonnegative_high_gap_squares q
  obtain ⟨Nl,s,Vl,_,hNl,hVl,hql,hlabels⟩ := exists_hillHminusRealLabels_common_spec q 2
  let N := max Np Nl
  refine ⟨N,Vp ∩ Vl,hNl.trans (le_max_right _ _),hVp.inter hVl,⟨hqp,hql⟩,?_⟩
  intro a ha hreal n hn
  have hnpos : 0 < n := by have h := hNl.trans (le_max_right Np Nl); omega
  let k : ℕ+ := ⟨n,hnpos⟩
  obtain ⟨_,_,_,hpairdata⟩ := hpairs k ((le_max_left Np Nl).trans hn)
  obtain ⟨l,u,_,hlu,hpair,hl,hu,_,_,_⟩ := hpairdata a ha.1 hreal
  obtain ⟨p,hpl,hpu⟩ := (hlabels a ha.2 hreal).high_pair k ((le_max_right Np Nl).trans hn)
  let t : HillHminusRealHighPair a k r := ⟨l,u,hlu,hpair⟩
  have he := p.endpoints_unique t
  have hleft : hillHminusRealLabels a hreal (2*n-1) = l := hpl.trans he.1
  have hright : hillHminusRealLabels a hreal (2*n) = u := hpu.trans he.2
  have hcenter : ((Real.pi : ℂ)*n)^2 = (freeHillValue n : ℂ) := by
    dsimp only [freeHillValue]
    push_cast
    ring
  have hrad : Real.pi*(n : ℝ)*r/32 ≤ (n : ℝ)/8 := by
    have hpi : Real.pi^2 < 16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
    have hpr := mul_le_mul_of_nonneg_left hrpi Real.pi_pos.le
    have hpr' : Real.pi*r ≤ 4 := by nlinarith
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hpr' hn0]
  constructor
  · rw [hleft]
    have hl' : (l : ℂ) ∈ ball (freeHillValue n : ℂ) (Real.pi*(n : ℝ)*r/32) := by
      have h := hl
      change (l : ℂ) ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℝ)*r/32) at h
      rwa [hcenter] at h
    have hx : |l-freeHillValue n| < Real.pi*(n : ℝ)*r/32 := by
      simpa only [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hl'
    exact hx.le.trans hrad
  · rw [hright]
    have hu' : (u : ℂ) ∈ ball (freeHillValue n : ℂ) (Real.pi*(n : ℝ)*r/32) := by
      have h := hu
      change (u : ℂ) ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℝ)*r/32) at h
      rwa [hcenter] at h
    have hx : |u-freeHillValue n| < Real.pi*(n : ℝ)*r/32 := by
      simpa only [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hu'
    exact hx.le.trans hrad

end NLS.KdV
