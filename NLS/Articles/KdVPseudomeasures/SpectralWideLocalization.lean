import NLS.Articles.KdVPseudomeasures.SpectralGapTail
import NLS.KdV.PseudomeasureWideLocalization

/-!
# Exhaustion of the original high singular spectrum

One cutoff chosen before every original real physical potential on a norm ball
gives an ordered family that exhausts the entire sufficiently high real spectrum,
with the already proved original infinity-Sobolev gap-tail bound. The full
operator and every eigenvector retain the original H-minus-one/H1 domains.
The global lower bound and exact real central count are proved in subsequent
modules. Canonical global enumeration and physical source parity require further proofs.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- Every actual original complex-source spectral point in a wide strip is
in its narrow strip and obeys the original tight localization bound. -/
theorem sourceHillSpectrum_wide_localization (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 2 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ wideHillStrip n) (hzsp : z ∈ sourceHillSpectrum r hr q) :
    z ∈ reducedHillStrip n ∧ ‖z-(freeHillValue n:ℂ)‖ ≤ Real.sqrt (n:ℝ)/4 := by
  rw [sourceHillSpectrum_eq] at hzsp
  exact endpointHillSpectrum_wide_localization r hr.1 hr.2 n hn z hz (sourceEndpointCoefficients r q)
    (by simpa only [norm_sourceEndpointCoefficients] using hs) hzsp

/-- The actual original real high spectrum is covered by the corrected narrow strips. -/
theorem sourceHillSpectrum_real_high_cover (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (N : ℕ) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, N ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ sourceHillSpectrum r hr q.val)
    (hhigh : freeHillValue N-12*(N:ℝ) ≤ z.re) :
    ∃ n : ℕ, N ≤ n ∧ z ∈ reducedHillStrip n ∧ ‖z-(freeHillValue n:ℂ)‖ ≤ Real.sqrt (n:ℝ)/4 := by
  rw [sourceHillSpectrum_eq] at hz
  apply endpointHillSpectrum_real_high_cover r hr.1 hr.2 (sourceEndpointCoefficients r q.val)
    _ N hN _ z hz hhigh
  · rw [sourceEndpointCoefficients_HminusOne_val]
    exact q.property.1
  · intro n hn
    simpa only [norm_sourceEndpointCoefficients] using hs n hn

/-- The constructed original physical pairs exhaust every actual source
spectral point above the explicit lower edge of the high region. -/
theorem sourceHillSpectrum_high_iff_pair (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (N : ℕ) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, N ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2)
    (P : (n : ℕ) → N ≤ n → SourceHillRealPair r hr q n)
    (z : ℂ) (hhigh : freeHillValue N-12*(N:ℝ) ≤ z.re) :
    z ∈ sourceHillSpectrum r hr q.val ↔
      ∃ (n : ℕ) (hn : N ≤ n), z = ((P n hn).left:ℂ) ∨ z = ((P n hn).right:ℂ) := by
  rw [sourceHillSpectrum_eq]
  apply endpointHillSpectrum_high_iff_pair r hr.1 hr.2 (sourceEndpointCoefficients r q.val)
    _ N hN _ P z hhigh
  · rw [sourceEndpointCoefficients_HminusOne_val]
    exact q.property.1
  · intro n hn
    simpa only [norm_sourceEndpointCoefficients] using hs n hn

/-- A single original norm-ball cutoff supplies an actual ordered exhaustive
high spectrum and its genuine infinity-Sobolev gap sequence, before global low-mode indexing. -/
theorem source_uniform_exhaustive_real_tail (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : Potential r, ‖q.val‖ ≤ R →
      ∃ P : (n : ℕ) → N ≤ n → SourceHillRealPair r hr q n,
        (∀ (n m : ℕ) (hn : N ≤ n) (hm : N ≤ m), n < m → (P n hn).right < (P m hm).left) ∧
        (∀ z : ℂ, freeHillValue N-12*(N:ℝ) ≤ z.re →
          (z ∈ sourceHillSpectrum r hr q.val ↔
            ∃ (n : ℕ) (hn : N ≤ n), z = ((P n hn).left:ℂ) ∨ z = ((P n hn).right:ℂ))) ∧
        ∃ g : WeightedCoeff (Weight.sobolev (-r)) ⊤,
          (∀ k : ℤ, g.val k = sourceHighGapTailValues r hr q N P k) ∧ ‖g‖ ≤ 6*Real.sqrt 6*‖q.val‖ := by
  obtain ⟨N,hN,hcut⟩ := exists_wideEndpointHill_cutoff r hr.2 R
  refine ⟨N,hN,?_⟩
  intro q hq
  have hw (n : ℕ) (hn : N ≤ n) : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hq (mul_nonneg
      (mul_nonneg (by norm_num) (endpointHillConstant_pos r hr.2).le)
      (Real.rpow_nonneg (by positivity) _))).trans (hcut n hn)
  have hs (n : ℕ) (hn : N ≤ n) : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2 := by
    have h := endpointHill_small_of_wide_small r hr.2 n (sourceEndpointCoefficients r q.val)
      (by simpa only [norm_sourceEndpointCoefficients] using hw n hn)
    simpa only [norm_sourceEndpointCoefficients] using h
  have hN1 : 1 ≤ N := by omega
  let P : (n : ℕ) → N ≤ n → SourceHillRealPair r hr q n :=
    fun n hn => sourceHillRealPair r hr n (hN1.trans hn) q (hs n hn)
  refine ⟨P,?_,?_,sourceHighGapTail r hr q N hN1 P hs,
    sourceHighGapTail_apply r hr q N hN1 P hs,norm_sourceHighGapTail_le r hr q N hN1 P hs⟩
  · intro n m hn hm hnm
    exact SourceHillRealPair.right_lt_left r hr q n (hN1.trans hn) m hnm (P n hn) (P m hm)
  · intro z hz
    exact sourceHillSpectrum_high_iff_pair r hr q N hN hw P z hz

end NLS.Articles.KdVPseudomeasures
