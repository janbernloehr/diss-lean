import NLS.Articles.KdVPseudomeasures.SpectralReality
import NLS.Articles.KdVPseudomeasures.SpectralCoefficients
import NLS.KdV.PseudomeasureRealPairs

/-!
# Actual ordered high pairs for the original source potentials

Each pair consists of actual original H1-domain eigenvalues, exhausts its whole
corrected strip, and retains the physical algebraic multiplicities. One cutoff
chosen before the original potential on each norm ball constructs an ordered
family with uniformly bounded endpoint-weighted gap widths. This is the actual
high spectral tail; its assignment to global canonical slots needs the central
count and global localization, which are not assumed here.
-/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- An actual physical high pair, parametrized by the original article potential. -/
def SourceHillRealPair (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (n : ℕ) : Type :=
  EndpointHillRealPair r hr.1 hr.2 (sourceEndpointCoefficients r q.val) n

/-- Construct the actual ordered pair of an original real mean-zero period-one potential. -/
def sourceHillRealPair (r : ℝ) (hr : AdmissiblePredualOrder r) (n : ℕ) (hn : 1 ≤ n)
    (q : Potential r) (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2) :
    SourceHillRealPair r hr q n := by
  apply endpointHillRealPair r hr.1 hr.2 n hn (sourceEndpointCoefficients r q.val)
    (by simpa only [norm_sourceEndpointCoefficients] using hs)
  rw [sourceEndpointCoefficients_HminusOne_val]
  exact q.property.1

variable (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (n : ℕ)

/-- The source pair exhausts the actual original operator spectrum on its full corrected strip. -/
theorem SourceHillRealPair.spectrum_iff (p : SourceHillRealPair r hr q n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    z ∈ sourceHillSpectrum r hr q.val ↔ z = (p.left:ℂ) ∨ z = (p.right:ℂ) := by
  rw [sourceHillSpectrum_eq]
  exact EndpointHillRealPair.spectrum_iff p z hz

/-- Actual original algebraic multiplicities are precisely the endpoint repetitions. -/
theorem SourceHillRealPair.multiplicities (p : SourceHillRealPair r hr q n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    sourceHillAlgebraicMultiplicity r hr q.val z = ({(p.left:ℂ),(p.right:ℂ)}:Multiset ℂ).count z := by
  rw [sourceHillAlgebraicMultiplicity_eq]
  exact EndpointHillRealPair.multiplicities p z hz

/-- The entire original physical source pair is unique. -/
theorem SourceHillRealPair.unique (p s : SourceHillRealPair r hr q n) : p = s :=
  EndpointHillRealPair.unique r hr.1 hr.2 n (sourceEndpointCoefficients r q.val) p s

/-- The original left spectral endpoint has an actual nonzero full-domain H1 eigenvector. -/
theorem SourceHillRealPair.left_has_eigenvector (p : SourceHillRealPair r hr q n) :
    ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
      singularHillOperator (potentialHminusOne r hr q) f = (p.left:ℂ) • singularHillDomainInclusion f := by
  rw [← sourceEndpointCoefficients_HminusOne r hr q]
  exact EndpointHillRealPair.left_has_eigenvector r hr.1 hr.2 n (sourceEndpointCoefficients r q.val) p

/-- The original right spectral endpoint has an actual nonzero full-domain H1 eigenvector. -/
theorem SourceHillRealPair.right_has_eigenvector (p : SourceHillRealPair r hr q n) :
    ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
      singularHillOperator (potentialHminusOne r hr q) f = (p.right:ℂ) • singularHillDomainInclusion f := by
  rw [← sourceEndpointCoefficients_HminusOne r hr q]
  exact EndpointHillRealPair.right_has_eigenvector r hr.1 hr.2 n (sourceEndpointCoefficients r q.val) p

/-- The actual left source multiplicity is two at a collapsed gap and one otherwise. -/
theorem SourceHillRealPair.left_multiplicity (p : SourceHillRealPair r hr q n) :
    sourceHillAlgebraicMultiplicity r hr q.val p.left = if p.left = p.right then 2 else 1 := by
  rw [sourceHillAlgebraicMultiplicity_eq]
  exact EndpointHillRealPair.left_multiplicity r hr.1 hr.2 n (sourceEndpointCoefficients r q.val) p

/-- The actual right source multiplicity is two at a collapsed gap and one otherwise. -/
theorem SourceHillRealPair.right_multiplicity (p : SourceHillRealPair r hr q n) :
    sourceHillAlgebraicMultiplicity r hr q.val p.right = if p.left = p.right then 2 else 1 := by
  rw [sourceHillAlgebraicMultiplicity_eq]
  exact EndpointHillRealPair.right_multiplicity r hr.1 hr.2 n (sourceEndpointCoefficients r q.val) p

/-- The actual pair has the source's full-strip coupling estimate for its physical gap width. -/
theorem SourceHillRealPair.gap_le_couplingRadius (hn : 1 ≤ n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2) (p : SourceHillRealPair r hr q n) :
    p.right-p.left ≤ Real.sqrt 6*sourceEndpointCouplingRadius r hr n q.val := by
  exact EndpointHillRealPair.gap_le_couplingRadius r hr.1 hr.2 n hn (sourceEndpointCoefficients r q.val)
    (by simpa only [norm_sourceEndpointCoefficients] using hs) p

/-- Weighted widths of the actual high pairs are bounded in the exact original endpoint norm. -/
theorem SourceHillRealPair.normalized_gap_le (hn : 1 ≤ n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2) (p : SourceHillRealPair r hr q n) :
    (Weight.sobolev r (2*(n:ℤ)))⁻¹*(p.right-p.left) ≤ 2*Real.sqrt 6*‖q.val‖ := by
  simpa only [EndpointHillRealPair.gap, norm_sourceEndpointCoefficients] using
    EndpointHillRealPair.normalized_gap_le r hr.1 hr.2 n hn (sourceEndpointCoefficients r q.val)
      (by simpa only [norm_sourceEndpointCoefficients] using hs) p

/-- Distinct mode numbers give strictly separated original physical pairs. -/
theorem SourceHillRealPair.right_lt_left (hn : 1 ≤ n) (m : ℕ) (hnm : n < m)
    (p : SourceHillRealPair r hr q n) (s : SourceHillRealPair r hr q m) : p.right < s.left :=
  EndpointHillRealPair.right_lt_left r hr.1 hr.2 n hn (sourceEndpointCoefficients r q.val)
    (sourceEndpointCoefficients r q.val) m hnm p s

/-- One norm-ball cutoff constructs an actual ordered original spectral tail,
with the cutoff chosen before q and with all normalized gap widths uniformly bounded. -/
theorem source_uniform_ordered_real_tail (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : Potential r, ‖q.val‖ ≤ R →
      ∃ P : (n : ℕ) → N ≤ n → SourceHillRealPair r hr q n,
        (∀ (n : ℕ) (hn : N ≤ n), 0 ≤ (P n hn).right-(P n hn).left ∧
          (Weight.sobolev r (2*(n:ℤ)))⁻¹*((P n hn).right-(P n hn).left) ≤ 2*Real.sqrt 6*‖q.val‖) ∧
        ∀ (n m : ℕ) (hn : N ≤ n) (hm : N ≤ m), n < m → (P n hn).right < (P m hm).left := by
  obtain ⟨N, hN, hcut⟩ := exists_endpointHill_cutoff r hr.2 R
  refine ⟨N, hN, ?_⟩
  intro q hq
  have hs (n : ℕ) (hn : N ≤ n) : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hq (mul_nonneg (endpointHillConstant_pos r hr.2).le
      (Real.rpow_nonneg (by positivity) _))).trans (hcut n hn)
  let P : (n : ℕ) → N ≤ n → SourceHillRealPair r hr q n :=
    fun n hn => sourceHillRealPair r hr n (hN.trans hn) q (hs n hn)
  refine ⟨P, ?_, ?_⟩
  · intro n hn
    exact ⟨sub_nonneg.mpr (P n hn).ordered,
      SourceHillRealPair.normalized_gap_le r hr q n (hN.trans hn) (hs n hn) (P n hn)⟩
  · intro n m hn hm hnm
    exact SourceHillRealPair.right_lt_left r hr q n (hN.trans hn) m hnm (P n hn) (P m hm)

end NLS.Articles.KdVPseudomeasures
