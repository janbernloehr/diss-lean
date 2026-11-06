import NLS.ZakharovShabat.NLSRiccatiPolynomialRemainder
import NLS.ZakharovShabat.NLSOddHamiltonianReducedPolynomial
import NLS.ZakharovShabat.SobolevOddHamiltonianReal
import NLS.ZakharovShabat.OddHamiltonianRemainderEstimate
import NLS.ZakharovShabat.SourceLemmaH1
import NLS.ZakharovShabat.SourceCorollaryH2

/-!
# Appendix B: actual differential-polynomial statements

Index k in the library denotes the article's density u_(k+1). The polynomial
is defined by the Riccati recurrence, independently of the spectral actions.
This module exposes the all-order polynomial content of Lemma 21 and the
smooth real-source form of Corollary 22 in the library Hamiltonian convention.
The sharp H^m version and the article's raw Riccati Hamiltonian convention
are retained by the Sobolev statements below.
-/
noncomputable section
open MvPolynomial NLS.DifferentialPolynomial NLS.ZakharovShabat NLS.Fourier
open scoped ContDiff
namespace NLS.Articles.DNLSEstimates

/-- Lemma 21: the actual recurrence polynomial has its stated leading jet,
homogeneous weight, derivative bound, jet order, and field balance. -/
theorem lemma_twenty_one_polynomial (k : ℕ) :
    ∃ q : DifferentialPolynomial.Polynomial,
      nlsRiccatiPolynomial k = -X (true,k) + q ∧
      q.IsWeightedHomogeneous totalWeight (k+1) ∧
      DerivativeOrderLE q ((k : ℤ)-2) ∧
      (∀ v : Jet, v ∈ q.vars → (v.2 : ℤ) ≤ (k : ℤ)-2) ∧
      (X (false,0)*q).IsWeightedHomogeneous totalWeight ((k : ℤ)+2) ∧
      (X (false,0)*q).IsWeightedHomogeneous fieldCharge 0 ∧
      DerivativeOrderLE (X (false,0)*q) ((k : ℤ)-2) := by
  obtain ⟨hw,hc,hd⟩ := nlsRiccatiRemainder_hamiltonian_grades k
  refine ⟨nlsRiccatiRemainder k, ?_, nlsRiccatiRemainder_totalWeight k,
    nlsRiccatiRemainder_derivativeOrder k,
    fun v hv => nlsRiccatiRemainder_vars k v hv, hw, hc, hd⟩
  simp [nlsRiccatiRemainder]

/-- Lemma 21's polynomial identity evaluates to the literal physical Riccati
density for every smooth pair, rather than a replacement recurrence. -/
theorem lemma_twenty_one_evaluation (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (k : ℕ) :
    nlsRiccatiDensity a b k =
      -iteratedDeriv k b + evaluate a b (nlsRiccatiRemainder k) :=
  nlsRiccatiDensity_eq_leading_add_remainder a b ha hb k

/-- Lemma 21 at its stated H^(k-1) regularity, with k=s+1. Equality is
of every original Fourier coefficient of the independently constructed
weak H^-1 Riccati density. The remainder is the actual lower-jet field. -/
theorem lemma_twenty_one_weak (s : ℕ) (a : SobolevSource s) (j : ℤ) :
    (weakSobolevRiccatiDensity s a).val j =
      -(2*Complex.I*(Real.pi : ℂ)*j)^(s+1)*a.2.val j +
        periodOneCoefficient
          (fun x : ℝ => sobolevPolynomialField s (nlsRiccatiRemainder (s+1)) a
            (x : AddCircle (2 : ℝ))) j := by
  rw [sourceLemmaH1, sourceH1RemainderCoefficient_eq_integral]

/-- Smooth real-source part of Corollary 22: one reduced polynomial is chosen
before every source, and retains the exact jet order, total weight and field
balance. The left side uses the library's positive-leading Hamiltonian. -/
theorem corollary_twenty_two_smooth (m : ℕ) (hm : 1 ≤ m) :
    ∃ q : DifferentialPolynomial.Polynomial,
      JetOrderLE q (m-1) ∧
      q.IsWeightedHomogeneous totalWeight (2*(m : ℤ)+2) ∧
      q.IsWeightedHomogeneous fieldCharge 0 ∧
      ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → Function.Periodic f 1 →
        classicalNLSHamiltonian f (fun x => star (f x)) (2*m+1) =
          ∫ x in (0 : ℝ)..1,
            (‖iteratedDeriv m f x‖^2 : ℝ) + evaluate f (fun y => star (f y)) q x :=
  exists_classicalNLSHamiltonian_odd_real_reduced_polynomial m hm

/-- The article's odd Hamiltonian on its sharp H^m domain, with the raw
Riccati normalization rather than the library's positive leading sign. -/
def articleOddHamiltonian (m : ℕ) (hm : 1 ≤ m) (a : SobolevSource m) : ℂ :=
  (-1 : ℂ)^(m+1) * sobolevOddHamiltonian m hm a

/-- Applying the printed leading sign recovers the library normalization. -/
theorem articleOddHamiltonian_normalized (m : ℕ) (hm : 1 ≤ m) (a : SobolevSource m) :
    (-1 : ℂ)^(m+1)*articleOddHamiltonian m hm a = sobolevOddHamiltonian m hm a := by
  rw [articleOddHamiltonian, ← mul_assoc, ← mul_pow]
  norm_num

/-- On actual smooth physical representatives the article normalization is
the literal Riccati mean from Appendix B. This fixes its meaning independently
of the action trace and of the decomposition to be proved. -/
theorem articleOddHamiltonian_eq_riccati_integral (m : ℕ) (hm : 1 ≤ m)
    (ab : SobolevSource m) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    articleOddHamiltonian m hm ab =
      ∫ x in (0 : ℝ)..1, a x*nlsRiccatiDensity a b (2*m) x := by
  rw [articleOddHamiltonian,
    sobolevOddHamiltonian_eq_classical m hm ab a b ha hb hpa hpb haq hbq,
    classicalNLSHamiltonian]
  have hp : (-1 : ℂ)^(m+1)*(-Complex.I)^(2*m+2) = 1 := by
    rw [show 2*m+2 = 2*(m+1) by omega, pow_mul]
    have hsq : (-Complex.I)^2 = (-1 : ℂ) := by norm_num [Complex.I_sq]
    rw [hsq, ← mul_pow]
    norm_num
  rw [← mul_assoc, hp, one_mul]

/-- Full real H^m content of Corollary 22, with one polynomial before the
potential, actual physical integral, exact leading energy and printed sign. -/
theorem corollary_twenty_two (m : ℕ) (hm : 1 ≤ m) :
    ∃ q : DifferentialPolynomial.Polynomial,
      JetOrderLE q (m-1) ∧
      q.IsWeightedHomogeneous totalWeight (2*(m : ℤ)+2) ∧
      q.IsWeightedHomogeneous fieldCharge 0 ∧
      ∀ a : realTypeHigherSobolevSourceLocus m,
        (-1 : ℂ)^(m+1)*articleOddHamiltonian m hm a.val =
          (‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2 : ℝ) +
          ∫ x in (0 : ℝ)..1, sobolevPolynomialField m q a.val (x : AddCircle (2 : ℝ)) := by
  obtain ⟨hq,hw,hc,_⟩ := Classical.choose_spec
    (exists_classicalNLSHamiltonian_odd_reduced_polynomial m hm)
  refine ⟨nlsOddReducedPolynomial m hm, hq, hw, hc, ?_⟩
  intro a
  rw [articleOddHamiltonian_normalized, sobolevOddHamiltonian_real_decomposition,
    sobolevPolynomialMean_eq_physical_integral]

/-- Corollary 22 as one literal physical integral, including the highest
weak derivative, on every nonsmooth real H^m input. -/
theorem corollary_twenty_two_integral (m : ℕ) (hm : 1 ≤ m) :
    ∃ q : DifferentialPolynomial.Polynomial,
      JetOrderLE q (m-1) ∧
      q.IsWeightedHomogeneous totalWeight (2*(m : ℤ)+2) ∧
      q.IsWeightedHomogeneous fieldCharge 0 ∧
      ∀ a : realTypeHigherSobolevSourceLocus m,
        (-1 : ℂ)^(m+1)*articleOddHamiltonian m hm a.val = ∫ x in (0 : ℝ)..1,
          (‖sobolevTopJetPhysical m hm a.val.1 x‖^2 : ℝ) +
          sobolevPolynomialField m q a.val (x : AddCircle (2 : ℝ)) := by
  simpa only [articleOddHamiltonian_normalized] using sourceCorollaryH2 m hm

/-- The article phase has modulus one and preserves the Hamiltonian norm. -/
theorem articleOddHamiltonian_norm (m : ℕ) (hm : 1 ≤ m) (a : SobolevSource m) :
    ‖articleOddHamiltonian m hm a‖ = ‖sobolevOddHamiltonian m hm a‖ := by
  simp [articleOddHamiltonian, norm_pow]

/-- Lemma 14's absolute physical remainder estimate and Hamiltonian bound.
The source's factor 1+(L2 norm)^(4m) is retained; one constant works in both
bounds and is chosen before every real H^m potential. -/
theorem lemma_fourteen (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
      ((∫ x in (0 : ℝ)..1,
        ‖sobolevPolynomialField m (nlsOddReducedPolynomial m hm) a.val
          (x : AddCircle (2 : ℝ))‖) ≤
        ε*‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2 +
          C*(1+‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^(4*m))*
            ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^2) ∧
      (‖articleOddHamiltonian m hm a.val‖ ≤
        (1+ε)*‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2 +
          C*(1+‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^(4*m))*
            ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^2) := by
  obtain ⟨C₁,hC₁,habs⟩ := exists_sobolevOddRemainder_derivative_absorption m hm ε hε
  obtain ⟨C₂,hC₂,henergy⟩ := exists_sobolevOddHamiltonian_energy_estimates m hm ε hε
  have hterm (C : ℝ) (hC : C ≤ C₁+C₂) (L : ℝ) (hL : 0 ≤ L) :
      C*(1+L^(4*m))*L^2 ≤ (C₁+C₂)*(1+L^(4*m))*L^2 := by gcongr
  refine ⟨C₁+C₂, by positivity, ?_⟩
  intro a
  constructor
  · exact (habs a).trans (add_le_add le_rfl
      (hterm C₁ (by linarith) ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖
        (norm_nonneg _)))
  · rw [articleOddHamiltonian_norm]
    exact (henergy a).2.trans (add_le_add le_rfl
      (hterm C₂ (by linarith) ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖
        (norm_nonneg _)))

end NLS.Articles.DNLSEstimates
