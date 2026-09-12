import NLS.SequenceSpaces.Pairing
import NLS.ZakharovShabat.PeriodicSpectrum

/-!
# Real-type potentials and the periodic spectrum

Real type in Fourier coordinates means conjugation together with reversal of
frequency between the two potential components. Domain vectors have absolutely
summable coefficients at every finite Banach exponent. Coefficient duality
therefore proves the symmetry argument of Proposition 1.1(iv), printed page 27.
-/

noncomputable section
open scoped ENNReal ComplexConjugate

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Fourier-coordinate real type: the second component is the conjugate
reflection of the first, as required by physical complex conjugation. -/
def IsRealType (φ : PairSpace p) : Prop := ∀ n : ℤ, φ.2 n = conj (φ.1 (-n))

omit [Fact (1 ≤ p)] in
/-- The reverse conjugate-reflection relation follows from real type. -/
theorem IsRealType.fst_eq (φ : PairSpace p) (hφ : IsRealType φ) (n : ℤ) :
    φ.1 n = conj (φ.2 (-n)) := by
  simpa using (congrArg conj (hφ (-n))).symm

omit [Fact (1 ≤ p)] in
@[simp] theorem isRealType_zero : IsRealType (0 : PairSpace p) := by
  intro n
  simp

omit [Fact (1 ≤ p)] in
/-- Opposite Fourier modes with conjugate amplitudes form a real-type potential. -/
theorem isRealType_single (k : ℤ) (a : ℂ) :
    IsRealType (lp.single p k a, lp.single p (-k) (conj a)) := by
  intro n
  change (lp.single p (-k) (conj a) : Coeff p) n = conj ((lp.single p k a : Coeff p) (-n))
  by_cases hn : n = -k
  · subst n
    simp
  · have hnk : -n ≠ k := by omega
    simp [lp.single_apply, hn, hnk]

/-- Duality with a domain vector is available for every finite Banach exponent. -/
def domainPairing (hp : p ≠ ⊤) (a : PairSpace p) (f : Domain p) : ℂ :=
  Coeff.pairing a.1 (WeightedCoeff.sobolevToL1CLM p hp f.1) +
    Coeff.pairing a.2 (WeightedCoeff.sobolevToL1CLM p hp f.2)

theorem domainPairing_add_left (hp : p ≠ ⊤) (a b : PairSpace p) (f : Domain p) :
    domainPairing hp (a + b) f = domainPairing hp a f + domainPairing hp b f := by
  simp only [domainPairing, Prod.fst_add, Prod.snd_add, Coeff.pairing_add_left]
  ring

theorem domainPairing_smul_left (hp : p ≠ ⊤) (z : ℂ) (a : PairSpace p) (f : Domain p) :
    domainPairing hp (z • a) f = z * domainPairing hp a f := by
  simp only [domainPairing, Prod.smul_fst, Prod.smul_snd, Coeff.pairing_smul_left]
  ring

/-- The domain inclusion pairing is Hermitian. -/
theorem domainPairing_inclusion_conj (hp : p ≠ ⊤) (f g : Domain p) :
    domainPairing hp (domainInclusion f) g = conj (domainPairing hp (domainInclusion g) f) := by
  simp only [domainPairing, domainInclusion_apply, Coeff.pairing, scalarInclusion_apply,
    WeightedCoeff.sobolevToL1CLM_apply, map_add, Complex.conj_tsum, map_mul, starRingEnd_self_apply]
  congr 1 <;> apply tsum_congr <;> intro n <;> ring

/-- The free diagonal symbols are real, giving symmetry in coefficient duality. -/
theorem domainPairing_freeOperator_conj (hp : p ≠ ⊤) (f g : Domain p) :
    domainPairing hp (freeOperator f) g = conj (domainPairing hp (freeOperator g) f) := by
  simp only [domainPairing, Coeff.pairing, freeOperator_fst_apply, freeOperator_snd_apply,
    WeightedCoeff.sobolevToL1CLM_apply, map_add, Complex.conj_tsum, map_mul,
    map_neg, Complex.conj_ofReal, map_intCast, starRingEnd_self_apply]
  congr 1 <;> apply tsum_congr <;> intro n <;> ring

/-- Real-type off-diagonal convolution is symmetric on the weighted domain. -/
theorem domainPairing_potentialOperator_conj (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : IsRealType φ) (f g : Domain p) :
    domainPairing hp (potentialOperator hp φ f) g =
      conj (domainPairing hp (potentialOperator hp φ g) f) := by
  let F₁ := WeightedCoeff.sobolevToL1CLM p hp f.1
  let F₂ := WeightedCoeff.sobolevToL1CLM p hp f.2
  let G₁ := WeightedCoeff.sobolevToL1CLM p hp g.1
  let G₂ := WeightedCoeff.sobolevToL1CLM p hp g.2
  change Coeff.pairing (Coeff.convolution φ.1 F₂) G₁ +
      Coeff.pairing (Coeff.convolution φ.2 F₁) G₂ =
    conj (Coeff.pairing (Coeff.convolution φ.1 G₂) F₁ +
      Coeff.pairing (Coeff.convolution φ.2 G₁) F₂)
  rw [map_add]
  exact (congrArg₂ (· + ·)
    (Coeff.pairing_convolution_conj φ.1 φ.2 hφ F₂ G₁)
    (Coeff.pairing_convolution_conj φ.2 φ.1 (IsRealType.fst_eq φ hφ) F₁ G₂)).trans (add_comm _ _)

/-- The full real-type operator is symmetric in coefficient duality. -/
theorem domainPairing_operator_conj (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : IsRealType φ) (f g : Domain p) :
    domainPairing hp (operator hp φ f) g = conj (domainPairing hp (operator hp φ g) f) := by
  change domainPairing hp (freeOperator f + potentialOperator hp φ f) g =
    conj (domainPairing hp (freeOperator g + potentialOperator hp φ g) f)
  rw [domainPairing_add_left, domainPairing_add_left, map_add,
    domainPairing_freeOperator_conj, domainPairing_potentialOperator_conj hp φ hφ]

/-- The duality energy of every nonzero domain vector is strictly positive. -/
theorem domainPairing_inclusion_re_pos (hp : p ≠ ⊤) (f : Domain p) (hf : f ≠ 0) :
    0 < (domainPairing hp (domainInclusion f) f).re := by
  have hcoeff (g : ScalarDomain p) (n : ℤ) :
      scalarInclusion g n = WeightedCoeff.sobolevToL1CLM p hp g n := by simp
  have h₁ := Coeff.pairing_self_re_nonneg (scalarInclusion f.1)
    (WeightedCoeff.sobolevToL1CLM p hp f.1) (hcoeff f.1)
  have h₂ := Coeff.pairing_self_re_nonneg (scalarInclusion f.2)
    (WeightedCoeff.sobolevToL1CLM p hp f.2) (hcoeff f.2)
  change 0 < (Coeff.pairing (scalarInclusion f.1) (WeightedCoeff.sobolevToL1CLM p hp f.1) +
    Coeff.pairing (scalarInclusion f.2) (WeightedCoeff.sobolevToL1CLM p hp f.2)).re
  rw [Complex.add_re]
  by_cases h : f.1 = 0
  · have hne : scalarInclusion f.2 ≠ 0 := by
      intro he
      have : f.2 = 0 := scalarInclusion_injective (he.trans (map_zero scalarInclusion).symm)
      exact hf (Prod.ext h this)
    exact add_pos_of_nonneg_of_pos h₁ (Coeff.pairing_self_re_pos _ _ (hcoeff f.2) hne)
  · have hne : scalarInclusion f.1 ≠ 0 := by
      intro he
      exact h (scalarInclusion_injective (he.trans (map_zero scalarInclusion).symm))
    exact add_pos_of_pos_of_nonneg (Coeff.pairing_self_re_pos _ _ (hcoeff f.1) hne) h₂

/-- Every eigenvalue of a real-type potential is real, at all finite Banach exponents. -/
theorem eigenvalue_im_eq_zero_of_realType (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : IsRealType φ) (z : ℂ) (f : Domain p) (hf : f ≠ 0)
    (he : operator hp φ f = z • domainInclusion f) : z.im = 0 := by
  let E := domainPairing hp (domainInclusion f) f
  have hE : conj E = E := (domainPairing_inclusion_conj hp f f).symm
  have hne : E ≠ 0 := by
    intro h
    have hpos := domainPairing_inclusion_re_pos hp f hf
    change 0 < E.re at hpos
    rw [h, Complex.zero_re] at hpos
    exact (lt_irrefl 0) hpos
  have hs := domainPairing_operator_conj hp φ hφ f f
  rw [he, domainPairing_smul_left] at hs
  change z * E = conj (z * E) at hs
  rw [map_mul, hE] at hs
  exact Complex.conj_eq_iff_im.mp ((mul_right_cancel₀ hne hs).symm)

/-- Proposition 1.1(iv) in coefficient space: the entire periodic spectrum is real. -/
theorem periodicSpectrum_im_eq_zero_of_realType (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : IsRealType φ) (z : ℂ) (hz : z ∈ periodicSpectrum hp φ) : z.im = 0 := by
  obtain ⟨f, hf, he⟩ := (mem_periodicSpectrum_iff_exists_eigenvector hp φ z).mp hz
  exact eigenvalue_im_eq_zero_of_realType hp φ hφ z f hf he

/-- Every nonreal parameter is in the resolvent set of a real-type potential. -/
theorem mem_resolventSet_of_realType_of_im_ne_zero (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : IsRealType φ) (z : ℂ) (hz : z.im ≠ 0) : z ∈ resolventSet hp φ := by
  by_contra h
  exact hz (periodicSpectrum_im_eq_zero_of_realType hp φ hφ z h)

end NLS.ZakharovShabat
