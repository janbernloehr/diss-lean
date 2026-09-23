import NLS.ZakharovShabat.SourceMidpointDiscSeparation
import NLS.SequenceSpaces.PuncturedLattice
import NLS.SequenceSpaces.UniformHolderTails

/-!
# Midpoint quotient bounds for Lemma 10.8

The linear perturbation of the midpoint quotient is a displacement
sequence paired with the punctured reciprocal lattice. Hölder's
inequality bounds every finite off-diagonal sum uniformly in the
omitted index.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

set_option linter.style.haveILetI false in
/-- Absolute reciprocal rows of an `ℓᑫ` displacement are uniformly
bounded by the conjugate reciprocal-lattice norm. -/
theorem sum_norm_div_index_le {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : q ≠ ⊤) (α : Coeff q) (n : ℤ) (s : Finset ℤ)
    (hs : ∀ m ∈ s, m ≠ n) :
    ∑ m ∈ s, ‖α m‖ / |((m-n : ℤ) : ℝ)| ≤
      ‖α‖ * ‖Coeff.puncturedLattice q.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖ := by
  haveI : Fact (1 ≤ q.conjExponent) := ⟨by simp [ENNReal.conjExponent]⟩
  have hqc : 1 < q.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top
  let b : Coeff q.conjExponent := Coeff.shift n (Coeff.puncturedLattice q.conjExponent hqc)
  have hb (m : ℤ) (hm : m ≠ n) : ‖b m‖ = |((m-n : ℤ) : ℝ)|⁻¹ := by
    simp only [b, Coeff.shift_apply, Coeff.puncturedLattice_apply,
      if_neg (sub_ne_zero.mpr hm), norm_inv,
      Complex.norm_intCast]
  calc
    ∑ m ∈ s, ‖α m‖ / |((m-n : ℤ) : ℝ)| =
        ∑ m ∈ s, ‖α m*b m‖ := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [norm_mul, hb m (hs m hm), div_eq_mul_inv]
    _ ≤ ‖α‖ * ‖b‖ := Coeff.sum_norm_holderProduct_le α b s
    _ = _ := by simp [b]

/-- A midpoint quotient differs from one by the root-minus-midpoint
displacement divided by its midpoint denominator. -/
theorem midpoint_quotient_eq_one_add (σ τ z : ℂ) (hτ : τ ≠ z) :
    (σ-z)/(τ-z) = 1+(σ-τ)/(τ-z) := by
  have hden : τ-z ≠ 0 := sub_ne_zero.mpr hτ
  field_simp
  ring

/-- Disc separation bounds one midpoint perturbation by the physical
reciprocal-lattice factor. -/
theorem norm_midpoint_displacement_div_le
    (C : ℝ) (hC : 1 ≤ C) (n m : ℤ) (hnm : n ≠ m)
    (α τ z : ℂ)
    (hsep : |((n-m : ℤ) : ℝ)| ≤ C*‖τ-z‖) :
    ‖α/(τ-z)‖ ≤ C*(‖α‖/|((m-n : ℤ) : ℝ)|) := by
  have hd : 0 < |((n-m : ℤ) : ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast sub_ne_zero.mpr hnm
  have hCpos : 0 < C := by linarith
  have hb : 0 < ‖τ-z‖ := by nlinarith
  have hreal : |((n-m : ℤ) : ℝ)| = |((m-n : ℤ) : ℝ)| := by
    rw [show n-m = -(m-n) by ring, Int.cast_neg, abs_neg]
  rw [norm_div, ← hreal]
  have hinv : 1/‖τ-z‖ ≤ C/|((n-m : ℤ) : ℝ)| := by
    exact (div_le_div_iff₀ hb hd).mpr (by simpa using hsep)
  calc
    ‖α‖/‖τ-z‖ = ‖α‖*(1/‖τ-z‖) := by ring
    _ ≤ ‖α‖*(C/|((n-m : ℤ) : ℝ)|) :=
      mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
    _ = C*(‖α‖/|((n-m : ℤ) : ℝ)|) := by ring

/-- The finite midpoint quotient is uniformly controlled by the
`ℓᑫ` norm of the root-minus-midpoint displacement. -/
theorem norm_midpoint_quotient_product_sub_one_le
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ⊤)
    (α : Coeff q) (σ τ : ℤ → ℂ) (n : ℤ) (z : ℂ)
    (C : ℝ) (hC : 1 ≤ C) (s : Finset ℤ)
    (hs : ∀ m ∈ s, m ≠ n)
    (hα : ∀ m ∈ s, σ m-τ m = α m)
    (hsep : ∀ m ∈ s,
      |((n-m : ℤ) : ℝ)| ≤ C*‖τ m-z‖) :
    ‖(∏ m ∈ s, (σ m-z)/(τ m-z))-1‖ ≤
      Real.exp (C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖)-1 := by
  let u : ℤ → ℂ := fun m => α m/(τ m-z)
  have hden (m : ℤ) (hm : m ∈ s) : τ m ≠ z := by
    intro he
    have hd : 0 < |((n-m : ℤ) : ℝ)| := by
      apply abs_pos.mpr
      exact_mod_cast sub_ne_zero.mpr (Ne.symm (hs m hm))
    have h := hsep m hm
    rw [he, sub_self, norm_zero, mul_zero] at h
    linarith
  have hprod : (∏ m ∈ s, (1+u m)) =
      ∏ m ∈ s, (σ m-z)/(τ m-z) := by
    apply Finset.prod_congr rfl
    intro m hm
    rw [midpoint_quotient_eq_one_add (σ m) (τ m) z (hden m hm), hα m hm]
  have hsum : (∑ m ∈ s, ‖u m‖) ≤
      C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖ := by
    calc
      _ ≤ ∑ m ∈ s, C*(‖α m‖/|((m-n : ℤ) : ℝ)|) := by
        apply Finset.sum_le_sum
        intro m hm
        exact norm_midpoint_displacement_div_le C hC n m
          (Ne.symm (hs m hm)) (α m) (τ m) z (hsep m hm)
      _ = C*(∑ m ∈ s, ‖α m‖/|((m-n : ℤ) : ℝ)|) := by
        rw [Finset.mul_sum]
      _ ≤ C*(‖α‖*‖Coeff.puncturedLattice q.conjExponent
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖) :=
        mul_le_mul_of_nonneg_left (sum_norm_div_index_le hq α n s hs)
          (by linarith)
      _ = _ := by ring
  rw [← hprod]
  exact (s.norm_prod_one_add_sub_one_le u).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)

/-- The literal finite midpoint quotient inherits the uniform bound
from midpoint-disc separation whenever `σ-τ` is represented in `ℓᑫ`. -/
theorem norm_sourceSingleRootMidpointPartialProduct_sub_one_le
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤)
    (φ ψ : CoeffPair p) (a : Coeff p) (α : Coeff q)
    (hα : ∀ m : ℤ,
      displacedRoots a m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m = α m)
    (N : ℕ) (ε C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-z‖)
    (n : ℤ) (M : ℕ) (z : ℂ)
    (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε n) :
    ‖sourceSingleRootMidpointPartialProduct hp hp1 n M (z,(a,ψ))-1‖ ≤
      Real.exp (C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖)-1 := by
  let s : Finset ℤ := (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase n
  have hs (m : ℤ) (hm : m ∈ s) : m ≠ n :=
    Finset.ne_of_mem_erase hm
  have hbound := norm_midpoint_quotient_product_sub_one_le hq α
    (displacedRoots a)
    (fun m => canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m) n z C hC s hs
    (fun m _ => hα m)
    (fun m hm => hsep n m (Ne.symm (hs m hm)) z hz)
  simpa only [sourceSingleRootMidpointPartialProduct, s] using hbound

/-- One connected source neighborhood controls every finite midpoint
quotient and every isolating disc with a common exponential constant. -/
theorem exists_local_sourceSingleRootMidpointPartialProduct_bound
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C : ℝ, 1 ≤ C ∧
          ∀ ψ ∈ V, ∀ a : Coeff p, ∀ α : Coeff q,
            (∀ m : ℤ,
              displacedRoots a m -
                canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
                  (periodOnePotential_mem ψ) m = α m) →
            ∀ n : ℤ, ∀ M : ℕ,
              ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                ‖sourceSingleRootMidpointPartialProduct hp hp1 n M (z,(a,ψ))-1‖ ≤
                  Real.exp (C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
                    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖)-1 := by
  obtain ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,hC,hsep⟩ :=
    exists_local_source_midpoint_index_separation hp hp1 φ hφ
  refine ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,hC,?_⟩
  intro ψ hψ a α hα n M z hz
  exact norm_sourceSingleRootMidpointPartialProduct_sub_one_le
    hp hp1 hq φ ψ a α hα N ε C hC (hsep ψ hψ) n M z hz

/-- Combining the midpoint and gap corrections gives a finite
full-quotient bound with separate displacement and squared-gap rows. -/
theorem norm_sourceSingleRootQuotientPartialProduct_sub_one_le_of_disc
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤)
    (φ ψ : CoeffPair p) (a : Coeff p) (α : Coeff q)
    (hα : ∀ m : ℤ,
      displacedRoots a m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m = α m)
    (N : ℕ) (ε C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-z‖)
    (n : ℤ) (M : ℕ) (z : ℂ)
    (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε n)
    (hsmall : ∀ m ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase n,
      ‖sourceSingleRootGapRadicand hp hp1 ψ m z‖ ≤ 1/2) :
    ‖sourceSingleRootQuotientPartialProduct hp hp1 n M (z,(a,ψ))-1‖ ≤
      Real.exp (C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖ +
        (C^2/2)*∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m)-1 := by
  let s : Finset ℤ := (Finset.Icc (-(M : ℤ)) (M : ℤ)).erase n
  let P := sourceSingleRootMidpointPartialProduct hp hp1 n M (z,(a,ψ))
  let G := sourceSingleRootGapCorrectionPartialProduct hp hp1 n M (z,(a,ψ))
  let A := C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖
  let B := (C^2/2)*∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m
  have hP : ‖P-1‖ ≤ Real.exp A-1 :=
    norm_sourceSingleRootMidpointPartialProduct_sub_one_le
      hp hp1 hq φ ψ a α hα N ε C hC hsep n M z hz
  have hPnorm : ‖P‖ ≤ Real.exp A := by
    calc
      ‖P‖ = ‖(P-1)+1‖ := by simp
      _ ≤ ‖P-1‖+‖(1:ℂ)‖ := norm_add_le _ _
      _ ≤ Real.exp A := by norm_num; linarith
  have hs : ∀ m ∈ s, m ≠ n := fun m hm => Finset.ne_of_mem_erase hm
  have hrow := sourceSingleRootGapRadicand_sum_le_reciprocal_row
    hp hp1 φ ψ N ε C hC hsep n z hz s hs
  have hB : 2*(∑ m ∈ s, ‖sourceSingleRootGapRadicand hp hp1 ψ m z‖) ≤ B := by
    dsimp [B]
    nlinarith [hrow]
  have hG : ‖G-1‖ ≤ Real.exp B-1 := by
    have h := norm_sourceSingleRootGapCorrectionPartialProduct_sub_one_le
      hp hp1 n M (z,(a,ψ)) hsmall
    exact h.trans (sub_le_sub_right (Real.exp_le_exp.mpr hB) 1)
  have hprod : ‖P‖*‖G-1‖ ≤ Real.exp A*(Real.exp B-1) := by
    calc
      _ ≤ Real.exp A*‖G-1‖ :=
        mul_le_mul_of_nonneg_right hPnorm (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hG (Real.exp_nonneg _)
  have heq : sourceSingleRootQuotientPartialProduct hp hp1 n M (z,(a,ψ))-1 =
      (P-1)+P*(G-1) := by
    rw [sourceSingleRootQuotientPartialProduct_factor]
    dsimp [P,G]
    ring
  rw [heq]
  calc
    ‖(P-1)+P*(G-1)‖ ≤ ‖P-1‖+‖P*(G-1)‖ := norm_add_le _ _
    _ = ‖P-1‖+‖P‖*‖G-1‖ := by rw [norm_mul]
    _ ≤ (Real.exp A-1)+Real.exp A*(Real.exp B-1) := add_le_add hP hprod
    _ = Real.exp (A+B)-1 := by rw [Real.exp_add]; ring

/-- A small full reciprocal-square row makes every off-diagonal
radicand small enough for the inverse-square-root estimate. -/
theorem sourceSingleRootGapRadicand_le_half_of_row_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-z‖)
    (i j : ℤ) (hij : i ≠ j)
    (z : ℂ) (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε i)
    (hrowSmall : (C^2/4)*
      (∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ i m) ≤ 1/2) :
    ‖sourceSingleRootGapRadicand hp hp1 ψ j z‖ ≤ 1/2 := by
  have hsum := (exists_sourceSquaredGapPhysicalRows hp hp1 ψ).choose_spec.1 i |>.1
  have hterm_nonneg (m : ℤ) :
      0 ≤ sourceSquaredGapReciprocalTerm hp hp1 ψ i m := by
    unfold sourceSquaredGapReciprocalTerm
    split_ifs
    · rfl
    · positivity
  have hterm : sourceSquaredGapReciprocalTerm hp hp1 ψ i j ≤
      ∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ i m := by
    have h := hsum.sum_le_tsum {j} (fun m _ => hterm_nonneg m)
    simpa using h
  have hCnonneg : 0 ≤ C^2/4 := by positivity
  calc
    ‖sourceSingleRootGapRadicand hp hp1 ψ j z‖ ≤
        (C^2/4)*sourceSquaredGapReciprocalTerm hp hp1 ψ i j :=
          sourceSingleRootGapRadicand_le_reciprocal_row
            hp hp1 φ ψ N ε C hC hsep i j hij z hz
    _ ≤ (C^2/4)*(∑' m : ℤ,
        sourceSquaredGapReciprocalTerm hp hp1 ψ i m) :=
          mul_le_mul_of_nonneg_left hterm hCnonneg
    _ ≤ 1/2 := hrowSmall

/-- A small squared-gap row gives the finite Lemma 10.8 quotient bound
without a separate smallness assumption for every factor. -/
theorem norm_sourceSingleRootQuotientPartialProduct_sub_one_le_of_small_row
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤)
    (φ ψ : CoeffPair p) (a : Coeff p) (α : Coeff q)
    (hα : ∀ m : ℤ,
      displacedRoots a m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m = α m)
    (N : ℕ) (ε C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-z‖)
    (n : ℤ) (M : ℕ) (z : ℂ)
    (hz : z ∈ sourceIsolatingDisc hp hp1 φ N ε n)
    (hrowSmall : (C^2/4)*
      (∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) ≤ 1/2) :
    ‖sourceSingleRootQuotientPartialProduct hp hp1 n M (z,(a,ψ))-1‖ ≤
      Real.exp (C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖ +
        (C^2/2)*∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m)-1 := by
  apply norm_sourceSingleRootQuotientPartialProduct_sub_one_le_of_disc
    hp hp1 hq φ ψ a α hα N ε C hC hsep n M z hz
  intro m hm
  exact sourceSingleRootGapRadicand_le_half_of_row_bound
    hp hp1 φ ψ N ε C hC hsep n m
      (Ne.symm (Finset.ne_of_mem_erase hm)) z hz hrowSmall

end NLS.ZakharovShabat
