import NLS.ZakharovShabat.SourceFrequencySequenceAnalytic
import NLS.ZakharovShabat.SourceAbelianMomentSquaredGapAtlas
import NLS.ZakharovShabat.SourceSecondMomentFrequencyTheorem20_4

/-! # Theorem 20.5: analytic frequency maps and refined asymptotics

The construction is unconditional for every finite source exponent above
one. At p = 2 it gives every finite target r > 1; at p > 2 it includes
r = p/2. The correction has locally uniform lp/3 + lq decompositions for
every finite q > 1, on a source neighborhood chosen before q.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The sequence maps at different source exponents agree on every
real potential with the same Fourier coefficients. This identifies the
constructed maps as extensions of the Hilbert frequency map. -/
theorem SourceAbelianMomentAtlas.frequencySequence_real_eq_of_coefficients
    {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {hp : p ≠ ⊤} {hq : q ≠ ⊤} {hp1 : 1 < p} {hq1 : 1 < q}
    {W P : Set (CoeffPair p)} {V Q : Set (CoeffPair q)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}
    (A : SourceAbelianMomentAtlas hp hp1 W s) (B : SourceAbelianMomentAtlas hq hq1 V t)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (ht : SourcePsiIsolatingComplexExtension hq hq1 Q t)
    (φ : realTypeSourceSubmodule p) (ψ : realTypeSourceSubmodule q)
    (hcoeff : ∀ j : ℤ, ψ.val.fst j = φ.val.fst j ∧ ψ.val.snd j = φ.val.snd j)
    (r : ℝ≥0∞) : A.frequencySequence r φ.val = B.frequencySequence r ψ.val := by
  unfold frequencySequence
  congr 1
  funext n
  exact A.renormalizedFrequency_real_eq_of_coefficients B hs ht φ ψ hcoeff n

/-- The refined target bounds imply the literal mixed remainder in
Theorem 20.5, including the quasi-normed p/3 range below one. -/
theorem frequencyCorrection_mixed_of_refined
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (A : SourceAbelianMomentAtlas hp hp1 W s) (T : Set (CoeffPair p))
    (hbound : ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∃ b : Coeff r,
        (∀ n, b n = A.frequencyCorrection ψ n) ∧ ‖b‖ ≤ C)
    (q : ℝ≥0∞) (hq : q ≠ ⊤) (hq1 : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T,
      ∃ a : Coeff (ENNReal.ofReal (p.toReal/3)), ∃ b : Coeff q,
        (∀ n, A.frequencyCorrection ψ n = a n + b n) ∧ ‖a‖ + ‖b‖ ≤ C := by
  by_cases ht : 1 < ENNReal.ofReal (p.toReal/3)
  · obtain ⟨C,hC,hb⟩ := hbound _ ENNReal.ofReal_ne_top ht le_rfl
    refine ⟨C,hC,?_⟩
    intro ψ hψ
    obtain ⟨a,ha,hn⟩ := hb ψ hψ
    exact ⟨a,0,by simpa using fun n => (ha n).symm,by simpa using hn⟩
  · obtain ⟨C,hC,hb⟩ := hbound q hq hq1 ((le_of_not_gt ht).trans hq1.le)
    refine ⟨C,hC,?_⟩
    intro ψ hψ
    obtain ⟨b,hb,hn⟩ := hb ψ hψ
    exact ⟨0,b,by simpa using fun n => (hb n).symm,by simpa using hn⟩

/-- Construct the analytic sequence map, physical finite-gap identity,
and locally uniform refined and mixed remainders of Theorem 20.5.
The target r = p/2 is admitted whenever p > 2; at p = 2 every r > 1
is admitted. All exponents in this statement are finite. -/
theorem exists_sourceFrequency_theorem20_5 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ A : SourceAbelianMomentAtlas hp hp1 W s, ∃ U : Set (CoeffPair p),
        IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ A.domain ∧
        (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r →
          ENNReal.ofReal (p.toReal/2) ≤ r →
          (∀ ψ ∈ U, ∀ n, A.frequencySequence r ψ n = A.renormalizedFrequency n ψ) ∧
            AnalyticOnNhd ℂ (A.frequencySequence r) U ∧
            AnalyticOnNhd ℝ (A.frequencySequence r) U) ∧
        (∀ (W₀ B X : Set (CoeffPair 2)) (t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n)
          (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t)
          (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ),
          A.renormalizedFrequency n φ.val = D.finiteGapFrequencyAtExponent hp hp1 φ hf n -
            4*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1 - (2*(n:ℂ)*Real.pi)^2) ∧
        ∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
          (∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
            ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∃ b : Coeff r,
              (∀ n, b n = A.frequencyCorrection ψ n) ∧ ‖b‖ ≤ C) ∧
          ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q →
            ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T,
              ∃ a : Coeff (ENNReal.ofReal (p.toReal/3)), ∃ b : Coeff q,
                (∀ n, A.frequencyCorrection ψ n = a n + b n) ∧ ‖a‖ + ‖b‖ ≤ C := by
  obtain ⟨W,V,_,_,hV,hrealV,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨U,hU,hUc,hreal,hUV,hanalytic,hlocal⟩ :=
    A.exists_analytic_frequencySequence hs hV hrealV
  refine ⟨W,s,A,U,hU,hUc,hreal,fun ψ hψ => (hUV hψ).1,?_,?_,?_⟩
  · intro r inst hr hr1 hpr
    obtain ⟨he,ha⟩ := hanalytic r hr hr1 hpr
    exact ⟨he,ha,ha.restrictScalars⟩
  · intro W₀ B X t D φ hf n
    exact A.renormalizedFrequency_eq_physical_finiteGap_all_exponents D
      hs.toSourcePsiIsolatingComplexExtension φ hf n
  · intro φ hφ
    obtain ⟨T,hT,hφT,hTU,hb⟩ := hlocal φ hφ
    exact ⟨T,hT,hφT,hTU,hb,frequencyCorrection_mixed_of_refined A T hb⟩

end NLS.ZakharovShabat
