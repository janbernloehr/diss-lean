import NLS.ZakharovShabat.SourceAbelianMomentOffDiagonalNeighborhood

/-! # The off-diagonal assertion of Lemma 20.3

The actual cubic-gap coefficient splits into an lq part and an l(p/2)
part for every finite q greater than one. If p/2 is above one, the entire
coefficient already lies at that exponent; otherwise it lies in every
such lq. The same connected source neighborhood and local ball work
before q, and both row norms are uniform in the deleted index.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Lemma 20.3's exact off-diagonal formula with its two sequence
exponents, locally uniform on a connected almost-real neighborhood.
The theorem includes collapsed gaps and does not assume a moment estimate. -/
theorem SourceAbelianMomentAtlas.exists_lemma20_3_offDiagonal
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧ ∀ φ ∈ U, ∃ ρ : ℝ, 0 < ρ ∧ ball φ ρ ⊆ U ∧
        ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 ≤ M ∧
          ∀ ψ ∈ ball φ ρ, ∀ n : ℤ, ∃ a : Coeff q, ∃ b : Coeff (ENNReal.ofReal (p.toReal/2)),
            a n = 0 ∧ b n = 0 ∧ ‖a‖ ≤ M ∧ ‖b‖ ≤ M ∧
            (∀ k, a k+b k = sourceSecondMomentCubicCoefficient A n ψ k) ∧
            ∀ k : ℤ, k ≠ n → A.moment n k 2 ψ =
              (sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*(a k+b k) := by
  obtain ⟨U,hU,hUconn,hrealU,hUV,hlocal⟩ :=
    A.exists_almostReal_offDiagonal_secondMoment_coefficients hs hV hrealV
  refine ⟨U,hU,hUconn,hrealU,hUV,?_⟩
  intro φ hφ
  obtain ⟨ρ,hρ,hball,hrows⟩ := hlocal φ hφ
  refine ⟨ρ,hρ,hball,?_⟩
  intro q hq hq1
  by_cases hhalf : 1 < ENNReal.ofReal (p.toReal/2)
  · obtain ⟨M,hM,hb⟩ := hrows _ ENNReal.ofReal_ne_top hhalf le_rfl
    refine ⟨M,hM,?_⟩
    intro ψ hψ n
    obtain ⟨b,hb,hbn,hbM,hfactor⟩ := hb ψ hψ n
    refine ⟨0,b,by simp,hbn,?_,hbM,?_,?_⟩
    · simpa only [lp.norm_zero] using hM
    · intro k
      simpa only [lp.coeFn_zero,Pi.zero_apply,zero_add] using hb k
    · intro k hkn
      simpa only [lp.coeFn_zero,Pi.zero_apply,zero_add] using hfactor k hkn
  · have hpr : ENNReal.ofReal (p.toReal/2) ≤ q := (not_lt.mp hhalf).trans hq1.le
    obtain ⟨M,hM,hb⟩ := hrows q hq hq1 hpr
    refine ⟨M,hM,?_⟩
    intro ψ hψ n
    obtain ⟨a,ha,han,haM,hfactor⟩ := hb ψ hψ n
    refine ⟨a,0,han,by simp,haM,?_,?_,?_⟩
    · simpa only [lp.norm_zero] using hM
    · intro k
      simpa only [lp.coeFn_zero,Pi.zero_apply,add_zero] using ha k
    · intro k hkn
      simpa only [lp.coeFn_zero,Pi.zero_apply,add_zero] using hfactor k hkn

/-- The explicit power-sum assertion in Lemma 20.3 uses the actual
coefficient, independent of r. Summing over all indices is equivalent to
omitting the deleted index, where this coefficient is zero. -/
theorem SourceAbelianMomentAtlas.exists_lemma20_3_offDiagonal_power_sum
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧ ∀ φ ∈ U, ∃ ρ : ℝ, 0 < ρ ∧ ball φ ρ ⊆ U ∧
        ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ ball φ ρ, ∀ n : ℤ,
            Summable (fun k : ℤ => ‖sourceSecondMomentCubicCoefficient A n ψ k‖^r.toReal) ∧
            (∑' k : ℤ, ‖sourceSecondMomentCubicCoefficient A n ψ k‖^r.toReal) ≤ C ∧
            ∀ k : ℤ, k ≠ n → A.moment n k 2 ψ =
              (sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*
                sourceSecondMomentCubicCoefficient A n ψ k := by
  obtain ⟨U,hU,hUconn,hrealU,hUV,hlocal⟩ :=
    A.exists_almostReal_offDiagonal_secondMoment_coefficients hs hV hrealV
  refine ⟨U,hU,hUconn,hrealU,hUV,?_⟩
  intro φ hφ
  obtain ⟨ρ,hρ,hball,hrows⟩ := hlocal φ hφ
  refine ⟨ρ,hρ,hball,?_⟩
  intro r hr hr1 hpr
  have hrreal := ENNReal.toReal_pos (zero_lt_one.trans hr1).ne' hr
  obtain ⟨M,hM,hb⟩ := hrows r hr hr1 hpr
  refine ⟨M^r.toReal+1,by positivity,?_⟩
  intro ψ hψ n
  obtain ⟨a,ha,_,haM,hfactor⟩ := hb ψ hψ n
  have hsum : (∑' k : ℤ, ‖sourceSecondMomentCubicCoefficient A n ψ k‖^r.toReal) = ‖a‖^r.toReal := by
    rw [lp.norm_rpow_eq_tsum hrreal]
    exact tsum_congr (fun k => by rw [ha k])
  refine ⟨((lp.memℓp a).summable hrreal).congr (fun k => by rw [ha k]),?_,?_⟩
  · rw [hsum]
    exact (Real.rpow_le_rpow (lp.norm_nonneg' _) haM hrreal.le).trans (by linarith)
  · intro k hkn
    simpa only [ha k] using hfactor k hkn

end NLS.ZakharovShabat
