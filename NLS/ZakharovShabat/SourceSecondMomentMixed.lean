import NLS.ZakharovShabat.SourceAbelianMomentLemma20_3
import NLS.SequenceSpaces.RefinedOnePlusDecomposition

/-!
# Fixed mixed remainder sequences for the original second moments

The diagonal sequence and every off-diagonal row have one genuine
ℓ^(p/2)+ℓ^(1+) decomposition. The neighborhood and both components are
chosen before the auxiliary exponent. Row bounds are uniform in the
deleted index, and the actual coefficient power sums are retained.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

structure SourceSecondMomentMixedData (A : SourceAbelianMomentAtlas hp hp1 W s)
    (T : Set (CoeffPair p)) : Prop where
  diagonal : ∃ g : CoeffPair p → Coeff (ENNReal.ofReal (p.toReal/2)), ∃ h : CoeffPair p → CoeffOnePlus,
    (∀ ψ ∈ T, ∀ k, A.moment k k 2 ψ = (sourcePeriodicGapDisplacement hp hp1 ψ k)^2/4*
      ((Real.pi : ℂ)+g ψ k+(h ψ).1 k)) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ‖g ψ‖ ≤ M) ∧
    ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ‖CoeffOnePlus.toCoeff q hq1 hq (h ψ)‖ ≤ M
  rows : ∃ g : CoeffPair p → ℤ → Coeff (ENNReal.ofReal (p.toReal/2)),
    ∃ h : CoeffPair p → ℤ → CoeffOnePlus,
    (∀ ψ ∈ T, ∀ n k : ℤ, k ≠ n → A.moment n k 2 ψ =
      (sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*(g ψ n k+(h ψ n).1 k)) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ∀ n, ‖g ψ n‖ ≤ M) ∧
    ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ∀ n, ‖CoeffOnePlus.toCoeff q hq1 hq (h ψ n)‖ ≤ M
  refined : ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
    ∃ M : ℝ, 0 < M ∧ ∀ ψ ∈ T, ∃ d : Coeff r,
      (∀ k, d k = sourceSecondMomentDiagonalCoefficient A ψ k) ∧ ‖d‖ ≤ M ∧
      ∀ n : ℤ, ∃ a : Coeff r,
        (∀ k, a k = sourceSecondMomentCubicCoefficient A n ψ k) ∧ a n = 0 ∧ ‖a‖ ≤ M

/-- Refined bounds give a fixed mixed decomposition without replacing the
actual moments, even at collapsed gaps or exponents p/2 below one. -/
theorem sourceSecondMomentMixedData_of_refined (A : SourceAbelianMomentAtlas hp hp1 W s)
    (T : Set (CoeffPair p))
    (hb : ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
      ∃ M : ℝ, 0 < M ∧ ∀ ψ ∈ T, ∃ d : Coeff r,
        (∀ k, d k = sourceSecondMomentDiagonalCoefficient A ψ k) ∧ ‖d‖ ≤ M ∧
        (∀ k, A.moment k k 2 ψ = (sourcePeriodicGapDisplacement hp hp1 ψ k)^2/4*((Real.pi:ℂ)+d k)) ∧
        ∀ n : ℤ, ∃ a : Coeff r,
          (∀ k, a k = sourceSecondMomentCubicCoefficient A n ψ k) ∧ a n = 0 ∧ ‖a‖ ≤ M ∧
          ∀ k, k ≠ n → A.moment n k 2 ψ = (sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*a k) :
    SourceSecondMomentMixedData A T := by
  obtain ⟨g,h,he,hg,hh⟩ := Coeff.exists_onePlus_decomposition_of_refined T
    (sourceSecondMomentDiagonalCoefficient A) ENNReal.ofReal_ne_top (by
      intro r hr hr1 hpr
      obtain ⟨M,hM,hb⟩ := hb r hr hr1 hpr
      exact ⟨M,hM.le,fun ψ hψ => by obtain ⟨d,he,hn,_⟩ := hb ψ hψ; exact ⟨d,he,hn⟩⟩)
  obtain ⟨g',h',he',hg',hh'⟩ := Coeff.exists_onePlus_decomposition_of_refined
    (T ×ˢ (univ : Set ℤ)) (fun u : CoeffPair p × ℤ => sourceSecondMomentCubicCoefficient A u.2 u.1)
    ENNReal.ofReal_ne_top (by
      intro r hr hr1 hpr
      obtain ⟨M,hM,hb⟩ := hb r hr hr1 hpr
      refine ⟨M,hM.le,?_⟩
      intro u hu
      obtain ⟨_,_,_,_,hrows⟩ := hb u.1 hu.1
      obtain ⟨a,he,_,hn,_⟩ := hrows u.2
      exact ⟨a,he,hn⟩)
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    conv_rhs => rw [← ENNReal.ofReal_toReal hp]
    exact ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := p)])
  obtain ⟨_,_,hfactor⟩ := hb p hp hp1 hhalf
  refine ⟨⟨g,h,?_,hg,hh⟩,⟨fun ψ n => g' (ψ,n),fun ψ n => h' (ψ,n),?_,?_,?_⟩,?_⟩
  · intro ψ hψ k
    obtain ⟨d,hd,_,hdF,_⟩ := hfactor ψ hψ
    rw [hdF k,hd k,he ψ hψ k,← add_assoc]
  · intro ψ hψ n k hkn
    obtain ⟨_,_,_,_,hrows⟩ := hfactor ψ hψ
    obtain ⟨a,ha,_,_,haF⟩ := hrows n
    rw [haF k hkn,ha k,he' (ψ,n) ⟨hψ,mem_univ n⟩ k]
  · obtain ⟨M,hM,hg'⟩ := hg'
    exact ⟨M,hM,fun ψ hψ n => hg' (ψ,n) ⟨hψ,mem_univ n⟩⟩
  · intro q hq1 hq
    obtain ⟨M,hM,hh'⟩ := hh' q hq1 hq
    exact ⟨M,hM,fun ψ hψ n => hh' (ψ,n) ⟨hψ,mem_univ n⟩⟩
  · intro r hr hr1 hpr
    obtain ⟨M,hM,hb⟩ := hb r hr hr1 hpr
    refine ⟨M,hM,?_⟩
    intro ψ hψ
    obtain ⟨d,he,hn,_,hrows⟩ := hb ψ hψ
    exact ⟨d,he,hn,fun n => by obtain ⟨a,he,hz,hn,_⟩ := hrows n; exact ⟨a,he,hz,hn⟩⟩

/-- The printed literal r-power row estimate, with its bound before the source
and deleted index. The diagonal coordinate is zero and may be included. -/
theorem SourceSecondMomentMixedData.row_power_sum
    {A : SourceAbelianMomentAtlas hp hp1 W s} {T : Set (CoeffPair p)}
    (D : SourceSecondMomentMixedData A T) (r : ℝ≥0∞) (hr : r ≠ ⊤) (hr1 : 1 < r)
    (hpr : ENNReal.ofReal (p.toReal/2) ≤ r) :
    ∃ B : ℝ, 0 < B ∧ ∀ ψ ∈ T, ∀ n : ℤ,
      Summable (fun k => ‖sourceSecondMomentCubicCoefficient A n ψ k‖^r.toReal) ∧
      (∑' k : ℤ, ‖sourceSecondMomentCubicCoefficient A n ψ k‖^r.toReal) ≤ B := by
  obtain ⟨M,hM,hb⟩ := D.refined r hr hr1 hpr
  have hrpos : 0 < r.toReal := ENNReal.toReal_pos (zero_lt_one.trans hr1).ne' hr
  refine ⟨M^r.toReal,Real.rpow_pos_of_pos hM _,?_⟩
  intro ψ hψ n
  obtain ⟨_,_,_,hrows⟩ := hb ψ hψ
  obtain ⟨a,ha,_,hn⟩ := hrows n
  have he : sourceSecondMomentCubicCoefficient A n ψ = fun k => a k := (funext ha).symm
  rw [he]
  refine ⟨(lp.memℓp a).summable hrpos,?_⟩
  rw [← lp.norm_rpow_eq_tsum hrpos a]
  exact Real.rpow_le_rpow (lp.norm_nonneg' a) hn hrpos.le

end NLS.ZakharovShabat
