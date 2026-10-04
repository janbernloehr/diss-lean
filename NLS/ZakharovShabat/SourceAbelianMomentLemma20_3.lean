import NLS.ZakharovShabat.SourceAbelianMomentDiagonalNeighborhood
import NLS.ZakharovShabat.SourceAbelianMomentOffDiagonalNeighborhood

/-! # Lemma 20.3 for the actual normalized second moments

One connected almost-real neighborhood supports both the diagonal and
off-diagonal formulas. The actual coefficient sequences have locally
uniform refined norms; off-diagonal row bounds are uniform in the deleted
index. Every local source ball is chosen before the sequence exponent.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Both parts of Lemma 20.3 with actual, exponent-independent coefficients
and one positive bound on their refined norms. -/
theorem SourceAbelianMomentAtlas.exists_lemma20_3_refined
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧ ∀ φ ∈ U, ∃ ρ : ℝ, 0 < ρ ∧ ball φ ρ ⊆ U ∧
        ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          ∃ M : ℝ, 0 < M ∧ ∀ ψ ∈ ball φ ρ, ∃ d : Coeff r,
            (∀ k, d k = sourceSecondMomentDiagonalCoefficient A ψ k) ∧ ‖d‖ ≤ M ∧
            (∀ k : ℤ, A.moment k k 2 ψ = (sourcePeriodicGapDisplacement hp hp1 ψ k)^2/4*((Real.pi:ℂ)+d k)) ∧
            ∀ n : ℤ, ∃ a : Coeff r,
              (∀ k, a k = sourceSecondMomentCubicCoefficient A n ψ k) ∧ a n = 0 ∧ ‖a‖ ≤ M ∧
              ∀ k : ℤ, k ≠ n → A.moment n k 2 ψ = (sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*a k := by
  obtain ⟨Ud,hUd,_,hreald,hdV,hdiag⟩ := A.exists_almostReal_diagonal_secondMoment_coefficients hs hV hrealV
  obtain ⟨Uo,hUo,_,hrealo,_,hoff⟩ := A.exists_almostReal_offDiagonal_secondMoment_coefficients hs hV hrealV
  let S := Ud ∩ Uo
  let U := connectedComponentIn S (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealS : realTypeSourceLocus p ⊆ S := fun ψ hψ => ⟨hreald hψ,hrealo hψ⟩
  have hUS : U ⊆ S := connectedComponentIn_subset S 0
  have hU : IsOpen U := (hUd.inter hUo).connectedComponentIn
  refine ⟨U,hU,isConnected_connectedComponentIn_iff.mpr (hrealS hzero),
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS,
    fun ψ hψ => hdV (hUS hψ).1,?_⟩
  intro φ hφ
  obtain ⟨ρd,hρd,_,hd⟩ := hdiag φ (hUS hφ).1
  obtain ⟨ρo,hρo,_,ho⟩ := hoff φ (hUS hφ).2
  obtain ⟨ρu,hρu,hu⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hφ)
  let ρ := min ρd (min ρo ρu)
  have hρ : 0 < ρ := lt_min hρd (lt_min hρo hρu)
  have hbd : ball φ ρ ⊆ ball φ ρd := ball_subset_ball (min_le_left _ _)
  have hbo : ball φ ρ ⊆ ball φ ρo := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hbu : ball φ ρ ⊆ U := (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))).trans hu
  refine ⟨ρ,hρ,hbu,?_⟩
  intro r hr hr1 hpr
  obtain ⟨Md,hMd,hdiagRows⟩ := hd r hr hr1 hpr
  obtain ⟨Mo,hMo,hoffRows⟩ := ho r hr hr1 hpr
  refine ⟨1+Md+Mo,by positivity,?_⟩
  intro ψ hψ
  obtain ⟨d,hdval,hdnorm,hdfactor⟩ := hdiagRows ψ (hbd hψ)
  refine ⟨d,hdval,by linarith,hdfactor,?_⟩
  intro n
  obtain ⟨a,haval,han,hanorm,hafactor⟩ := hoffRows ψ (hbo hψ) n
  exact ⟨a,haval,han,by linarith,hafactor⟩

/-- Lemma 20.3 in its mixed-exponent form, with both exact formulas on
one connected almost-real neighborhood and at all selected indices.
The coefficient norms are locally uniform, and uniform in the deleted index. -/
theorem SourceAbelianMomentAtlas.exists_lemma20_3
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧ ∀ φ ∈ U, ∃ ρ : ℝ, 0 < ρ ∧ ball φ ρ ⊆ U ∧
        ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 < M ∧
          ∀ ψ ∈ ball φ ρ, ∃ d : Coeff q, ∃ e : Coeff (ENNReal.ofReal (p.toReal/2)),
            ‖d‖ ≤ M ∧ ‖e‖ ≤ M ∧
            (∀ k : ℤ, A.moment k k 2 ψ =
              (sourcePeriodicGapDisplacement hp hp1 ψ k)^2/4*((Real.pi:ℂ)+d k+e k)) ∧
            ∀ n : ℤ, ∃ a : Coeff q, ∃ b : Coeff (ENNReal.ofReal (p.toReal/2)),
              a n = 0 ∧ b n = 0 ∧ ‖a‖ ≤ M ∧ ‖b‖ ≤ M ∧ ∀ k : ℤ, k ≠ n →
                A.moment n k 2 ψ = (sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*(a k+b k) := by
  obtain ⟨U,hU,hUc,hreal,hUV,hlocal⟩ := A.exists_lemma20_3_refined hs hV hrealV
  refine ⟨U,hU,hUc,hreal,hUV,?_⟩
  intro φ hφ
  obtain ⟨ρ,hρ,hball,hrows⟩ := hlocal φ hφ
  refine ⟨ρ,hρ,hball,?_⟩
  intro q hq hq1
  by_cases hhalf : 1 < ENNReal.ofReal (p.toReal/2)
  · obtain ⟨M,hM,hb⟩ := hrows _ ENNReal.ofReal_ne_top hhalf le_rfl
    refine ⟨M,hM,?_⟩
    intro ψ hψ
    obtain ⟨e,_,he,hdiag,hoff⟩ := hb ψ hψ
    refine ⟨0,e,by simpa only [lp.norm_zero] using hM.le,he,?_,?_⟩
    · intro k
      simpa only [lp.coeFn_zero,Pi.zero_apply,add_zero] using hdiag k
    · intro n
      obtain ⟨b,_,hbn,hbM,hfactor⟩ := hoff n
      refine ⟨0,b,by simp,hbn,by simpa only [lp.norm_zero] using hM.le,hbM,?_⟩
      intro k hkn
      simpa only [lp.coeFn_zero,Pi.zero_apply,zero_add] using hfactor k hkn
  · obtain ⟨M,hM,hb⟩ := hrows q hq hq1 ((not_lt.mp hhalf).trans hq1.le)
    refine ⟨M,hM,?_⟩
    intro ψ hψ
    obtain ⟨d,_,hd,hdiag,hoff⟩ := hb ψ hψ
    refine ⟨d,0,hd,by simpa only [lp.norm_zero] using hM.le,?_,?_⟩
    · intro k
      simpa only [lp.coeFn_zero,Pi.zero_apply,add_zero] using hdiag k
    · intro n
      obtain ⟨a,_,han,haM,hfactor⟩ := hoff n
      refine ⟨a,0,han,by simp,haM,by simpa only [lp.norm_zero] using hM.le,?_⟩
      intro k hkn
      simpa only [lp.coeFn_zero,Pi.zero_apply,add_zero] using hfactor k hkn

end NLS.ZakharovShabat
