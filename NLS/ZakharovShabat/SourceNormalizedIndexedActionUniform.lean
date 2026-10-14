import NLS.ZakharovShabat.SourceActionChiUniform
import NLS.ZakharovShabat.SourceNormalizedIndexedActionEstimate

/-!
# Uniform normalized-action estimates on the entire original domain

The cosine estimate and the actual gap-supremum bounds give refined
sequence bounds at every complex source. The neighborhood is independent
of the index and the refined exponent, and includes collapsed gaps.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Uniform gap and critical-coefficient bounds transfer the literal supremum
estimate to the actual filled normalized indexed actions. -/
theorem SourceEquation2_19Data.normalized_refined_of_bounds
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceEquation2_19Data hp hp1 W) (hVW : V ⊆ W)
    (G B : ℝ) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hg : ∀ ψ ∈ V, ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ ≤ G)
    (hb : ∀ ψ ∈ V, ‖sourceCriticalGapQuotient hp hp1 ψ‖ ≤ B)
    (hs : ∀ (r : ℝ≥0∞), r ≠ ⊤ → 1 < r → p/2 ≤ r →
      ∃ L : ℝ, 0 ≤ L ∧ ∀ ψ ∈ V, ∃ a : Coeff r,
        (∀ n : ℤ, a n = (sourceActionChiGapSup hp hp1 ψ n : ℂ)) ∧ ‖a‖ ≤ L) :
    ∀ (r : ℝ≥0∞), r ≠ ⊤ → 1 < r → p/2 ≤ r →
      ∃ L : ℝ, 0 ≤ L ∧ ∀ ψ ∈ V, ∃ a : Coeff r,
        (∀ n : ℤ, a n = 4*sourceNormalizedIndexedAction hp hp1 n ψ-1) ∧ ‖a‖ ≤ L := by
  intro r hr hr1 hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  have hhalf : 0 < ENNReal.ofReal (p.toReal/2) := by
    rw [Coeff.halfExponent_eq_div hp]
    exact ENNReal.div_pos (zero_lt_one.trans hp1).ne' (by norm_num)
  have hhalfr : ENNReal.ofReal (p.toReal/2) ≤ r := by rwa [Coeff.halfExponent_eq_div hp]
  obtain ⟨Q,hQ,hcoeff⟩ := hs r hr hr1 hpr
  let L : ℝ := 2*(2*G*B+1)^2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hC : 0 ≤ 8*B^2 := by positivity
  refine ⟨L*Q+8*B^2*G^2,by positivity,?_⟩
  intro ψ hψ
  obtain ⟨e,he,hen⟩ := hcoeff ψ hψ
  let a : Coeff r := (L:ℂ) • e
  let b : Coeff (ENNReal.ofReal (p.toReal/2)) := ((8*B^2:ℝ):ℂ) • sourcePeriodicSquaredGapCoeff hp hp1 ψ
  have ha (n : ℤ) : ‖a n‖ = L*sourceActionChiGapSup hp hp1 ψ n := by
    simp only [a,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,he,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg hL,Real.norm_of_nonneg (H.previous.chiGapSup_nonneg ψ (hVW hψ) n)]
  have hb' (n : ℤ) : ‖b n‖ = 8*B^2*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 := by
    simp only [b,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,sourcePeriodicSquaredGapCoeff_apply,
      norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hC]
  have hpoint (n : ℤ) : ‖4*sourceNormalizedIndexedAction hp hp1 n ψ-1‖ ≤ ‖a n‖+‖b n‖ := by
    have hgn : ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ ≤ G :=
      (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' _ n).trans (hg ψ hψ)
    have hbn : ‖sourceCriticalGapQuotient hp hp1 ψ n‖ ≤ B :=
      (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' _ n).trans (hb ψ hψ)
    have hs0 := H.previous.chiGapSup_nonneg ψ (hVW hψ) n
    rw [ha,hb']
    calc
      _ ≤ 8*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2*‖sourceCriticalGapQuotient hp hp1 ψ n‖^2+
          2*(2*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖*‖sourceCriticalGapQuotient hp hp1 ψ n‖+1)^2*
            sourceActionChiGapSup hp hp1 ψ n := H.norm_normalized_sub_one_le ψ (hVW hψ) n
      _ ≤ 8*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2*B^2+
          2*(2*G*B+1)^2*sourceActionChiGapSup hp hp1 ψ n := by gcongr
      _ = _ := by dsimp [L]; ring
  have han : ‖a‖ ≤ L*Q := by
    dsimp only [a]
    rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hL]
    exact mul_le_mul_of_nonneg_left hen hL
  have hbn : ‖b‖ ≤ 8*B^2*G^2 := by
    dsimp only [b]
    rw [lp.norm_const_smul hhalf.ne',Complex.norm_real,Real.norm_of_nonneg hC]
    exact mul_le_mul_of_nonneg_left ((norm_sourcePeriodicSquaredGapCoeff_le_sq hp hp1 ψ).trans
      (pow_le_pow_left₀ (norm_nonneg _) (hg ψ hψ) 2)) hC
  obtain ⟨E,hE,hEn,_⟩ := Coeff.exists_tailCoeff_of_twoSequenceMajorants
    hhalf hr1 hr hhalfr (fun n => 4*sourceNormalizedIndexedAction hp hp1 n ψ-1) 0 a b
      (fun n _ => hpoint n)
  exact ⟨E,fun n => by simpa using hE n,hEn.trans (add_le_add han hbn)⟩

/-- One neighborhood gives both literal refined estimates near every complex source of W. -/
theorem SourceEquation2_19Data.uniform_refined
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_19Data hp hp1 W) (hW : IsOpen W) (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
      (∀ (r : ℝ≥0∞), r ≠ ⊤ → 1 < r → p/2 ≤ r →
        ∃ L : ℝ, 0 ≤ L ∧ ∀ ψ ∈ V, ∃ a : Coeff r,
          (∀ n : ℤ, a n = (sourceActionChiGapSup hp hp1 ψ n : ℂ)) ∧ ‖a‖ ≤ L) ∧
      (∀ (r : ℝ≥0∞), r ≠ ⊤ → 1 < r → p/2 ≤ r →
        ∃ L : ℝ, 0 ≤ L ∧ ∀ ψ ∈ V, ∃ a : Coeff r,
          (∀ n : ℤ, a n = 4*sourceNormalizedIndexedAction hp hp1 n ψ-1) ∧ ‖a‖ ≤ L) := by
  obtain ⟨S,hS,hφS,hSW,hs⟩ := H.previous.chiGapSup_refined hW φ hφ
  obtain ⟨Vb,hVb,_,hφb,_,B,hB,hbound⟩ := H.previous.criticalOffsets.locally_uniform φ hφ
  obtain ⟨_,_,Vg,hVg,hφg,G,hG,hgap⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  let V := S ∩ (Vb ∩ Vg)
  have hVW : V ⊆ W := fun _ hψ => hSW hψ.1
  have hs' : ∀ (r : ℝ≥0∞), r ≠ ⊤ → 1 < r → p/2 ≤ r →
      ∃ L : ℝ, 0 ≤ L ∧ ∀ ψ ∈ V, ∃ a : Coeff r,
        (∀ n : ℤ, a n = (sourceActionChiGapSup hp hp1 ψ n : ℂ)) ∧ ‖a‖ ≤ L := by
    intro r hr hr1 hpr
    obtain ⟨L,hL,hcoeff⟩ := hs r hr hr1 hpr
    exact ⟨L,hL,fun ψ hψ => hcoeff ψ hψ.1⟩
  exact ⟨V,hS.inter (hVb.inter hVg),⟨hφS,hφb,hφg⟩,hVW,hs',
    H.normalized_refined_of_bounds hVW G B hG hB.le
      (fun ψ hψ => (hgap ψ hψ.2.2).1) (fun ψ hψ => hbound ψ hψ.2.1) hs'⟩

end NLS.ZakharovShabat
