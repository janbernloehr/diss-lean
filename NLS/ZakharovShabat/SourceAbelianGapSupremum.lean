import NLS.ZakharovShabat.SourceFullAbelianAllGapMajorants
import NLS.SequenceSpaces.RefinedOnePlusDecomposition

/-!
# The literal mixed supremum remainder of Lemma 19.4

The supremum ranges over both sides and the entire closed gap. It is bounded
before it is used. One ℓ^(p/2)+ℓ^(1+) decomposition works before every auxiliary
exponent is selected, including p/2 below one and collapsed gaps.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- All actual error magnitudes on the two sides of the selected closed gap. -/
def gapErrorRange (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (ψ : CoeffPair p) (n : ℤ) : Set ℝ :=
  range (fun u : Icc (0 : ℝ) Real.pi × Bool =>
    ‖C.gapBoundary n ψ u.1.val u.2 - Complex.I*sourceStandardRootGapBoundary hp hp1 ψ n u.1.val u.2‖)

/-- The literal supremum in Lemma 19.4, including both endpoints and both sides. -/
def gapErrorSup (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (ψ : CoeffPair p) (n : ℤ) : ℝ :=
  sSup (C.gapErrorRange ψ n)

theorem gapErrorRange_nonempty (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (ψ : CoeffPair p) (n : ℤ) :
    (C.gapErrorRange ψ n).Nonempty :=
  ⟨_,⟨(⟨0,⟨le_rfl,Real.pi_pos.le⟩⟩,false),rfl⟩⟩

theorem gapErrorSup_nonneg (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (ψ : CoeffPair p) (n : ℤ) :
    0 ≤ C.gapErrorSup ψ n := Real.sSup_nonneg (by rintro _ ⟨u,rfl⟩; exact norm_nonneg _)

theorem gapErrorSup_le (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (ψ : CoeffPair p) (n : ℤ)
    (B : ℝ) (hB : ∀ θ ∈ Icc (0 : ℝ) Real.pi, ∀ upper : Bool,
      ‖C.gapBoundary n ψ θ upper - Complex.I*sourceStandardRootGapBoundary hp hp1 ψ n θ upper‖ ≤ B) :
    C.gapErrorSup ψ n ≤ B :=
  csSup_le (C.gapErrorRange_nonempty ψ n) (by rintro _ ⟨u,rfl⟩; exact hB u.1.val u.1.property u.2)

theorem gapError_le_sup (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (ψ : CoeffPair p) (n : ℤ)
    (hb : BddAbove (C.gapErrorRange ψ n)) (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) Real.pi) (upper : Bool) :
    ‖C.gapBoundary n ψ θ upper - Complex.I*sourceStandardRootGapBoundary hp hp1 ψ n θ upper‖ ≤
      C.gapErrorSup ψ n := le_csSup hb ⟨(⟨θ,hθ⟩,upper),rfl⟩

theorem gapErrorSup_eq_zero_of_collapsed (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (ψ : CoeffPair p) (n : ℤ) (hn : sourcePeriodicGapDisplacement hp hp1 ψ n = 0) :
    C.gapErrorSup ψ n = 0 := by
  apply le_antisymm _ (C.gapErrorSup_nonneg ψ n)
  apply C.gapErrorSup_le ψ n 0
  intro θ _ upper
  rw [sourcePeriodicGapDisplacement_apply] at hn
  have hg : sourceStandardRootHalfGap hp hp1 ψ n = 0 := by
    unfold sourceStandardRootHalfGap
    rw [hn]
    simp
  rw [C.gapBoundary_eq_zero_of_collapsed n ψ hn θ upper]
  simp only [sourceStandardRootGapBoundary,hg,zero_mul,mul_zero,sub_zero,norm_zero,le_refl]

end SourceFullAbelianUniformCauchyFamily

/-- A single decomposition of the actual supremum, with simultaneous local bounds. -/
structure SourceAbelianMixedGapData {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (V : Set (CoeffPair p)) : Prop where
  bounded : ∀ ψ ∈ V, ∀ n, BddAbove (C.gapErrorRange ψ n)
  mixed : ∃ g : CoeffPair p → Coeff (ENNReal.ofReal (p.toReal/2)), ∃ h : CoeffPair p → CoeffOnePlus,
    (∀ ψ ∈ V, ∀ n, (C.gapErrorSup ψ n : ℂ) =
      (‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ : ℂ)*(g ψ n+(h ψ).1 n)) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ V, ‖g ψ‖ ≤ M) ∧
    ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ V, ‖CoeffOnePlus.toCoeff q hq1 hq (h ψ)‖ ≤ M

namespace SourceAbelianMixedGapData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
  {C : SourceFullAbelianUniformCauchyFamily hp hp1 W}

/-- The literal complex gap displacement can replace its magnitude, with the
same exponents and locally uniform bounds, even when p/2 is below one. -/
theorem mixed_displacement (D : SourceAbelianMixedGapData C V) :
    ∃ g : CoeffPair p → Coeff (ENNReal.ofReal (p.toReal/2)), ∃ h : CoeffPair p → CoeffOnePlus,
      (∀ ψ ∈ V, ∀ n, (C.gapErrorSup ψ n : ℂ) =
        sourcePeriodicGapDisplacement hp hp1 ψ n*(g ψ n+(h ψ).1 n)) ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ V, ‖g ψ‖ ≤ M) ∧
      ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
        ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ V, ‖CoeffOnePlus.toCoeff q hq1 hq (h ψ)‖ ≤ M := by
  obtain ⟨g,h,he,⟨M,hM,hg⟩,hh⟩ := D.mixed
  let u : CoeffPair p → ℤ → ℂ := fun ψ n =>
    (‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ : ℂ)/sourcePeriodicGapDisplacement hp hp1 ψ n
  have hu (ψ : CoeffPair p) (n : ℤ) : ‖u ψ n‖ ≤ 1 := by
    simp only [u,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    exact div_self_le_one _
  have hmul (ψ : CoeffPair p) (n : ℤ) (a : ℂ) : ‖u ψ n*a‖ ≤ ‖a‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hu ψ n)
  let g' : CoeffPair p → Coeff (ENNReal.ofReal (p.toReal/2)) := fun ψ =>
    ⟨fun n => u ψ n*g ψ n,(lp.memℓp (g ψ)).mono' (fun n => hmul ψ n _)⟩
  let h' : CoeffPair p → CoeffOnePlus := fun ψ =>
    ⟨fun n => u ψ n*(h ψ).1 n,fun q hq1 hq =>
      ((h ψ).property q hq1 hq).mono' (fun n => hmul ψ n _)⟩
  have ht : ENNReal.ofReal (p.toReal/2) ≠ 0 := (ENNReal.ofReal_pos.mpr
    (div_pos (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp) (by norm_num))).ne'
  refine ⟨g',h',?_,⟨M,hM,fun ψ hψ => (lp.norm_mono ht (fun n => hmul ψ n _)).trans (hg ψ hψ)⟩,?_⟩
  · intro ψ hψ n
    change (C.gapErrorSup ψ n : ℂ) =
      sourcePeriodicGapDisplacement hp hp1 ψ n*(u ψ n*g ψ n+u ψ n*(h ψ).1 n)
    by_cases hn : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
    · simp only [hn,C.gapErrorSup_eq_zero_of_collapsed ψ n hn,Complex.ofReal_zero,zero_mul]
    · rw [he ψ hψ n,← mul_add,← mul_assoc]
      congr 1
      dsimp only [u]
      field_simp
  · intro q hq1 hq
    obtain ⟨N,hN,hhN⟩ := hh q hq1 hq
    refine ⟨N,hN,fun ψ hψ => ?_⟩
    exact (lp.norm_mono (ne_of_gt (zero_lt_one.trans hq1)) (fun n => hmul ψ n _)).trans (hhN ψ hψ)

/-- Restricting the source neighborhood preserves the same chosen decomposition. -/
theorem mono (D : SourceAbelianMixedGapData C V) {U : Set (CoeffPair p)} (hUV : U ⊆ V) :
    SourceAbelianMixedGapData C U := by
  obtain ⟨g,h,he,⟨M,hM,hg⟩,hh⟩ := D.mixed
  refine ⟨fun ψ hψ => D.bounded ψ (hUV hψ),g,h,fun ψ hψ => he ψ (hUV hψ),
    ⟨M,hM,fun ψ hψ => hg ψ (hUV hψ)⟩,?_⟩
  intro q hq1 hq
  obtain ⟨N,hN,hn⟩ := hh q hq1 hq
  exact ⟨N,hN,fun ψ hψ => hn ψ (hUV hψ)⟩

/-- Lemma 19.1(iii), strengthened to every gap on the same source neighborhood. -/
theorem uniform_boundary_bound (D : SourceAbelianMixedGapData C V) :
    ∃ B : ℝ, 0 < B ∧ ∀ ψ ∈ V, ∀ n : ℤ, ∀ θ ∈ Icc (0 : ℝ) Real.pi, ∀ upper : Bool,
      ‖C.gapBoundary n ψ θ upper‖ ≤ B*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
  obtain ⟨g,h,he,⟨M,hM,hg⟩,hh⟩ := D.mixed
  obtain ⟨N,hN,hhN⟩ := hh 2 (by norm_num) (by simp)
  have ht : ENNReal.ofReal (p.toReal/2) ≠ 0 := (ENNReal.ofReal_pos.mpr
    (div_pos (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp) (by norm_num))).ne'
  refine ⟨M+N+1,by linarith,?_⟩
  intro ψ hψ n θ hθ upper
  have hgn : ‖g ψ n‖ ≤ M := (lp.norm_apply_le_norm ht (g ψ) n).trans (hg ψ hψ)
  have hhn : ‖(h ψ).1 n‖ ≤ N :=
    (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (CoeffOnePlus.toCoeff 2 (by norm_num) (by simp) (h ψ)) n).trans (hhN ψ hψ)
  have hs := congrArg norm (he ψ hψ n)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (C.gapErrorSup_nonneg ψ n),norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] at hs
  have herr : ‖C.gapBoundary n ψ θ upper-Complex.I*sourceStandardRootGapBoundary hp hp1 ψ n θ upper‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖*(M+N) := by
    apply (C.gapError_le_sup ψ n (D.bounded ψ hψ n) θ hθ upper).trans
    rw [hs]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hgn hhn)) (norm_nonneg _)
  have hsin : ‖(Real.sin θ : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one θ
  have hhalf : ‖sourceStandardRootHalfGap hp hp1 ψ n‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
    simp only [sourceStandardRootHalfGap,sourcePeriodicGapDisplacement_apply,norm_div,Complex.norm_ofNat]
    linarith [norm_nonneg (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)]
  have hroot : ‖Complex.I*sourceStandardRootGapBoundary hp hp1 ψ n θ upper‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
    have h := (mul_le_of_le_one_right (norm_nonneg (sourceStandardRootHalfGap hp hp1 ψ n)) hsin).trans hhalf
    cases upper <;> simpa only [sourceStandardRootGapBoundary,Bool.false_eq_true,↓reduceIte,
      norm_mul,norm_neg,Complex.norm_I,one_mul] using h
  have hb := norm_add_le (C.gapBoundary n ψ θ upper-Complex.I*sourceStandardRootGapBoundary hp hp1 ψ n θ upper)
    (Complex.I*sourceStandardRootGapBoundary hp hp1 ψ n θ upper)
  rw [sub_add_cancel] at hb
  nlinarith

/-- The literal supremum in Lemma 19.1(iii) is bounded before taking it. -/
theorem uniform_boundary_sup (D : SourceAbelianMixedGapData C V) :
    ∃ B : ℝ, 0 < B ∧ ∀ ψ ∈ V, ∀ n : ℤ,
      let S := range (fun u : Icc (0 : ℝ) Real.pi × Bool => ‖C.gapBoundary n ψ u.1.val u.2‖)
      BddAbove S ∧ sSup S ≤ B*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
  obtain ⟨B,hB,hbound⟩ := D.uniform_boundary_bound
  refine ⟨B,hB,?_⟩
  intro ψ hψ n
  dsimp only
  have hb : ∀ x ∈ range (fun u : Icc (0 : ℝ) Real.pi × Bool => ‖C.gapBoundary n ψ u.1.val u.2‖),
      x ≤ B*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
    rintro _ ⟨u,rfl⟩
    exact hbound ψ hψ n u.1.val u.1.property u.2
  exact ⟨⟨_,hb⟩,csSup_le ⟨_,⟨(⟨0,⟨le_rfl,Real.pi_pos.le⟩⟩,false),rfl⟩⟩ hb⟩

end SourceAbelianMixedGapData

/-- Turn all auxiliary majorants into one decomposition of the literal supremum. -/
theorem sourceAbelianMixedGapData_of_majorants
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (V : Set (CoeffPair p))
    (hb : ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ V,
      ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
        ‖Bq‖ ≤ M ∧ ‖Bg‖ ≤ M ∧ ∀ n : ℤ, ∀ θ ∈ Icc (0:ℝ) Real.pi, ∀ upper : Bool,
          ‖C.gapBoundary n ψ θ upper-Complex.I*sourceStandardRootGapBoundary hp hp1 ψ n θ upper‖ ≤
            ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖*(‖Bq n‖+‖Bg n‖)) :
    SourceAbelianMixedGapData C V := by
  let t := ENNReal.ofReal (p.toReal/2)
  have ht : 0 < t := ENNReal.ofReal_pos.mpr (by
    exact div_pos (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp) (by norm_num))
  let f : CoeffPair p → ℤ → ℂ := fun ψ n =>
    (C.gapErrorSup ψ n / ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ : ℝ)
  have hbounded (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) : BddAbove (C.gapErrorRange ψ n) := by
    obtain ⟨M,_,hbM⟩ := hb 2 (by simp) (by norm_num)
    obtain ⟨Bq,Bg,_,_,hb'⟩ := hbM ψ hψ
    exact ⟨_,by rintro _ ⟨u,rfl⟩; exact hb' n u.1.val u.1.property u.2⟩
  have hnorm : ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → t ≤ r →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ V, ∃ b : Coeff r, (∀ n, b n = f ψ n) ∧ ‖b‖ ≤ M := by
    intro r hr hr1 htr
    let : Fact (1 ≤ r) := ⟨hr1.le⟩
    obtain ⟨M,hM,hbM⟩ := hb r hr hr1
    refine ⟨2*M,by positivity,?_⟩
    intro ψ hψ
    obtain ⟨Bq,Bg,hBq,hBg,hpoint⟩ := hbM ψ hψ
    let G : Coeff r := ⟨fun n => Bg n,(lp.memℓp Bg).of_exponent_ge htr⟩
    let c : Coeff r := Coeff.magnitude Bq+Coeff.magnitude G
    have hcn (n : ℤ) : ‖c n‖ = ‖Bq n‖+‖Bg n‖ := by
      change ‖(‖Bq n‖ : ℂ)+(‖Bg n‖ : ℂ)‖ = _
      rw [← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hfc (n : ℤ) : ‖f ψ n‖ ≤ ‖c n‖ := by
      rw [hcn]
      have hs := C.gapErrorSup_le ψ n _ (hpoint n)
      have hf0 : 0 ≤ C.gapErrorSup ψ n / ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ :=
        div_nonneg (C.gapErrorSup_nonneg ψ n) (norm_nonneg _)
      change ‖((C.gapErrorSup ψ n / ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hf0]
      by_cases hn : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
      · simp only [hn,norm_zero,div_zero]
        positivity
      · apply (div_le_iff₀ (norm_pos_iff.mpr hn)).mpr
        simpa only [mul_comm] using hs
    let b : Coeff r := ⟨f ψ,(lp.memℓp c).mono' hfc⟩
    refine ⟨b,fun _ => rfl,?_⟩
    have hG : ‖G‖ ≤ ‖Bg‖ := Coeff.norm_quasiExponentInclusion_le ht (zero_lt_one.trans hr1) hr htr Bg
    calc
      ‖b‖ ≤ ‖c‖ := lp.norm_mono (zero_lt_one.trans hr1).ne' hfc
      _ ≤ ‖Bq‖+‖G‖ := by simpa only [Coeff.norm_magnitude] using norm_add_le (Coeff.magnitude Bq) (Coeff.magnitude G)
      _ ≤ 2*M := by linarith
  obtain ⟨g,h,he,hg,hh⟩ := Coeff.exists_onePlus_decomposition_of_refined V f ENNReal.ofReal_ne_top hnorm
  refine ⟨hbounded,g,h,?_,hg,hh⟩
  intro ψ hψ n
  rw [← he ψ hψ n]
  dsimp only [f]
  by_cases hn : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
  · simp [C.gapErrorSup_eq_zero_of_collapsed ψ n hn]
  · rw [← Complex.ofReal_mul,mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hn)]

/-- One local neighborhood carries the exact mixed supremum for every real base source. -/
theorem exists_sourceAbelian_mixedGapData (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : realTypeSourceSubmodule p,
        ∃ C : SourceFullAbelianUniformCauchyFamily hp hp1 W,
        ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧
          V ⊆ ball C.discs.source.val C.discs.sourceRadius ∧ SourceAbelianMixedGapData C V := by
  obtain ⟨W,hW,hr,hlocal⟩ := exists_sourceFullAbelian_all_gap_majorants hp hp1
  refine ⟨W,hW,hr,?_⟩
  intro φ
  obtain ⟨C,V,hV,hφ,hVC,hb⟩ := hlocal φ
  exact ⟨C,V,hV,hφ,hVC,sourceAbelianMixedGapData_of_majorants C V hb⟩

end NLS.ZakharovShabat
