import NLS.ZakharovShabat.SourceFullAbelianSquareGapBound
import NLS.ZakharovShabat.SourceFullAbelianAllGapMajorants

/-! # Locally uniform mixed sequence bounds for the filled square

The primitive estimate of Lemma 19.4 implies the square expansion used
in Lemma 20.3. Uniform coefficient bounds absorb the quadratic error
without changing either sequence exponent, even when `p/2 < 1`.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One neighborhood at each real source bounds the square error on
all complex gaps. The neighborhood is chosen before the auxiliary exponent. -/
theorem exists_sourceFullAbelian_local_square_gap_majorants (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : realTypeSourceSubmodule p,
        ∃ C : SourceFullAbelianUniformCauchyFamily hp hp1 W,
        ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧
          V ⊆ ball C.discs.source.val C.discs.sourceRadius ∧
          ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ V,
            ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
              ‖Bq‖ ≤ M ∧ ‖Bg‖ ≤ M ∧ ∀ j : ℤ, ∀ z ∈ sourcePeriodicSegment hp hp1 ψ j,
                ‖sourceFullAbelianSquare hp hp1 W j (z,ψ) + sourceAngularSelectedPolynomial hp hp1 ψ j z‖ ≤
                  ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖^2*(‖Bq j‖+‖Bg j‖) := by
  obtain ⟨W,hW,hreal,hlocal⟩ := exists_sourceFullAbelian_all_gap_majorants hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro φ
  obtain ⟨C,V,hV,hφ,hVC,hmajor⟩ := hlocal φ
  refine ⟨C,V,hV,hφ,hVC,?_⟩
  intro q hq hq1
  obtain ⟨M,hM,hb⟩ := hmajor q hq hq1
  let S : ℝ := 2*M+1
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hg0 : ENNReal.ofReal (p.toReal/2) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hq0 : q ≠ 0 := (zero_lt_one.trans hq1).ne'
  refine ⟨S*M,mul_nonneg hS hM,?_⟩
  intro ψ hψ
  obtain ⟨Bq,Bg,hBq,hBg,hpoint⟩ := hb ψ hψ
  let Aq : Coeff q := (S:ℂ) • Bq
  let Ag : Coeff (ENNReal.ofReal (p.toReal/2)) := (S:ℂ) • Bg
  have hAq : ‖Aq‖ ≤ S*M := by
    rw [show Aq = (S:ℂ) • Bq from rfl,lp.norm_const_smul hq0]
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hS] using
      mul_le_mul_of_nonneg_left hBq hS
  have hAg : ‖Ag‖ ≤ S*M := by
    rw [show Ag = (S:ℂ) • Bg from rfl,lp.norm_const_smul hg0]
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hS] using
      mul_le_mul_of_nonneg_left hBg hS
  refine ⟨Aq,Ag,hAq,hAg,?_⟩
  intro j z hz
  obtain ⟨θ,hθ,rfl⟩ := exists_sourcePeriodicSegment_cosine_parameter hp hp1 ψ j z hz
  let E : ℝ := ‖Bq j‖+‖Bg j‖
  have hE : 0 ≤ E := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hES : E+1 ≤ S := by
    have hqj := (lp.norm_apply_le_norm hq0 Bq j).trans hBq
    have hgj := (lp.norm_apply_le_norm hg0 Bg j).trans hBg
    dsimp [E,S]
    linarith
  have hbound := C.fullSquare_add_polynomial_norm_le ψ (hVC hψ) j θ true E hE (hpoint j θ hθ true)
  apply hbound.trans
  have he : ‖Aq j‖+‖Ag j‖ = E*S := by
    simp only [Aq,Ag,lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hS,E]
    ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hES
    (mul_nonneg (sq_nonneg ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖) hE)]

/-- The square expansion used in Lemma 20.3 on one connected almost-real
source neighborhood, uniformly over every point of every complex gap. -/
theorem exists_sourceFullAbelian_almostReal_square_gap_majorants (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ W ∧
      (∀ ψ ∈ U, ∀ j : ℤ, AnalyticOnNhd ℂ (fun z => sourceFullAbelianSquare hp hp1 W j (z,ψ))
        (sourceFullAbelianSquareDomain hp hp1 ψ j)) ∧
      ∀ φ ∈ U, ∃ r : ℝ, 0 < r ∧ ball φ r ⊆ U ∧
        ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ ball φ r,
          ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
            ‖Bq‖ ≤ M ∧ ‖Bg‖ ≤ M ∧ ∀ j : ℤ, ∀ z ∈ sourcePeriodicSegment hp hp1 ψ j,
              ‖sourceFullAbelianSquare hp hp1 W j (z,ψ) + sourceAngularSelectedPolynomial hp hp1 ψ j z‖ ≤
                ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖^2*(‖Bq j‖+‖Bg j‖) := by
  obtain ⟨W,_,_,hlocal⟩ := exists_sourceFullAbelian_local_square_gap_majorants hp hp1
  choose C V hV hφV hVC hmajor using hlocal
  let S : Set (CoeffPair p) := ⋃ φ : realTypeSourceSubmodule p, V φ
  have hS : IsOpen S := isOpen_iUnion hV
  have hrealS : realTypeSourceLocus p ⊆ S :=
    fun ψ hψ => mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hφV ⟨ψ,hψ⟩⟩
  let U := connectedComponentIn S (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealU : realTypeSourceLocus p ⊆ U :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS
  have hUS : U ⊆ S := connectedComponentIn_subset S 0
  have hU : IsOpen U := hS.connectedComponentIn
  refine ⟨W,U,hU,isConnected_connectedComponentIn_iff.mpr (hrealS hzero),hrealU,?_,?_,?_⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hψ)
    exact (C φ).discs.source_subset (hVC φ hφ)
  · intro ψ hψ j
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hψ)
    exact (C φ).fullSquare_analytic j ψ (hVC φ hφ)
  · intro χ hχ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hχ)
    obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp ((hU.inter (hV φ)).mem_nhds ⟨hχ,hφ⟩)
    refine ⟨r,hr,fun ψ hψ => (hsub hψ).1,?_⟩
    intro q hq hq1
    obtain ⟨M,hM,hb⟩ := hmajor φ q hq hq1
    exact ⟨M,hM,fun ψ hψ => hb ψ (hsub hψ).2⟩

end NLS.ZakharovShabat
