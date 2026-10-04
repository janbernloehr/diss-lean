import NLS.ZakharovShabat.SourceAbelianMomentErrorDomain
import NLS.ZakharovShabat.SourceFullAbelianSquareGapMajorants
import NLS.SequenceSpaces.QuasiExponentEmbedding

/-! # Refined square-error sequences for the actual moment atlas

The filled square is independent of its ambient source neighborhood.
Thus its mixed gap estimate transfers to any actual moment atlas, and
embedding the half-exponent summand gives a single refined error sequence.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- One source neighborhood supports the square-error sequence at every
finite exponent above one and at least p/2, in the atlas's own ambient domain. -/
theorem SourceAbelianMomentAtlas.exists_local_refined_square_gap_majorants
    (A : SourceAbelianMomentAtlas hp hp1 W s) (φ : realTypeSourceSubmodule p) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ A.domain ∧
      ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ∃ E : Coeff r, ‖E‖ ≤ M ∧
          ∀ k : ℤ, ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
            ‖sourceFullAbelianSquare hp hp1 W k (z,ψ)+sourceAngularSelectedPolynomial hp hp1 ψ k z‖ ≤
              ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2*‖E k‖ := by
  obtain ⟨W',_,_,hlocal⟩ := exists_sourceFullAbelian_local_square_gap_majorants hp hp1
  obtain ⟨C,T,hT,hφT,hTC,hmajor⟩ := hlocal φ
  refine ⟨T ∩ A.sourceBall φ,hT.inter isOpen_ball,
    ⟨hφT,mem_ball_self (A.localChart φ).radius_pos⟩,
    fun ψ hψ => mem_iUnion.mpr ⟨φ,hψ.2⟩,?_⟩
  intro r hr hr1 hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  have hhalf : 0 < ENNReal.ofReal (p.toReal/2) :=
    ENNReal.ofReal_pos.mpr (div_pos (ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp) (by norm_num))
  obtain ⟨M,hM,hrows⟩ := hmajor r hr hr1
  refine ⟨2*M,by positivity,?_⟩
  intro ψ hψ
  obtain ⟨Bq,Bg,hBq,hBg,hpoint⟩ := hrows ψ hψ.1
  let G : Coeff r := ⟨fun k => Bg k,(lp.memℓp Bg).of_exponent_ge hpr⟩
  have hG : ‖G‖ ≤ M := (Coeff.norm_quasiExponentInclusion_le hhalf (zero_lt_one.trans hr1) hr hpr Bg).trans hBg
  let E := Coeff.magnitude Bq+Coeff.magnitude G
  have hE (k : ℤ) : ‖E k‖ = ‖Bq k‖+‖Bg k‖ := by
    simp only [E,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
  refine ⟨E,?_,?_⟩
  · have h := norm_add_le (Coeff.magnitude Bq) (Coeff.magnitude G)
    simp only [Coeff.norm_magnitude] at h
    dsimp only [E]
    linarith
  · obtain ⟨D₀⟩ := (A.localChart φ).charts ψ hψ.2
    obtain ⟨D₁⟩ := C.charts ψ (hTC hψ.1)
    intro k z hz
    rw [sourceFullAbelianSquare_independent_neighborhood D₀ D₁,hE]
    exact hpoint k z hz

end NLS.ZakharovShabat
