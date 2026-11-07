import NLS.ZakharovShabat.SourceDiagonalMomentFractionalBound
import NLS.ZakharovShabat.SourcePsiSobolevUniformLittleO
import NLS.ZakharovShabat.SourceSquareSobolevUniformLittleO

/-! Uniform little-o of the actual raw diagonal second moment, with
both literal selected-gap factors and one fixed complex neighborhood. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem SourceAbelianMomentErrorDomain.exists_local_sobolev_diagonal_moment_uniform_littleO
    {A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s}
    (D : SourceAbelianMomentErrorDomain A)
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (φ : realTypeSourceSubmodule 2)
    (hφV : normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht.le) φ.val ∈ V) :
    let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht.le)
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ L ⁻¹' (D.domain ∩ V) ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ ψ ∈ T, ∀ k : ℤ, K ≤ k.natAbs →
        Weight.sobolev t k * ‖A.moment k k 2 (L ψ)-
          (Real.pi:ℂ)*(sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) k)^2/4‖ ≤
            ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) k‖^2*ε := by
  intro L
  have hrφ := normalizedWeightedSource_realType (sourceSobolevSpectralWeight t ht.le) φ.val φ.property
  let φ₀ : realTypeSourceSubmodule 2 := ⟨L φ.val,hrφ⟩
  obtain ⟨W',_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num)
  obtain ⟨C,hcenter⟩ := hfamilies φ₀
  have hφC : L φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hcenter]
    exact mem_ball_self C.discs.sourceRadius_pos
  have hφA : L φ.val ∈ A.sourceBall φ₀ := mem_ball_self (A.localChart φ₀).radius_pos
  obtain ⟨Ts,hTs,hφs,hsquare⟩ := exists_local_sobolev_square_gap_uniform_littleO t ht ht1 φ
  obtain ⟨Tq,hTq,hφq,hqV,hquot⟩ :=
    hs.exists_local_sobolev_filled_quotient_uniform_littleO t ht ht1 φ hφV
  let T := (Ts ∩ Tq) ∩ L ⁻¹' ((D.domain ∩ A.sourceBall φ₀) ∩
    ball C.discs.source.val C.discs.sourceRadius)
  have hT : IsOpen T := (hTs.inter hTq).inter
    (((D.isOpen_domain.inter isOpen_ball).inter isOpen_ball).preimage L.continuous)
  refine ⟨T,hT,⟨⟨hφs,hφq⟩,⟨D.real_subset hrφ,hφA⟩,hφC⟩,
    (fun _ hψ => ⟨hψ.2.1.1,hqV hψ.1.2⟩),?_⟩
  intro ε hε
  let δ := min 1 (ε/(8*Real.pi))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : 8*Real.pi*δ ≤ ε := by
    have h : δ*(8*Real.pi) ≤ ε :=
      (le_div_iff₀ (by positivity : 0 < 8*Real.pi)).mp (min_le_right _ _)
    simpa only [mul_comm] using h
  have hsmall : 8*Real.pi*(δ*(δ+1)+δ/4)/4 ≤ ε := by
    have hp : δ*(δ+1)+δ/4 ≤ 4*δ := by nlinarith
    calc
      _ ≤ 8*Real.pi*(4*δ)/4 := by gcongr
      _ = 8*Real.pi*δ := by ring
      _ ≤ ε := hδε
  obtain ⟨Ks,hKs⟩ := hsquare δ hδ
  obtain ⟨Kq,hKq⟩ := hquot δ hδ
  refine ⟨max Ks Kq,?_⟩
  intro ψ hψ k hk
  let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ)
  let w := Weight.sobolev t k
  have hw : 0 < w := (Weight.sobolev t).positive k
  have hw1 : 1 ≤ w := by
    simpa only [Weight.sobolev_zero_apply] using Weight.sobolev_mono ht.le k
  obtain ⟨D₀⟩ := (A.localChart φ₀).charts (L ψ) hψ.2.1.2
  obtain ⟨D₁⟩ := C.charts (L ψ) hψ.2.2
  have hS : ∀ z ∈ sourcePeriodicSegment (by norm_num) (by norm_num) (L ψ) k,
      ‖sourceFullAbelianSquare (by norm_num) (by norm_num) W k (z,L ψ)+
        sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (L ψ) k z‖ ≤ ‖γ k‖^2*(δ/w) := by
    intro z hz
    rw [sourceFullAbelianSquare_independent_neighborhood D₀ D₁,← mul_div_assoc]
    exact (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using
      (hKs ψ hψ.1.1 W' C hψ.2.2 k ((le_max_left _ _).trans hk) z hz))
  have hQ : ∀ z ∈ sourcePeriodicSegment (by norm_num) (by norm_num) (L ψ) k,
      ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k
        (z,(sourcePsiFillDeletedRoot k (s k (L ψ))
          (sourceStandardRootMidpoint (by norm_num) (by norm_num) (L ψ) k),L ψ))-1‖ ≤ δ/w := by
    intro z hz
    exact (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using
      (hKq ψ hψ.1.2 k k ((le_max_right _ _).trans hk) z hz))
  obtain ⟨hc,he⟩ := D.diagonal_coefficient_bound (L ψ) hψ.2.1.1 k (δ/w) (δ/w)
    (div_nonneg hδ.le hw.le) (div_nonneg hδ.le hw.le) hS hQ
  have hweighted := NLS.weighted_diagonal_coefficient_error_bound w δ δ _ hw1 hδ.le hδ.le hc
  have hraw := NLS.ComplexAnalysis.weighted_quadratic_remainder_bound w
    (8*Real.pi*(δ*(δ+1)+δ/4)) (γ k) (A.moment k k 2 (L ψ)) (Real.pi:ℂ)
    (sourceSecondMomentDiagonalCoefficient A (L ψ) k) he hweighted
  exact hraw.trans (by simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left hsmall (sq_nonneg ‖γ k‖))

end NLS.ZakharovShabat
