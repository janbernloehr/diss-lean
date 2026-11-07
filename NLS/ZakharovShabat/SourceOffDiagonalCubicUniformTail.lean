import NLS.ZakharovShabat.SourcePsiChiSobolevUniformTail
import NLS.ZakharovShabat.SourceSquareSobolevUniformLittleO
import NLS.ZakharovShabat.SourceAbelianMomentSquaredOffsetError
import NLS.SequenceSpaces.CubicOffsetSmallBound

/-! Uniformly vanishing ACTUAL cubic off-diagonal moment coefficients.
The neighborhood is fixed before every tolerance and every omitted label;
all literal gap factors are retained, including collapsed complex gaps. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem SourceAbelianMomentErrorDomain.exists_local_sobolev_offDiagonal_cubic_uniform_tail
    {A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s}
    (D : SourceAbelianMomentErrorDomain A)
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (t : ℝ) (ht : 0<t) (ht1 : t<1) (φ : realTypeSourceSubmodule 2)
    (hφV : normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht.le) φ.val∈V) :
    let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht.le)
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ.val∈T ∧ T⊆L ⁻¹' (D.domain∩V) ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ ψ∈T, ∀ n k : ℤ, K≤k.natAbs → k≠n →
        ‖((n-k:ℤ):ℂ)*A.moment n k 2 (L ψ)‖ ≤
          ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) k‖^3*ε := by
  intro L
  have hrφ := normalizedWeightedSource_realType (sourceSobolevSpectralWeight t ht.le) φ.val φ.property
  let φ₀ : realTypeSourceSubmodule 2 := ⟨L φ.val,hrφ⟩
  obtain ⟨W',_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies
    (by norm_num : (2:ℝ≥0∞)≠⊤) (by norm_num)
  obtain ⟨C,hcenter⟩ := hfamilies φ₀
  have hφC : L φ.val∈ball C.discs.source.val C.discs.sourceRadius := by
    rw [hcenter]
    exact mem_ball_self C.discs.sourceRadius_pos
  have hφA : L φ.val∈A.sourceBall φ₀ := mem_ball_self (A.localChart φ₀).radius_pos
  obtain ⟨Ts,hTs,hφs,hsquare⟩ := exists_local_sobolev_square_gap_uniform_littleO t ht ht1 φ
  obtain ⟨Tc,hTc,hφc,_,hchi⟩ := hs.exists_local_sobolev_chi_uniform_tail t ht ht1 φ hφV
  obtain ⟨Tg,hTg,hφg,hgap⟩ := exists_local_sobolev_gap_uniform_tail t ht φ.val
  obtain ⟨To,hTo,hφo,hoD,B,hB,hoff⟩ := D.locally_uniform_offDiagonal_squaredOffset_bound hs
    (L φ.val) (D.real_subset hrφ) hφV
  let T := ((Ts∩Tc)∩Tg)∩L ⁻¹' ((To∩A.sourceBall φ₀)∩
    ball C.discs.source.val C.discs.sourceRadius)
  have hT : IsOpen T := ((hTs.inter hTc).inter hTg).inter
    (((hTo.inter isOpen_ball).inter isOpen_ball).preimage L.continuous)
  refine ⟨T,hT,⟨⟨⟨hφs,hφc⟩,hφg⟩,⟨hφo,hφA⟩,hφC⟩,
    (fun _ hψ => hoD hψ.2.1.1),?_⟩
  intro ε hε
  let δ := min 1 (ε/(8*B+8))
  have hden : 0<8*B+8 := by linarith
  have hδ : 0<δ := lt_min zero_lt_one (div_pos hε hden)
  have hδ1 : δ≤1 := min_le_left _ _
  have hδε : δ*(8*B+8)≤ε := (le_div_iff₀ hden).mp (min_le_right _ _)
  obtain ⟨Ks,hKs⟩ := hsquare δ hδ
  obtain ⟨Kc,hKc⟩ := hchi δ hδ
  obtain ⟨Kg,hKg⟩ := hgap δ hδ
  refine ⟨max Ks (max Kc Kg),?_⟩
  intro ψ hψ n k hk hkn
  let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ)
  have hks : Ks≤k.natAbs := (le_max_left _ _).trans hk
  have hkc : Kc≤k.natAbs := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hkg : Kg≤k.natAbs := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hG : ‖γ k‖≤δ := hKg ψ hψ.1.2 k hkg
  obtain ⟨α,_,hα,hrow⟩ := hoff (L ψ) hψ.2.1.1 n
  obtain ⟨D₀⟩ := (A.localChart φ₀).charts (L ψ) hψ.2.1.2
  obtain ⟨D₁⟩ := C.charts (L ψ) hψ.2.2
  have hS : ∀ z∈sourcePeriodicSegment (by norm_num) (by norm_num) (L ψ) k,
      ‖sourceFullAbelianSquare (by norm_num) (by norm_num) W k (z,L ψ)+
        sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (L ψ) k z‖≤‖γ k‖^2*δ := by
    intro z hz
    rw [sourceFullAbelianSquare_independent_neighborhood D₀ D₁]
    have hw : 1≤Weight.sobolev t k := by
      simpa only [Weight.sobolev_zero_apply] using Weight.sobolev_mono ht.le k
    exact (le_mul_of_one_le_left (norm_nonneg _) hw).trans
      (hKs ψ hψ.1.1.1 W' C hψ.2.2 k hks z hz)
  have hb := hrow k hkn δ δ hδ.le hS (hKc ψ hψ.1.1.2 n k hkc hkn)
  have hαk : ‖α k‖≤B := (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) α k).trans hα
  have he := (NLS.cubic_offset_remainder_small_bound ‖γ k‖ ‖α k‖ B δ
    (norm_nonneg _) hB.le hδ.le hG hαk hδ1).trans hδε
  exact hb.trans (mul_le_mul_of_nonneg_left he (by positivity))

end NLS.ZakharovShabat
