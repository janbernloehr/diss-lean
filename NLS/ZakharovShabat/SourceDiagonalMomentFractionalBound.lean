import NLS.ZakharovShabat.SourceSquareFractionalGapBound
import NLS.ZakharovShabat.SourcePsiFractionalQuotientDecay
import NLS.ZakharovShabat.SourceAbelianMomentDiagonalCoefficients
import NLS.ComplexAnalysis.WeightedQuadraticRemainder

/-! Fractional errors of the ACTUAL raw diagonal moments on complex
weighted-source neighborhoods. Two literal gap factors remain in the
bound, so closed gaps require no division or density argument. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W V : Set (CoeffPair 2)}
variable {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem SourceAbelianMomentErrorDomain.exists_local_sobolev_diagonal_moment_bound
    {A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s}
    (D : SourceAbelianMomentErrorDomain A)
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (t : ℝ) (ht : 0≤t) (u : ℝ) (hu0 : 0≤u) (hu1 : u≤1) (hut : u≤t)
    (φ : realTypeSourceSubmodule 2)
    (hφV : normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht) φ.val∈V) :
    let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ.val∈T ∧ T⊆L ⁻¹' (D.domain∩V) ∧
      ∃ K : ℕ, ∃ M : ℝ, 0≤M ∧ ∀ ψ∈T, ∀ k : ℤ, K≤k.natAbs →
        Weight.sobolev u k*‖A.moment k k 2 (L ψ)-
          (Real.pi:ℂ)*(sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) k)^2/4‖≤
            ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) k‖^2*M := by
  intro L
  have hrφ : L φ.val∈realTypeSourceLocus 2 :=
    normalizedWeightedSource_realType (sourceSobolevSpectralWeight t ht) φ.val φ.property
  let φ₀ : realTypeSourceSubmodule 2 := ⟨L φ.val,hrφ⟩
  obtain ⟨W',_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num)
  obtain ⟨C,hcenter⟩ := hfamilies φ₀
  have hφC : L φ.val∈ball C.discs.source.val C.discs.sourceRadius := by
    rw [hcenter]
    exact mem_ball_self C.discs.sourceRadius_pos
  have hφA : L φ.val∈A.sourceBall φ₀ := mem_ball_self (A.localChart φ₀).radius_pos
  obtain ⟨Ts,hTs,hφs,Ks,Ms,hMs,hsquare⟩ :=
    exists_local_sobolev_square_gap_bound t ht u hu0 hu1 hut φ
  obtain ⟨Nq,εq,_hεq,Tq,hTq,hφq,hqV,Kq,hNKq,Mq,hMq,hquot⟩ :=
    hs.exists_local_sobolev_filled_quotient_decay t ht u hu0 hu1 (by linarith) φ hφV
  obtain ⟨Kg,Vg,hVg,hφg,htiny⟩ :=
    exists_local_sourcePeriodicMidpointGap_tiny_tail (by norm_num) (by norm_num) (L φ.val)
  let T := (Ts∩Tq)∩L ⁻¹' ((D.domain∩A.sourceBall φ₀)∩
    (ball C.discs.source.val C.discs.sourceRadius∩Vg))
  have hT : IsOpen T := (hTs.inter hTq).inter
    (((D.isOpen_domain.inter isOpen_ball).inter (isOpen_ball.inter hVg)).preimage L.continuous)
  have hφT : φ.val∈T := ⟨⟨hφs,hφq⟩,⟨D.real_subset hrφ,hφA⟩,hφC,hφg⟩
  let B := 8*Real.pi*(Ms*(Mq+1)+Mq/4)
  have hB : 0≤B := by dsimp only [B];positivity
  refine ⟨T,hT,hφT,(fun ψ hψ => ⟨hψ.2.1.1,hqV hψ.1.2⟩),
    max Ks (max Kq Kg),B/4,div_nonneg hB (by norm_num),?_⟩
  intro ψ hψ k hk
  have hks : Ks≤k.natAbs := (le_max_left _ _).trans hk
  have hkq : Kq≤k.natAbs := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hkg : Kg≤k.natAbs := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ)
  let w := Weight.sobolev u k
  have hw : 0<w := (Weight.sobolev u).positive k
  have hw1 : 1≤w := by
    simpa only [Weight.sobolev_zero_apply] using Weight.sobolev_mono hu0 k
  obtain ⟨D₀⟩ := (A.localChart φ₀).charts (L ψ) hψ.2.1.2
  obtain ⟨D₁⟩ := C.charts (L ψ) hψ.2.2.1
  have hS : ∀ z∈sourcePeriodicSegment (by norm_num) (by norm_num) (L ψ) k,
      ‖sourceFullAbelianSquare (by norm_num) (by norm_num) W k (z,L ψ)+
        sourceAngularSelectedPolynomial (by norm_num) (by norm_num) (L ψ) k z‖≤‖γ k‖^2*(Ms/w) := by
    intro z hz
    rw [sourceFullAbelianSquare_independent_neighborhood D₀ D₁]
    have hb := hsquare ψ hψ.1.1 W' C hψ.2.2.1 k hks z hz
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using hb)
  have hQ : ∀ z∈sourcePeriodicSegment (by norm_num) (by norm_num) (L ψ) k,
      ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k
        (z,(sourcePsiFillDeletedRoot k (s k (L ψ))
          (sourceStandardRootMidpoint (by norm_num) (by norm_num) (L ψ) k),L ψ))-1‖≤Mq/w := by
    intro z hz
    obtain ⟨hm,hg⟩ := htiny (L ψ) hψ.2.2.2 k hkg
    have hz8 := sourcePeriodicSegment_subset_free_eighth_ball (by norm_num) (by norm_num) (L ψ) k hm hg hz
    have hzq : z∈sourceIsolatingDisc (by norm_num) (by norm_num) (L φ.val) Nq εq k := by
      simp only [sourceIsolatingDisc,if_neg (by omega : ¬k.natAbs≤Nq)]
      exact (mem_ball.mp hz8).trans (by linarith [Real.pi_pos])
    exact (le_div_iff₀ hw).mpr
      (by simpa only [mul_comm] using hquot ψ hψ.1.2 k k hkq z hzq)
  obtain ⟨hc,he⟩ := D.diagonal_coefficient_bound (L ψ) hψ.2.1.1 k (Ms/w) (Mq/w)
    (div_nonneg hMs hw.le) (div_nonneg hMq hw.le) hS hQ
  have hweighted := NLS.weighted_diagonal_coefficient_error_bound w Ms Mq _ hw1 hMs hMq hc
  have hraw := NLS.ComplexAnalysis.weighted_quadratic_remainder_bound w B (γ k)
    (A.moment k k 2 (L ψ)) (Real.pi:ℂ) (sourceSecondMomentDiagonalCoefficient A (L ψ) k) he hweighted
  simpa only [mul_div_assoc] using hraw

end NLS.ZakharovShabat
