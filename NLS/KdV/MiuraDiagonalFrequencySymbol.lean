import NLS.ZakharovShabat.SourceRegularDiagonalSequenceBounds
import NLS.ZakharovShabat.SourceOppositeSecondMomentSequence
import NLS.ZakharovShabat.SourceFirstWeightedActionSequence
import NLS.ZakharovShabat.SourceNormalizedWeightedActionPositive
import NLS.SequenceSpaces.AffinePositiveSymbolReciprocal
import NLS.KdV.MiuraCanonicalRootReflection
import NLS.KdV.HillMiuraPositiveGaps

/-! The corrected actual Miura diagonal frequency is the actual first
weighted action times a bounded analytic Hilbert symbol. Positivity at
all real positive gaps, including closed gaps, supplies one reciprocal
neighborhood before every frequency index. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem exists_Miura_diagonal_frequency_symbol
    {W V R : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W)
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s) (hV : IsOpen V)
    (A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) R s) (D : SourceAbelianMomentErrorDomain A)
    (u : PeriodOneRealL2) (huV : hillMiuraDiagonal u.val∈V)
    (huC : hillMiuraDiagonal u.val∈ball C.discs.source.val C.discs.sourceRadius) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ hillMiuraDiagonal u.val∈U ∧
      U⊆D.domain∩V∩ball C.discs.source.val C.discs.sourceRadius ∧
      ∃ M : ℝ, 0≤M ∧ ∃ σ : CoeffPair 2 → Coeff 2, AnalyticOnNhd ℂ σ U ∧
        (∀ ψ∈U, ‖σ ψ‖≤M) ∧ (∀ ψ∈U, ∀ j : ℤ, j≤0 → σ ψ j=0) ∧
        (∀ ψ∈U, ∀ n : ℕ+, C.normalizedWeightedAction (n : ℤ) 1 ψ≠0 ∧
          σ ψ (n : ℤ)=1-(n : ℂ)*(C.normalizedSecondMoment s (n : ℤ) (n : ℤ) ψ-
            C.normalizedSecondMoment s (n : ℤ) (-(n : ℤ)) ψ)/C.normalizedWeightedAction (n : ℤ) 1 ψ) ∧
        ∀ v : Coeff 2, hillMiuraDiagonal v∈U → ∀ n : ℕ+,
          let ψ := hillMiuraDiagonal v;
          -12*(n : ℂ)*(A.moment (n : ℤ) (n : ℤ) 2 ψ-A.moment (n : ℤ) (-(n : ℤ)) 2 ψ)+
              12*sourceComplexHigherAction (by norm_num) (by norm_num) (n : ℤ) 1 ψ=
            12*sourceComplexHigherAction (by norm_num) (by norm_num) (n : ℤ) 1 ψ*σ ψ (n : ℤ) := by
  let φ := hillMiuraRealSource u
  obtain ⟨rd,hrd,hsubd,Md,hMd,Gd,hGd,hvd,hbd⟩ := C.exists_ball_regularDiagonal_error_l2 hs hV A D φ huV huC
  obtain ⟨rx,hrx,_hsubx,Kx,hKx,Gx,hGx,hvx,_hpx,hbx⟩ := C.exists_ball_opposite_secondMoment_l2 hs hV A D φ huV huC
  obtain ⟨r1,hr1,_hsub1,M1,hM1,G1,hG1,hv1,hb1⟩ := C.exists_ball_firstWeightedAction_error_l2 φ huC
  obtain ⟨rh,hrh,_hsubh,hNh⟩ := C.exists_ball_normalizedWeightedActions
    (sourceHigherActionAtlas (by norm_num) (by norm_num)) φ huC
  let T := (ball φ.val rd∩ball φ.val rx)∩(ball φ.val r1∩ball φ.val rh)
  have hT : IsOpen T := (isOpen_ball.inter isOpen_ball).inter (isOpen_ball.inter isOpen_ball)
  have hφT : φ.val∈T := ⟨⟨mem_ball_self hrd,mem_ball_self hrx⟩,mem_ball_self hr1,mem_ball_self hrh⟩
  have hG1T : AnalyticOnNhd ℂ G1 T := hG1.mono (fun ψ hψ => hψ.2.1)
  have hne (j : ℤ) (hj : 0<j) : (Real.pi : ℂ)+G1 φ.val j≠0 := by
    have hpos := C.normalizedWeightedAction_one_real_positive φ huC j
      (hillMiura_positive_gap_left_pos u j hj)
    have hW : C.normalizedWeightedAction j 1 φ.val≠0 := by
      intro hz
      rw [hz,zero_re] at hpos
      linarith [hpos.1]
    rw [hv1 φ.val (mem_ball_self hr1) j,if_neg (ne_of_gt hj)]
    convert (div_ne_zero (mul_ne_zero (by norm_num : (4 : ℂ)≠0) hW)
      (by exact_mod_cast (ne_of_gt hj) : (j : ℂ)≠0)) using 1
    ring
  obtain ⟨U,hU,hφU,hUT,BN,hBN,N,hNa,hNd⟩ := Coeff.exists_local_affine_positive_reciprocal
    (by norm_num : (2 : ℝ≥0∞)≠⊤) T hT G1 hG1T (Real.pi : ℂ)
    (ofReal_ne_zero.mpr Real.pi_ne_zero) φ.val hφT hne
  let E := fun ψ => G1 ψ-Gd ψ+(4 : ℂ) • Gx ψ
  have hE : AnalyticOnNhd ℂ E U :=
    ((hG1.mono (fun ψ hψ => (hUT hψ).2.1)).sub
      (hGd.mono (fun ψ hψ => (hUT hψ).1.1))).add
        ((analyticOnNhd_const).smul (hGx.mono (fun ψ hψ => (hUT hψ).1.2)))
  let σ := fun ψ => Coeff.holderProduct (q := 2) (N ψ) (E ψ)
  have hσ : AnalyticOnNhd ℂ σ U := fun ψ hψ =>
    ((Coeff.holderProduct (p := ⊤) (r := 2) (q := 2)).analyticAt_bilinear _).comp₂ (hNa ψ hψ) (hE ψ hψ)
  have hraw (ψ : CoeffPair 2) (hψ : ψ∈U) (n : ℕ+) :
      C.normalizedWeightedAction (n : ℤ) 1 ψ≠0 ∧
        σ ψ (n : ℤ)=1-(n : ℂ)*(C.normalizedSecondMoment s (n : ℤ) (n : ℤ) ψ-
          C.normalizedSecondMoment s (n : ℤ) (-(n : ℤ)) ψ)/C.normalizedWeightedAction (n : ℤ) 1 ψ := by
    have hn : (n : ℤ)≠0 := by exact_mod_cast n.pos.ne'
    have hnC : (n : ℂ)≠0 := by exact_mod_cast n.pos.ne'
    have hact : (Real.pi : ℂ)+G1 ψ (n : ℤ)=4*C.normalizedWeightedAction (n : ℤ) 1 ψ/(n : ℂ) := by
      rw [hv1 ψ (hUT hψ).2.1 (n : ℤ),if_neg hn]
      push_cast
      ring
    have hW : C.normalizedWeightedAction (n : ℤ) 1 ψ≠0 := by
      intro hz
      have hz' := (hNd ψ hψ).2.2 n |>.1
      rw [hact,hz,mul_zero,zero_div] at hz'
      exact hz' rfl
    refine ⟨hW,?_⟩
    change N ψ (n : ℤ)*(G1 ψ (n : ℤ)-Gd ψ (n : ℤ)+4*Gx ψ (n : ℤ))=_
    rw [(hNd ψ hψ).2.2 n |>.2,hact,hv1 ψ (hUT hψ).2.1 (n : ℤ),if_neg hn,
      hvd ψ (hUT hψ).1.1 (n : ℤ),hvx ψ (hUT hψ).1.2 (n : ℤ),if_neg hn]
    unfold SourceFullAbelianUniformCauchyFamily.regularDiagonalSecondMomentError
    push_cast
    field_simp
    ring
  let MX := Kx*‖Coeff.puncturedLattice 2 (by norm_num)‖
  have hMX : 0≤MX := mul_nonneg hKx (norm_nonneg _)
  refine ⟨U,hU,hφU,fun ψ hψ => hsubd (hUT hψ).1.1,
    BN*(M1+Md+4*MX),by positivity,σ,hσ,?_,?_,hraw,?_⟩
  · intro ψ hψ
    have heB : ‖E ψ‖≤M1+Md+4*MX := by
      have hh := norm_add_le (G1 ψ-Gd ψ) ((4 : ℂ) • Gx ψ)
      rw [norm_smul,norm_ofNat] at hh
      exact hh.trans (add_le_add ((norm_sub_le _ _).trans
        (add_le_add (hb1 ψ (hUT hψ).2.1) (hbd ψ (hUT hψ).1.1)))
        (mul_le_mul_of_nonneg_left (hbx ψ (hUT hψ).1.2) (by norm_num)))
    exact (Coeff.norm_holderProduct_le _ _).trans
      (mul_le_mul ((hNd ψ hψ).1) heB (norm_nonneg _) hBN)
  · intro ψ hψ j hj
    change N ψ j*E ψ j=0
    rw [(hNd ψ hψ).2.1 j hj,zero_mul]
  · intro v hv n
    let ψ := hillMiuraDiagonal v
    have hdψ := (hsubd (hUT hv).1.1).1.1
    have hCψ := (hsubd (hUT hv).1.1).2
    have hact : sourceComplexHigherAction (by norm_num) (by norm_num) (n : ℤ) 1 ψ=
        (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ (n : ℤ))^2*
          C.normalizedWeightedAction (n : ℤ) 1 ψ := by
      simpa only [sourceComplexHigherAction,sourcePeriodicGapDisplacement_apply] using
        (hNh (n : ℤ) 1).2 ψ (hUT hv).2.2
    have hgap : sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ (-(n : ℤ))=
        sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ (n : ℤ) := by
      simpa only [sourcePeriodicGapDisplacement_apply] using (sourcePeriodicReflection_hillMiuraDiagonal v).gap_neg (n : ℤ)
    dsimp only
    rw [C.moment_two_eq_squaredGap_mul_normalized A D ψ hdψ hCψ (n : ℤ) (n : ℤ),
      C.moment_two_eq_squaredGap_mul_normalized A D ψ hdψ hCψ (n : ℤ) (-(n : ℤ)),hact,hgap,(hraw ψ hv n).2]
    have hW := (hraw ψ hv n).1
    field_simp
    ring

end NLS.KdV
