import NLS.ZakharovShabat.SourceSobolevMidpointUniformTail
import NLS.ZakharovShabat.SourceSobolevGapUniformTail
import NLS.ZakharovShabat.SourcePsiSobolevUniformLittleO
import NLS.ZakharovShabat.SourcePsiMidpointFilledFactorMajorant
import NLS.SequenceSpaces.UniformKernelMultiplierTails

/-! The actual midpoint-filled chi tends uniformly to i on whole gaps.
The omitted-midpoint denominator is retained, before all omitted indices,
on one fixed full complex normalized Sobolev source neighborhood. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem SourcePsiSquaredGapComplexExtension.exists_local_sobolev_chi_uniform_tail
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (t : ℝ) (ht : 0<t) (ht1 : t<1) (φ : realTypeSourceSubmodule 2)
    (hφV : normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht.le) φ.val∈V) :
    let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht.le)
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ.val∈T ∧ T⊆L ⁻¹' V ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ ψ∈T, ∀ n k : ℤ, K≤k.natAbs → k≠n →
        ∀ z∈sourcePeriodicSegment (by norm_num) (by norm_num) (L ψ) k,
          ‖sourcePsiMidpointFilledRegularFactor (by norm_num) (by norm_num) n k
            (s n (L ψ)) (L ψ) z-I‖≤ε := by
  intro L
  obtain ⟨Tm,hTm,hφm,hmid⟩ := exists_local_sobolev_midpoint_uniform_tail
    (by norm_num) (by norm_num) t ht φ.val φ.property
  obtain ⟨Tg,hTg,hφg,hgap⟩ := exists_local_sobolev_gap_uniform_tail t ht φ.val
  obtain ⟨Tq,hTq,hφq,hqV,hquot⟩ :=
    hs.exists_local_sobolev_filled_quotient_uniform_littleO t ht ht1 φ hφV
  obtain ⟨Vs,hVs,hφs,D,hD,Ks,hsep⟩ :=
    exists_local_sourcePeriodicMidpoint_tail_lattice_separation (by norm_num) (by norm_num) (L φ.val)
  obtain ⟨Ki,Vi,hVi,hφi,htiny⟩ :=
    exists_local_sourcePeriodicMidpointGap_tiny_tail (by norm_num) (by norm_num) (L φ.val)
  let T := ((Tm∩Tg)∩Tq)∩L ⁻¹' (Vs∩Vi)
  have hT : IsOpen T := ((hTm.inter hTg).inter hTq).inter ((hVs.inter hVi).preimage L.continuous)
  have hφT : φ.val∈T := ⟨⟨⟨hφm,hφg⟩,hφq⟩,hφs,hφi⟩
  let μ := fun ψ => sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) (L ψ)
  have hμ : ∀ ψ∈T, ∀ k, 0≤‖μ ψ k‖ ∧ ‖μ ψ k‖≤D := by
    intro ψ hψ k
    exact ⟨norm_nonneg _,(lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) (μ ψ) k).trans
      (hsep (L ψ) hψ.2.1).1⟩
  have hμtail : ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ ψ∈T, ∀ k : ℤ, K≤k.natAbs → ‖μ ψ k‖≤ε := by
    intro ε hε
    obtain ⟨K,hK⟩ := hmid ε hε
    exact ⟨K,fun ψ hψ k hk => hK ψ hψ.1.1.1 k hk⟩
  have hrec := Coeff.exists_uniform_punctured_multiplier_tail T (fun ψ k => ‖μ ψ k‖) D hD hμ hμtail
  refine ⟨T,hT,hφT,(fun _ hψ => hqV hψ.1.2),?_⟩
  intro ε hε
  let c := 4+4/Real.pi
  have hc : 0<c := by dsimp only [c];positivity
  let δ := ε/c
  have hδ : 0<δ := div_pos hε hc
  have hδε : 2*δ+(4/Real.pi)*δ≤ε := by
    have he : δ*c=ε := div_mul_cancel₀ ε hc.ne'
    dsimp only [c] at he
    nlinarith
  obtain ⟨Kr,hKr⟩ := hrec δ hδ
  obtain ⟨Km,hKm⟩ := hmid (δ/2) (half_pos hδ)
  obtain ⟨Kg,hKg⟩ := hgap δ hδ
  obtain ⟨Kq,hKq⟩ := hquot δ hδ
  refine ⟨max (max Ks Ki) (max (max Kr Km) (max Kg Kq)),?_⟩
  intro ψ hψ n k hk hkn z hz
  have hks : Ks≤k.natAbs := (le_max_left Ks Ki).trans ((le_max_left _ _).trans hk)
  have hki : Ki≤k.natAbs := (le_max_right Ks Ki).trans ((le_max_left _ _).trans hk)
  have hkr : Kr≤k.natAbs := (le_max_left Kr Km).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hk))
  have hkm : Km≤k.natAbs := (le_max_right Kr Km).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hk))
  have hkg : Kg≤k.natAbs := (le_max_left Kg Kq).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hk))
  have hkq : Kq≤k.natAbs := (le_max_right Kg Kq).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hk))
  let d := |((n-k:ℤ):ℝ)|
  have hd1 : 1≤d := by
    dsimp only [d]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hkn.symm)
  have hd : 0<d := zero_lt_one.trans_le hd1
  have hμn : ‖μ ψ n‖/d≤δ := by
    have h := hKr ψ hψ k hkr n
    rw [Coeff.puncturedLattice_apply,if_neg (sub_ne_zero.mpr hkn),norm_inv,Complex.norm_intCast] at h
    dsimp only [d]
    simpa only [Int.cast_sub,abs_sub_comm,div_eq_mul_inv,mul_comm] using h
  have hzδ : z∈closedBall ((Real.pi:ℂ)*k) δ := by
    have hmidk : ‖sourceStandardRootMidpoint (by norm_num) (by norm_num) (L ψ) k-(Real.pi:ℂ)*k‖≤δ/2 := by
      have h := hKm ψ hψ.1.1.1 k hkm
      change ‖sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) (L ψ) k‖≤δ/2 at h
      simpa only [sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] using h
    have hzg := norm_sourceMidpoint_sub_le_halfGap (by norm_num) (by norm_num) (L ψ) k z hz
    have hg := hKg ψ hψ.1.1.2 k hkg
    rw [mem_closedBall,dist_eq_norm]
    calc
      _ = ‖(z-sourceStandardRootMidpoint (by norm_num) (by norm_num) (L ψ) k)+
          (sourceStandardRootMidpoint (by norm_num) (by norm_num) (L ψ) k-(Real.pi:ℂ)*k)‖ := by congr 1;ring
      _ ≤ ‖z-sourceStandardRootMidpoint (by norm_num) (by norm_num) (L ψ) k‖+
          ‖sourceStandardRootMidpoint (by norm_num) (by norm_num) (L ψ) k-(Real.pi:ℂ)*k‖ := norm_add_le _ _
      _ ≤ ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) k‖/2+δ/2 :=
        add_le_add (by simpa only [norm_sub_rev] using hzg) hmidk
      _ ≤ δ := by linarith
  obtain ⟨hmi,hga⟩ := htiny (L ψ) hψ.2.2 k hki
  have hz8 := sourcePeriodicSegment_subset_free_eighth_ball (by norm_num) (by norm_num) (L ψ) k hmi hga hz
  have hQ : ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k
      (z,(sourcePsiFillDeletedRoot n (s n (L ψ))
        (sourceStandardRootMidpoint (by norm_num) (by norm_num) (L ψ) n),L ψ))-1‖≤δ := by
    have hw : 1≤Weight.sobolev t k := by simpa only [Weight.sobolev_zero_apply] using Weight.sobolev_mono ht.le k
    exact (le_mul_of_one_le_left (norm_nonneg _) hw).trans (hKq ψ hψ.1.2 n k hkq z hz)
  have hb := norm_sourcePsiMidpointFilledRegularFactor_sub_I_le (by norm_num) (by norm_num) n k hkn
    (s n (L ψ)) (L ψ) (lp.single 2 k (δ:ℂ)) ‖μ ψ n‖ δ (norm_nonneg _) hδ.le
    (by
      change ‖sourceStandardRootMidpoint (by norm_num) (by norm_num) (L ψ) n-(Real.pi:ℂ)*n‖≤
        ‖sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) (L ψ) n‖
      simp only [sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint,le_refl]) z hzδ
    ((hsep (L ψ) hψ.2.1).2 k hks n hkn.symm z (ball_subset_closedBall hz8))
    (by simpa only [lp.single_apply,Pi.single_eq_same,Complex.norm_real,Real.norm_of_nonneg hδ.le] using hQ)
  simp only [lp.single_apply,Pi.single_eq_same,Complex.norm_real,Real.norm_of_nonneg hδ.le] at hb
  have hradius : δ/d≤δ := div_le_self hδ.le hd1
  have hsum : (‖μ ψ n‖+δ)/d≤2*δ := by rw [add_div];linarith
  apply hb.trans
  change 2*δ+(2/Real.pi)*(‖μ ψ n‖+δ)/d≤ε
  calc
    _ = 2*δ+(2/Real.pi)*((‖μ ψ n‖+δ)/d) := by ring
    _ ≤ 2*δ+(2/Real.pi)*(2*δ) := by gcongr
    _ = 2*δ+(4/Real.pi)*δ := by ring
    _ ≤ ε := hδε

end NLS.ZakharovShabat
