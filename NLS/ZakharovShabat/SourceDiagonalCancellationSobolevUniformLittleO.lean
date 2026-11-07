import NLS.ZakharovShabat.SourceFirstWeightedActionSobolevUniformLittleO
import NLS.ZakharovShabat.SourceDiagonalMomentSobolevUniformLittleO
import NLS.ZakharovShabat.SourceRefinedCubicNormBounds

/-! Fixed-neighborhood uniform little-o for the ACTUAL diagonal
moment/action cancellation, retaining two gap factors at collapse. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem SourceAbelianMomentErrorDomain.exists_local_sobolev_diagonal_cancellation_uniform_littleO
    {A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s}
    (D : SourceAbelianMomentErrorDomain A)
    (A₀ : SourceHigherActionAtlas (by norm_num) (by norm_num))
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus 2⊆V)
    (t : ℝ) (ht : 0<t) (ht1 : t<1)
    (φ : realTypeSourceSubmodule 2) :
    let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht.le)
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ.val∈T ∧ T⊆L ⁻¹' (D.domain∩V∩A₀.domain) ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ ψ∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
        sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) (-(n:ℤ))=
          sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) (n:ℤ) →
        Weight.sobolev (t-1) (n:ℤ)*‖-12*(n:ℂ)*
          (A.moment (n:ℤ) (n:ℤ) 2 (L ψ)-A.moment (n:ℤ) (-(n:ℤ)) 2 (L ψ))+
            12*A₀.action (n:ℤ) 1 (L ψ)‖≤
              ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) (n:ℤ)‖^2*ε := by
  intro L
  have hrφ := normalizedWeightedSource_realType (sourceSobolevSpectralWeight t ht.le) φ.val φ.property
  let φ₀ : realTypeSourceSubmodule 2 := ⟨L φ.val,hrφ⟩
  obtain ⟨W',_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num)
  obtain ⟨C,hcenter⟩ := hfamilies φ₀
  have hφC : L φ.val∈ball C.discs.source.val C.discs.sourceRadius := by
    rw [hcenter]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨Ta,hTa,hφa,haA,ha⟩ :=
    C.exists_local_sobolev_firstWeightedAction_uniform_littleO A₀ t ht ht1 φ hφC
  obtain ⟨Td,hTd,hφd,hdD,hd⟩ :=
    D.exists_local_sobolev_diagonal_moment_uniform_littleO hs t ht ht1 φ (hrealV hrφ)
  obtain ⟨U,_hU,hrealU,_hUV,hcubic⟩ := A.exists_local_refinedCubicNormBounds hs hV hrealV
  obtain ⟨ρ,hρ,_hρU,_D,Mc,_hD,hMc,hrows⟩ := hcubic (L φ.val) (hrealU hrφ)
  obtain ⟨_Ng,_hNg,G,hG,hφG,H,hH,hgap⟩ := exists_uniform_small_sourcePeriodicGapDisplacement
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num) (L φ.val) (by norm_num : (0 : ℝ)<1)
  let T := (Ta∩Td)∩L ⁻¹' (ball (L φ.val) ρ∩G)
  have hT : IsOpen T := (hTa.inter hTd).inter ((isOpen_ball.inter hG).preimage L.continuous)
  have hφball : L φ.val∈ball (L φ.val) ρ := mem_ball_self hρ
  have hφT : φ.val∈T := ⟨⟨hφa,hφd⟩,hφball,hφG⟩
  refine ⟨T,hT,hφT,(fun ψ hψ => ⟨hdD hψ.1.2,haA hψ.1.1⟩),?_⟩
  intro ε hε
  let P := H*(Mc/2)
  have hP : 0≤P := by dsimp only [P];positivity
  let η := ε/(12*(P+3))
  have hden : 0<12*(P+3) := by positivity
  have hη : 0<η := div_pos hε hden
  have hηsum : 12*(η+η+η*P)≤ε := by
    have he : η*(12*(P+3))=ε := div_mul_cancel₀ ε hden.ne'
    nlinarith
  obtain ⟨Ka,hKa⟩ := ha η hη
  obtain ⟨Kd,hKd⟩ := hd η hη
  obtain ⟨Kr,hKr⟩ := Weight.exists_sobolev_ratio_tail (t-1) 0 (by linarith) hη
  refine ⟨max (max Ka Kd) Kr,?_⟩
  intro ψ hψ n hn hreflect
  have hna : Ka≤(n:ℤ).natAbs := (le_max_left Ka Kd).trans ((le_max_left _ _).trans hn)
  have hnd : Kd≤(n:ℤ).natAbs := (le_max_right Ka Kd).trans ((le_max_left _ _).trans hn)
  have hnr : Kr≤(n:ℤ).natAbs := (le_max_right _ _).trans hn
  let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) (n:ℤ)
  let r := Weight.sobolev (t-1) (n:ℤ)
  let w := Weight.sobolev t (n:ℤ)
  have hr : 0≤r := ((Weight.sobolev (t-1)).positive (n:ℤ)).le
  have hrw : r*‖(n:ℂ)‖≤w := by
    have hnle : ‖(n:ℂ)‖≤Weight.sobolev 1 (n:ℤ) := by
      have h : ‖(((n:ℤ):ℂ))‖≤Weight.sobolev 1 (n:ℤ) := by
        rw [Complex.norm_intCast]
        simp only [Weight.sobolev_apply,Real.rpow_one]
        linarith
      simpa only [Int.cast_natCast] using h
    have he : r*Weight.sobolev 1 (n:ℤ)=w := by
      dsimp only [r,w]
      rw [← Weight.sobolev_add,sub_add_cancel]
    exact (mul_le_mul_of_nonneg_left hnle hr).trans_eq he
  have hγ : ‖γ‖≤H :=
    (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞)≠0)
      (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ)) (n:ℤ)).trans (hgap (L ψ) hψ.2.2).1
  have hnn : (n:ℤ)≠0 := by exact_mod_cast n.pos.ne'
  have hnnC : (n:ℂ)≠0 := by exact_mod_cast n.pos.ne'
  have htwo : (n:ℤ)-(-(n:ℤ))≠0 := by omega
  have hkernel : ‖(n:ℂ)‖*‖Coeff.puncturedLattice 2 (by norm_num) ((n:ℤ)-(-(n:ℤ)))‖=1/2 := by
    rw [Coeff.puncturedLattice_apply,if_neg htwo,norm_inv]
    have he : (((n:ℤ)-(-(n:ℤ)) : ℤ):ℂ)=2*(n:ℂ) := by push_cast;ring
    rw [he,norm_mul,Complex.norm_ofNat]
    have hnorm : ‖(n:ℂ)‖≠0 := norm_ne_zero_iff.mpr hnnC
    field_simp
  have hx : ‖(n:ℂ)*A.moment (n:ℤ) (-(n:ℤ)) 2 (L ψ)‖≤‖γ‖^3*(Mc/2) := by
    have hb := (hrows (L ψ) hψ.2.1).2 (n:ℤ) (-(n:ℤ)) (by omega)
    rw [hreflect] at hb
    rw [norm_mul]
    calc
      _≤‖(n:ℂ)‖*(Mc*‖γ‖^3*‖Coeff.puncturedLattice 2 (by norm_num) ((n:ℤ)-(-(n:ℤ)))‖) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _=(Mc*‖γ‖^3)*(‖(n:ℂ)‖*‖Coeff.puncturedLattice 2 (by norm_num) ((n:ℤ)-(-(n:ℤ)))‖) := by ring
      _=‖γ‖^3*(Mc/2) := by rw [hkernel];ring
  have ha' := hKa ψ hψ.1.1 (n:ℤ) hna
  simp only [Int.cast_natCast] at ha'
  rw [mul_comm (Real.pi:ℂ) (n:ℂ)] at ha'
  have hw := NLS.ComplexAnalysis.weighted_diagonal_action_cancellation_tail_bound w r H (Mc/2) η η
    hr (div_nonneg hMc (by norm_num)) γ (n:ℂ) (Real.pi:ℂ)
    (A₀.action (n:ℤ) 1 (L ψ)) (A.moment (n:ℤ) (n:ℤ) 2 (L ψ))
    (A.moment (n:ℤ) (-(n:ℤ)) 2 (L ψ)) hγ hrw ha' (hKd ψ hψ.1.2 (n:ℤ) hnd) hx
  have hrη : r≤η := by simpa only [Weight.sobolev_zero_apply,div_one] using (hKr (n:ℤ) hnr).le
  have hsmall : 12*(η+η+r*H*(Mc/2))≤ε := by
    calc
      _ = 12*(η+η+r*P) := by dsimp only [P];ring
      _ ≤ 12*(η+η+η*P) := by gcongr
      _ ≤ ε := hηsum
  exact hw.trans (mul_le_mul_of_nonneg_left hsmall (sq_nonneg ‖γ‖))

end NLS.ZakharovShabat
