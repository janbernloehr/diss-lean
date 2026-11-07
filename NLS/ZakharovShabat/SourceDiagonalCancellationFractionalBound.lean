import NLS.ZakharovShabat.SourceFirstWeightedActionFractionalBound
import NLS.ZakharovShabat.SourceDiagonalMomentFractionalBound
import NLS.ZakharovShabat.SourceRefinedCubicNormBounds

/-! Fractional control of the ACTUAL diagonal moment/action
cancellation, retaining the squared selected gap at every collapse. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem SourceAbelianMomentErrorDomain.exists_local_sobolev_diagonal_cancellation_bound
    {A : SourceAbelianMomentAtlas (by norm_num) (by norm_num) W s}
    (D : SourceAbelianMomentErrorDomain A)
    (A₀ : SourceHigherActionAtlas (by norm_num) (by norm_num))
    (hs : SourcePsiSquaredGapComplexExtension (by norm_num) (by norm_num) V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus 2⊆V)
    (t : ℝ) (ht : 0≤t) (u : ℝ) (hu0 : 0≤u) (hu1 : u≤1) (hut : u≤t)
    (φ : realTypeSourceSubmodule 2) :
    let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ.val∈T ∧ T⊆L ⁻¹' (D.domain∩V∩A₀.domain) ∧
      ∃ K : ℕ, ∃ M : ℝ, 0≤M ∧ ∀ ψ∈T, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
        sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) (-(n:ℤ))=
          sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) (n:ℤ) →
        Weight.sobolev (u-1) (n:ℤ)*‖-12*(n:ℂ)*
          (A.moment (n:ℤ) (n:ℤ) 2 (L ψ)-A.moment (n:ℤ) (-(n:ℤ)) 2 (L ψ))+
            12*A₀.action (n:ℤ) 1 (L ψ)‖≤
              ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) (n:ℤ)‖^2*M := by
  intro L
  have hrφ := normalizedWeightedSource_realType (sourceSobolevSpectralWeight t ht) φ.val φ.property
  let φ₀ : realTypeSourceSubmodule 2 := ⟨L φ.val,hrφ⟩
  obtain ⟨W',_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num)
  obtain ⟨C,hcenter⟩ := hfamilies φ₀
  have hφC : L φ.val∈ball C.discs.source.val C.discs.sourceRadius := by
    rw [hcenter]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨Ta,hTa,hφa,haA,Ka,Ma,hMa,ha⟩ :=
    C.exists_local_sobolev_firstWeightedAction_bound A₀ t ht u hu0 hu1 hut φ hφC
  obtain ⟨Td,hTd,hφd,hdD,Kd,Md,hMd,hd⟩ :=
    D.exists_local_sobolev_diagonal_moment_bound hs t ht u hu0 hu1 hut φ (hrealV hrφ)
  obtain ⟨U,_hU,hrealU,_hUV,hcubic⟩ := A.exists_local_refinedCubicNormBounds hs hV hrealV
  obtain ⟨ρ,hρ,_hρU,_D,Mc,_hD,hMc,hrows⟩ := hcubic (L φ.val) (hrealU hrφ)
  obtain ⟨_Ng,_hNg,G,hG,hφG,H,hH,hgap⟩ := exists_uniform_small_sourcePeriodicGapDisplacement
    (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num) (L φ.val) (by norm_num : (0 : ℝ)<1)
  let T := (Ta∩Td)∩L ⁻¹' (ball (L φ.val) ρ∩G)
  have hT : IsOpen T := (hTa.inter hTd).inter ((isOpen_ball.inter hG).preimage L.continuous)
  have hφball : L φ.val∈ball (L φ.val) ρ := mem_ball_self hρ
  have hφT : φ.val∈T := ⟨⟨hφa,hφd⟩,hφball,hφG⟩
  let M := 12*(Ma+Md+H*(Mc/2))
  have hM : 0≤M := by dsimp only [M];positivity
  refine ⟨T,hT,hφT,(fun ψ hψ => ⟨hdD hψ.1.2,haA hψ.1.1⟩),max Ka Kd,M,hM,?_⟩
  intro ψ hψ n hn hreflect
  have hna : Ka≤(n:ℤ).natAbs := (le_max_left _ _).trans hn
  have hnd : Kd≤(n:ℤ).natAbs := (le_max_right _ _).trans hn
  let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) (n:ℤ)
  let r := Weight.sobolev (u-1) (n:ℤ)
  let w := Weight.sobolev u (n:ℤ)
  have hr : 0≤r := ((Weight.sobolev (u-1)).positive (n:ℤ)).le
  have hr1 : r≤1 := by
    simpa only [Weight.sobolev_zero_apply] using Weight.sobolev_mono (by linarith : u-1≤0) (n:ℤ)
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
  have ha' := ha ψ hψ.1.1 (n:ℤ) hna
  simp only [Int.cast_natCast] at ha'
  rw [mul_comm (Real.pi:ℂ) (n:ℂ)] at ha'
  exact NLS.ComplexAnalysis.weighted_diagonal_action_cancellation_bound w r H (Mc/2) Ma Md
    hr hr1 (div_nonneg hMc (by norm_num)) γ (n:ℂ) (Real.pi:ℂ)
    (A₀.action (n:ℤ) 1 (L ψ)) (A.moment (n:ℤ) (n:ℤ) 2 (L ψ))
    (A.moment (n:ℤ) (-(n:ℤ)) 2 (L ψ)) hγ hrw ha' (hd ψ hψ.1.2 (n:ℤ) hnd) hx

end NLS.ZakharovShabat
