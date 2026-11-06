import NLS.KdV.HillHminusEndpointCartesianCommutation
import NLS.KdV.HillHminusConjugateCartesianGerms

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

theorem hillSpectralCartesian_mul_conj (q : RealPeriodOneHillPotential) (n : ℕ+) :
    hillSpectralCartesian q.val q.property.1 q.property.2 n n.pos *
      conj (hillSpectralCartesian q.val q.property.1 q.property.2 n n.pos) =
        2 * (hillRealGapIntegral q.val q.property.1 q.property.2 n 0 : ℂ) := by
  have hi := hillSpectralCartesian_action_identity (by simp) (by simp [IsRealHillPotential])
    q.val q.property.1 q.property.2 n n.pos
  apply Complex.ext
  · simpa only [mul_re,conj_re,conj_im,mul_neg,sub_neg_eq_add,ofReal_re,ofReal_im,
      mul_zero,sub_zero,show (2:ℂ).re=2 from rfl,show (2:ℂ).im=0 from rfl,←sq,
      zero_pow (by decide : (2:ℕ)≠0),sub_zero] using hi
  · simp only [mul_im,conj_re,conj_im,ofReal_im,show (2:ℂ).im=0 from rfl,
      show (2:ℂ).re=2 from rfl,zero_mul,mul_zero,add_zero]
    ring

theorem hillSpectralCartesian_ne_zero_open (q : RealPeriodOneHillPotential) (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) :
    hillSpectralCartesian q.val q.property.1 q.property.2 n n.pos ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_hillSpectralCartesian (by simp) (by simp [IsRealHillPotential])]
  exact Real.sqrt_pos.mpr (mul_pos (by norm_num) (hillRealGapIntegral_pos_of_open q n hgap))

/-- The genuine mixed Cartesian bracket at an all-periodic source has
its EXACT positive 2*i normalization for the ORIGINAL complex coordinate. -/
theorem hillOriginalCartesian_conjugate_hminus_Gardner_endpoint_eq
    (q : RealPeriodOneHillPotential) (n m : ℕ+)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0)
    (hterminal : ∀ k : ℕ, ∀ hk : 1 ≤ k,
      hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk = 0)
    (Z C : PeriodOneHminusOne → ℂ)
    (hZ : AnalyticAt ℂ Z (hillOriginalHminusSource q.val))
    (hC : AnalyticAt ℂ C (hillOriginalHminusSource q.val))
    (hZM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      Z (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos)
    (hCM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      C (hillOriginalHminusSource p.val) = conj (hillSpectralCartesian p.val p.property.1 p.property.2 m m.pos)) :
    NLS.Poisson.hminusGardnerBracket Z C (hillOriginalHminusSource q.val) =
      2 * I * (if (n:ℕ)=(m:ℕ) then 1 else 0 : ℂ) := by
  obtain ⟨J,A,hJ,_,hJM,_,_,_⟩ :=
    exists_hillOriginal_action_amplitude_hminus_differentials q m hgapm
  obtain ⟨ε,hε,W,hWball,hWMball⟩ :=
    exists_hillOriginal_cartesian_hminus_isospectral_physical_germs q m hgapm
  have hW := hWball _ (Metric.mem_ball_self hε)
  obtain ⟨V,hV,hqV,hWV⟩ := hWMball q (Metric.mem_ball_self hε) (fun _ => rfl)
  have hWM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      W (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 m m.pos :=
    Filter.Eventually.mono (hV.mem_nhds hqV) (fun p hp => hWV p hp)
  have hprod : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      W (hillOriginalHminusSource p.val) * C (hillOriginalHminusSource p.val) =
        2 * J (hillOriginalHminusSource p.val) := by
    filter_upwards [hWM,hCM,hJM] with p hw hc hj
    rw [hw,hc,hj]
    exact hillSpectralCartesian_mul_conj p m
  have hd := hillHminusPhysicalGerm_fderiv_eq_of_eventuallyEq q
    (fun a => W a * C a) (fun a => 2 * J a) (hW.mul hC) (analyticAt_const.mul hJ) hprod
  have hd2 : fderiv ℂ (fun a => W a * C a) (hillOriginalHminusSource q.val) =
      (2:ℂ) • fderiv ℂ J (hillOriginalHminusSource q.val) := by
    rw [hd]
    exact (hJ.differentiableAt.hasFDerivAt.const_mul 2).fderiv
  have hb := NLS.Poisson.hminusGardnerBracket_mul_right Z W C (hillOriginalHminusSource q.val)
    hW.differentiableAt hC.differentiableAt
  rw [hillOriginalCartesians_hminus_Gardner_endpoint_zero q n m hgapn hgapm hterminal
    Z W hZ hW hZM hWM,mul_zero,add_zero] at hb
  have hs := NLS.Poisson.hminusGardnerBracket_of_fderiv_smul_right Z
    (fun a => W a * C a) J (hillOriginalHminusSource q.val) 2 hd2
  have he : W (hillOriginalHminusSource q.val) *
      NLS.Poisson.hminusGardnerBracket Z C (hillOriginalHminusSource q.val) =
        2 * (I * (if (m:ℕ)=(n:ℕ) then 1 else 0 : ℂ) *
          hillSpectralCartesian q.val q.property.1 q.property.2 n n.pos) := by
    rw [←hb,hs,hillOriginalCartesian_action_hminus_Gardner_eq q n m Z J hZ hJ hZM hJM]
  have hWn : W (hillOriginalHminusSource q.val) ≠ 0 := by
    rw [hWM.self_of_nhds]
    exact hillSpectralCartesian_ne_zero_open q m hgapm
  by_cases hnm : (n:ℕ)=(m:ℕ)
  · have heq : n=m := Subtype.ext hnm
    subst m
    rw [if_pos rfl,mul_one] at he ⊢
    apply mul_left_cancel₀ hWn
    rw [he,hWM.self_of_nhds]
    ring
  · rw [if_neg (Ne.symm hnm),mul_zero,zero_mul,mul_zero] at he
    have hz := (mul_eq_zero.mp he).resolve_left hWn
    simpa only [if_neg hnm,mul_zero] using hz

end NLS.KdV
