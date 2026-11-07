import NLS.ZakharovShabat.SourceCauchyFirstMomentIdentification
import NLS.ZakharovShabat.SourceHigherActionOneSobolevRatio
import NLS.ZakharovShabat.SourceNormalizedEnergyAction

/-! Quantitative inverse-index error for the SAME Cauchy energy action
ratio on a common complex first-order normalized source neighborhood. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {W : Set (CoeffPair 2)}

theorem exists_local_normalizedSobolev_energyActionRatio_decay
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (φ : realTypeSourceLocus 2)
    (hφ : normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) φ.val∈
      ball C.discs.source.val C.discs.sourceRadius) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val∈U ∧
      (∀ ψ∈U, normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ∈
        ball C.discs.source.val C.discs.sourceRadius) ∧
      ∃ N : ℕ, ∃ K : ℝ, 0≤K ∧ ∀ ψ∈U, ∀ n : ℕ+, N≤(n:ℕ) →
        let χ := normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ
        (1+(n:ℝ))*‖(2*((Real.pi:ℂ)*(n:ℕ)))*C.normalizedEnergyActionRatio (n:ℕ) χ-1‖≤K := by
  let w := SpectralWeight.sobolev 1 (by norm_num)
  let L := normalizedWeightedSourceCLM (p := 2) w
  let φu : realTypeSourceSubmodule 2 := ⟨L φ.val,normalizedWeightedSource_realType w φ.val φ.property⟩
  obtain ⟨Ni,V,hV,hφV,hVC,hi⟩ := C.exists_local_normalizedWeightedAction_one_eq_filled φu hφ
  obtain ⟨A,hA,hφA,Nd,K,hK,hd⟩ := exists_local_normalizedSobolevHigherActionOneRatio_decay φ
  refine ⟨A∩L ⁻¹' V,hA.inter (hV.preimage L.continuous),⟨hφA,hφV⟩,
    (fun ψ hψ => hVC hψ.2),max Ni Nd,K,hK,?_⟩
  intro ψ hψ n hn
  have hni : Ni≤(((n:ℕ):ℤ)).natAbs := by simpa only [Int.natAbs_natCast] using (le_max_left Ni Nd).trans hn
  have hnd : Nd≤(n:ℕ) := (le_max_right Ni Nd).trans hn
  have he := (hi (n:ℕ) hni).2 hψ.2
  dsimp only [L,w,normalizedWeightedSourceCLM_apply] at he
  have hb := hd ψ hψ.1 n hnd
  dsimp only
  rw [normalizedEnergyActionRatio,he]
  have hfactor (c F τ : ℂ) : (2*c)*(2*F/τ^2)=4*c*F/τ^2 := by ring
  rw [hfactor]
  exact hb

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
