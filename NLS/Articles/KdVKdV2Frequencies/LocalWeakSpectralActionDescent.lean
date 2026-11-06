import NLS.Articles.KdVKdV2Frequencies.GlobalWeakInverseSource
import NLS.SequenceSpaces.ScalarActionDescentFromRealGerms
import NLS.SequenceSpaces.SignedCartesianActions

/-! Local analytic action descent of genuine rough spectral invariants.
The SAME fixed weak inverse is used, including at closed actions and infinite
support, with normalized signed products calibrated by the exact Cartesian map. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- A genuine analytic rough spectral invariant descends analytically through
the actual weak signed products near zero, including all closed tail actions.
The original fixed global inverse supplies every physical real source value. -/
theorem exists_local_weak_spectral_action_factor (D : GlobalRoughAbelianForwardData)
    (δ : ℝ) (hδ : 0<δ) (F : PeriodOneHminusOne → ℂ)
    (hF : AnalyticOnNhd ℂ F (ball (0 : PeriodOneHminusOne) δ))
    (hinv : ∀ q∈ball (0 : PeriodOneHminusOne) δ, ∀ p∈ball (0 : PeriodOneHminusOne) δ,
      IsRealPeriodOneHminusOne q → IsRealPeriodOneHminusOne p →
      hillHminusDiscriminant p=hillHminusDiscriminant q → F p=F q) :
    ∃ Z : Set (Coeff 2 × Coeff 2), ∃ T : Set (Coeff 1), ∃ g : Coeff 1 → ℂ,
      IsOpen Z ∧ (0 : Coeff 2 × Coeff 2)∈Z ∧ IsOpen T ∧ (0 : Coeff 1)∈T ∧
      quadraticActionsExponent (q := 1) '' Z=T ∧ AnalyticOnNhd ℂ g T ∧
      ∀ z∈Z, ∀ hz : z∈Coeff.realPairLocus 2,
        D.realWeakInverseSource ⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hz⟩∈ball 0 δ ∧
        g (quadraticActionsExponent (q := 1) z)=
          F (D.realWeakInverseSource ⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hz⟩) := by
  obtain ⟨U,hU,h0U,G,hG,hG0,hmatch⟩ := D.realWeakInverseSource_has_complex_germ 0
  have h0 : G 0=0 := by simpa only [Submodule.coe_zero,D.realWeakInverseSource_zero] using hG0
  let V := (Coeff.cartesianToSigned ⁻¹' U) ∩ (G ∘ Coeff.cartesianToSigned) ⁻¹' ball 0 δ
  let f := F ∘ G ∘ Coeff.cartesianToSigned
  have hcont : ContinuousOn (G ∘ Coeff.cartesianToSigned) (Coeff.cartesianToSigned ⁻¹' U) :=
    hG.continuousOn.comp Coeff.cartesianToSigned.continuous.continuousOn (fun _ hz => hz)
  have hV : IsOpen V := hcont.isOpen_inter_preimage (hU.preimage Coeff.cartesianToSigned.continuous) isOpen_ball
  have h0V : (0 : Coeff 2 × Coeff 2)∈V := by
    constructor
    · change Coeff.cartesianToSigned 0∈U
      simpa only [map_zero,Submodule.coe_zero] using h0U
    · change G (Coeff.cartesianToSigned 0)∈ball 0 δ
      rw [map_zero,h0]
      exact mem_ball_self hδ
  have hf : AnalyticOnNhd ℂ f V := by
    intro z hz
    exact (hF _ hz.2).comp ((hG _ hz.1).comp (Coeff.cartesianToSigned.analyticAt z))
  have hI : ∀ z∈V, ∀ w∈V, z∈Coeff.realPairLocus 2 → w∈Coeff.realPairLocus 2 →
      (∀ j, w.1 j^2+w.2 j^2=z.1 j^2+z.2 j^2) → f w=f z := by
    intro z hz w hw hzr hwr he
    let a : physicalRealDeletedSubmodule := ⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hzr⟩
    let b : physicalRealDeletedSubmodule := ⟨Coeff.cartesianToSigned w,Coeff.cartesianToSigned_real w hwr⟩
    have ha := hmatch a hz.1
    have hb := hmatch b hw.1
    have htrace : hillHminusDiscriminant (D.realWeakInverseSource b)=
        hillHminusDiscriminant (D.realWeakInverseSource a) := by
      apply D.realWeakInverseSource_discriminant_eq_of_products
      intro n
      change (Coeff.cartesianToSigned w).val (n : ℤ)*(Coeff.cartesianToSigned w).val (-(n : ℤ))=
        (Coeff.cartesianToSigned z).val (n : ℤ)*(Coeff.cartesianToSigned z).val (-(n : ℤ))
      rw [Coeff.cartesianToSigned_product w (n : ℤ) (by exact_mod_cast n.pos),
        Coeff.cartesianToSigned_product z (n : ℤ) (by exact_mod_cast n.pos),quadraticActionsExponent_apply,
        quadraticActionsExponent_apply,he]
    change F (G (Coeff.cartesianToSigned w))=F (G (Coeff.cartesianToSigned z))
    rw [hb,ha]
    exact hinv _ (by rw [←ha];exact hz.2) _ (by rw [←hb];exact hw.2)
      (D.realWeakInverseSource_real a) (D.realWeakInverseSource_real b) htrace
  have hr0 : (0 : Coeff 2 × Coeff 2)∈Coeff.realPairLocus 2 := by constructor <;> intro j <;> simp
  obtain ⟨Z,T,g,hZ,h0Z,hZV,hT,himage,hg,hrec⟩ :=
    Coeff.exists_local_scalar_action_factor_of_real_invariance (p := 2) (q := 1)
      (by simp) f V hV hf hI 0 h0V hr0
  have hQ0 : quadraticActionsExponent (q := 1) (0 : Coeff 2 × Coeff 2)=(0 : Coeff 1) := by
    ext j
    simp only [quadraticActionsExponent_apply,Prod.fst_zero,Prod.snd_zero,lp.coeFn_zero,Pi.zero_apply,
      zero_pow (by decide : 2≠0),zero_add,zero_div]
  refine ⟨Z,T,g,hZ,h0Z,hT,?_,himage,hg,?_⟩
  · rw [←hQ0,←himage]
    exact mem_image_of_mem _ h0Z
  · intro z hz hzr
    have he := hmatch ⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hzr⟩ (hZV hz).1
    refine ⟨?_,?_⟩
    · rw [←he]
      exact (hZV hz).2
    · rw [hrec z hz]
      exact congrArg F he

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
