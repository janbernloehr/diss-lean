import NLS.Articles.KdVKdV2Frequencies.GlobalWeakInverseSource
import NLS.SequenceSpaces.LocalScalarActionFamily
import NLS.SequenceSpaces.SignedCartesianActions

/-! Simultaneous analytic action descent of a family of genuine rough spectral invariants.
The SAME fixed weak inverse is used, including at closed actions and infinite
support, with normalized signed products calibrated by the exact Cartesian map. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- ONE source neighborhood and ONE action neighborhood precede EVERY
component of a genuine analytic rough spectral family. The SAME fixed inverse
recovers all physical real values, including closed and infinite actions. -/
theorem exists_local_weak_spectral_action_family {ι : Type*} (D : GlobalRoughAbelianForwardData)
    (δ : ℝ) (hδ : 0<δ) (F : ι → PeriodOneHminusOne → ℂ)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) (ball (0 : PeriodOneHminusOne) δ))
    (hinv : ∀ i, ∀ q∈ball (0 : PeriodOneHminusOne) δ, ∀ p∈ball (0 : PeriodOneHminusOne) δ,
      IsRealPeriodOneHminusOne q → IsRealPeriodOneHminusOne p →
      hillHminusDiscriminant p=hillHminusDiscriminant q → F i p=F i q) :
    ∃ Z : Set (Coeff 2 × Coeff 2), ∃ T : Set (Coeff 1), ∃ g : ι → Coeff 1 → ℂ,
      IsOpen Z ∧ (0 : Coeff 2 × Coeff 2)∈Z ∧ IsOpen T ∧ (0 : Coeff 1)∈T ∧
      quadraticActionsExponent (q := 1) '' Z=T ∧ (∀ i, AnalyticOnNhd ℂ (g i) T) ∧
      (∀ z∈Z, ∀ hz : z∈Coeff.realPairLocus 2,
        D.realWeakInverseSource ⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hz⟩∈ball 0 δ) ∧
      ∀ i, ∀ z∈Z, ∀ hz : z∈Coeff.realPairLocus 2,
        g i (quadraticActionsExponent (q := 1) z)=
          F i (D.realWeakInverseSource ⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hz⟩) := by
  obtain ⟨U,hU,h0U,G,hG,hG0,hmatch⟩ := D.realWeakInverseSource_has_complex_germ 0
  have h0 : G 0=0 := by simpa only [Submodule.coe_zero,D.realWeakInverseSource_zero] using hG0
  let V := (Coeff.cartesianToSigned ⁻¹' U) ∩ (G ∘ Coeff.cartesianToSigned) ⁻¹' ball 0 δ
  let f := fun i => F i ∘ G ∘ Coeff.cartesianToSigned
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
  have hf (i : ι) : AnalyticOnNhd ℂ (f i) V := by
    intro z hz
    exact (hF i _ hz.2).comp ((hG _ hz.1).comp (Coeff.cartesianToSigned.analyticAt z))
  have hI (i : ι) : ∀ z∈V, ∀ w∈V, z∈Coeff.realPairLocus 2 → w∈Coeff.realPairLocus 2 →
      (∀ j, w.1 j^2+w.2 j^2=z.1 j^2+z.2 j^2) → f i w=f i z := by
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
    change F i (G (Coeff.cartesianToSigned w))=F i (G (Coeff.cartesianToSigned z))
    rw [hb,ha]
    exact hinv i _ (by rw [←ha];exact hz.2) _ (by rw [←hb];exact hw.2)
      (D.realWeakInverseSource_real a) (D.realWeakInverseSource_real b) htrace
  have hr0 : (0 : Coeff 2 × Coeff 2)∈Coeff.realPairLocus 2 := by constructor <;> intro j <;> simp
  obtain ⟨Z,T,g,hZ,h0Z,hZV,hT,himage,hg,hrec⟩ :=
    Coeff.exists_local_scalar_action_family_of_real_invariance (p := 2) (q := 1)
      (by simp) f V hV hf hI 0 h0V hr0
  have hQ0 : quadraticActionsExponent (q := 1) (0 : Coeff 2 × Coeff 2)=(0 : Coeff 1) := by
    ext j
    simp only [quadraticActionsExponent_apply,Prod.fst_zero,Prod.snd_zero,lp.coeFn_zero,Pi.zero_apply,
      zero_pow (by decide : 2≠0),zero_add,zero_div]
  refine ⟨Z,T,g,hZ,h0Z,hT,?_,himage,hg,?_,?_⟩
  · rw [←hQ0,←himage]
    exact mem_image_of_mem _ h0Z
  · intro z hz hzr
    have he := hmatch ⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hzr⟩ (hZV hz).1
    rw [←he]
    exact (hZV hz).2
  · intro i z hz hzr
    rw [hrec i z hz]
    exact congrArg (F i) (hmatch ⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hzr⟩ (hZV hz).1)

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
