import NLS.Articles.KdVKdV2Frequencies.LocalWeakSpectralActionFamily
import NLS.SequenceSpaces.LocallyBoundedRealization

/-! Sequence-valued spectral action descent for every Banach coefficient exponent through the SAME weak
inverse. Common scalar charts retain their full complex source recovery;
surjectivity of the common chart transfers the actual sequence norm bound
before all coordinates, proving Banach analyticity on ONE weak action domain. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem exists_local_sequence_weak_spectral_action_factor (D : GlobalRoughAbelianForwardData)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (δ K : ℝ) (hδ : 0<δ) (_hK : 0≤K) (F : PeriodOneHminusOne → Coeff p)
    (hF : AnalyticOnNhd ℂ F (ball (0 : PeriodOneHminusOne) δ))
    (hbound : ∀ q∈ball (0 : PeriodOneHminusOne) δ, ‖F q‖≤K)
    (hzero : ∀ q∈ball (0 : PeriodOneHminusOne) δ, ∀ j : ℤ, j≤0 → F q j=0)
    (hinv : ∀ q∈ball (0 : PeriodOneHminusOne) δ, ∀ p∈ball (0 : PeriodOneHminusOne) δ,
      IsRealPeriodOneHminusOne q → IsRealPeriodOneHminusOne p → q.val 0=0 → p.val 0=0 →
      hillHminusDiscriminant p=hillHminusDiscriminant q → F p=F q) :
    ∃ Z : Set (Coeff 2 × Coeff 2), ∃ T : Set (Coeff 1), ∃ g : Coeff 1 → Coeff p,
      IsOpen Z ∧ (0 : Coeff 2 × Coeff 2)∈Z ∧ IsOpen T ∧ (0 : Coeff 1)∈T ∧
      quadraticActionsExponent (q := 1) '' Z=T ∧ AnalyticOnNhd ℂ g T ∧
      (∀ a∈T, ‖g a‖≤K ∧ ∀ j : ℤ, j≤0 → g a j=0) ∧
      (∀ z∈Z, ∀ hz : z∈Coeff.realPairLocus 2,
        D.realWeakInverseSource ⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hz⟩∈ball 0 δ) ∧
      ∀ z∈Z, ∀ hz : z∈Coeff.realPairLocus 2,
        g (quadraticActionsExponent (q := 1) z)=
          F (D.realWeakInverseSource ⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hz⟩) := by
  obtain ⟨U,hU,h0U,G,hG,hG0,hmatch⟩ := D.realWeakInverseSource_has_complex_germ 0
  have h0 : G 0=0 := by simpa only [Submodule.coe_zero,D.realWeakInverseSource_zero] using hG0
  let V := (Coeff.cartesianToSigned ⁻¹' U) ∩ (G ∘ Coeff.cartesianToSigned) ⁻¹' ball 0 δ
  let f := fun (i : ℤ) z => F (G (Coeff.cartesianToSigned z)) i
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
  have hf (i : ℤ) : AnalyticOnNhd ℂ (f i) V := by
    intro z hz
    exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p i).analyticAt _).comp
      ((hF _ hz.2).comp ((hG _ hz.1).comp (Coeff.cartesianToSigned.analyticAt z)))
  have hI (i : ℤ) : ∀ z∈V, ∀ w∈V, z∈Coeff.realPairLocus 2 → w∈Coeff.realPairLocus 2 →
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
    change F (G (Coeff.cartesianToSigned w)) i=F (G (Coeff.cartesianToSigned z)) i
    rw [hb,ha]
    exact congrArg (fun x : Coeff p => x i)
      (hinv _ (by rw [←ha];exact hz.2) _ (by rw [←hb];exact hw.2)
        (D.realWeakInverseSource_real a) (D.realWeakInverseSource_real b)
        (D.realWeakInverseSource_zero_mode a) (D.realWeakInverseSource_zero_mode b) htrace)
  have hr0 : (0 : Coeff 2 × Coeff 2)∈Coeff.realPairLocus 2 := by constructor <;> intro j <;> simp
  obtain ⟨Z,T,g,hZ,h0Z,hZV,hT,himage,hg,hrec⟩ :=
    Coeff.exists_local_scalar_action_family_of_real_invariance (p := 2) (q := 1)
      (by simp) f V hV hf hI 0 h0V hr0
  have hQ0 : quadraticActionsExponent (q := 1) (0 : Coeff 2 × Coeff 2)=(0 : Coeff 1) := by
    ext j
    simp only [quadraticActionsExponent_apply,Prod.fst_zero,Prod.snd_zero,lp.coeFn_zero,Pi.zero_apply,
      zero_pow (by decide : 2≠0),zero_add,zero_div]
  have hrealize (a : Coeff 1) (ha : a∈T) :
      ∃ b : Coeff p, (∀ j, b j=g j a) ∧ ‖b‖≤K := by
    have hi : a∈quadraticActionsExponent (q := 1) '' Z := by rw [himage];exact ha
    obtain ⟨z,hz,rfl⟩ := hi
    refine ⟨F (G (Coeff.cartesianToSigned z)),?_,hbound _ (hZV hz).2⟩
    intro j
    exact (hrec j z hz).symm
  obtain ⟨_hgcoord,hga⟩ := Coeff.analytic_realization_of_local_bounds (r := p)
    (fun a j => g j a) hT (fun j => hg j) (by
      intro a ha
      exact ⟨T,hT,ha,Subset.rfl,K,hrealize⟩)
  let result := fun a => Coeff.ofFunctionOrZero p (fun j => g j a)
  have hgval (a : Coeff 1) (ha : a∈T) : ‖result a‖≤K ∧ ∀ j, result a j=g j a := by
    obtain ⟨b,hb,hbn⟩ := hrealize a ha
    change ‖Coeff.ofFunctionOrZero p (fun j => g j a)‖≤K ∧
      ∀ j, Coeff.ofFunctionOrZero p (fun j => g j a) j=g j a
    rw [Coeff.ofFunctionOrZero_eq_of_coordinates _ b hb]
    exact ⟨hbn,hb⟩
  refine ⟨Z,T,result,hZ,h0Z,hT,?_,himage,hga,?_,?_,?_⟩
  · rw [←hQ0,←himage]
    exact mem_image_of_mem _ h0Z
  · intro a ha
    refine ⟨(hgval a ha).1,?_⟩
    intro j hj
    rw [(hgval a ha).2 j]
    have hi : a∈quadraticActionsExponent (q := 1) '' Z := by rw [himage];exact ha
    obtain ⟨z,hz,rfl⟩ := hi
    rw [hrec j z hz]
    exact hzero _ (hZV hz).2 j hj
  · intro z hz hzr
    have he := hmatch ⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hzr⟩ (hZV hz).1
    rw [←he]
    exact (hZV hz).2
  · intro z hz hzr
    have ha : quadraticActionsExponent (q := 1) z∈T := by rw [←himage];exact mem_image_of_mem _ hz
    ext j
    rw [(hgval _ ha).2 j,hrec j z hz]
    exact congrArg (fun q => F q j)
      (hmatch ⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hzr⟩ (hZV hz).1)

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
