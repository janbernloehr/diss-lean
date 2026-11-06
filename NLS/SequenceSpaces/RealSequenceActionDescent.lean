import NLS.SequenceSpaces.RealScalarActionFamilyDescent
import NLS.SequenceSpaces.LocallyBoundedRealization

/-! Genuine Banach sequence-valued action descent at arbitrary real
coordinate pairs. The common complex quotient chart transfers the ACTUAL
sequence norm by surjectivity, before every scalar coordinate is realized. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] [p.HolderTriple p q]

theorem exists_real_sequence_action_chart (hp : p≠⊤)
    (f : (Coeff p × Coeff p) → Coeff r) (U : Set (Coeff p × Coeff p))
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hinv : ∀ z∈U, ∀ w∈U, z∈realPairLocus p → w∈realPairLocus p →
      quadraticActionsExponent (q := q) w=quadraticActionsExponent z → f w=f z)
    (z₀ : Coeff p × Coeff p) (hz₀ : z₀∈U) (hzreal : z₀∈realPairLocus p)
    (K : ℝ) (hbound : ∀ z∈U, ‖f z‖≤K) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (Coeff q), ∃ g : Coeff q → Coeff r,
      IsOpen Z ∧ z₀∈Z ∧ Z⊆U ∧ IsOpen T ∧ quadraticActionsExponent (q := q) '' Z=T ∧
      AnalyticOnNhd ℂ g T ∧ (∀ a∈T, ‖g a‖≤K) ∧
      ∀ z∈Z, g (quadraticActionsExponent (q := q) z)=f z := by
  let F := fun (j : ℤ) z => f z j
  have hF (j : ℤ) : AnalyticOnNhd ℂ (F j) U := by
    intro z hz
    exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) r j).analyticAt _).comp (hf z hz)
  obtain ⟨Z,T,g,hZ,hzZ,hZU,hT,himage,hg,hrec⟩ :=
    exists_real_scalar_action_family_chart hp F U hU hF
      (fun j z hz w hw hzr hwr ha => congrArg (fun b : Coeff r => b j) (hinv z hz w hw hzr hwr ha))
      z₀ hz₀ hzreal
  have hrealize (a : Coeff q) (ha : a∈T) :
      ∃ b : Coeff r, (∀ j, b j=g j a) ∧ ‖b‖≤K := by
    have hi : a∈quadraticActionsExponent (q := q) '' Z := by rw [himage];exact ha
    obtain ⟨z,hz,rfl⟩ := hi
    exact ⟨f z,(fun j => (hrec j z hz).symm),hbound z (hZU hz)⟩
  obtain ⟨hval,hga⟩ := analytic_realization_of_local_bounds (r := r) (fun a j => g j a) hT hg (by
    intro a ha
    exact ⟨T,hT,ha,Subset.rfl,K,hrealize⟩)
  let G := fun a => ofFunctionOrZero r (fun j => g j a)
  refine ⟨Z,T,G,hZ,hzZ,hZU,hT,himage,hga,?_,?_⟩
  · intro a ha
    obtain ⟨b,hb,hbn⟩ := hrealize a ha
    change ‖ofFunctionOrZero r (fun j => g j a)‖≤K
    rwa [ofFunctionOrZero_eq_of_coordinates _ b hb]
  · intro z hz
    have ha : quadraticActionsExponent (q := q) z∈T := by rw [←himage];exact mem_image_of_mem _ hz
    ext j
    rw [hval _ ha j,hrec j z hz]

end NLS.Coeff
