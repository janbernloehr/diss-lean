import NLS.ComplexAnalysis.DenseSegmentComplement
import NLS.ComplexAnalysis.RootRatioPrimitive

/-!
# Gluing local primitives that agree on a dense set

Compatible local analytic primitives determine one analytic function on
their open domain. Matching a fixed function on a dense subset fixes all
overlaps and makes the extension unique among continuous extensions.
-/

noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis

theorem exists_primitive_of_local_dense_extensions
    (f g : ℂ → ℂ) (Ω D : Set ℂ) (hD : Dense D)
    (hlocal : ∀ z ∈ Ω, ∃ B : Set ℂ, ∃ P : ℂ → ℂ,
      IsOpen B ∧ z ∈ B ∧ B ⊆ Ω ∧ AnalyticOnNhd ℂ P B ∧
      (∀ w ∈ B, HasDerivAt P (g w) w) ∧ EqOn P f (B ∩ D)) :
    ∃ E : ℂ → ℂ, AnalyticOnNhd ℂ E Ω ∧
      (∀ z ∈ Ω, HasDerivAt E (g z) z) ∧ EqOn E f (Ω ∩ D) ∧
      ∀ B : Set ℂ, ∀ P : ℂ → ℂ, IsOpen B → B ⊆ Ω →
        ContinuousOn P B → EqOn P f (B ∩ D) → EqOn E P B := by
  classical
  choose B P hB hxB hBΩ hPa hPd hmatch using (fun x : Ω => hlocal x x.property)
  let E : ℂ → ℂ := fun z => if hz : z ∈ Ω then P ⟨z,hz⟩ z else 0
  have hE (x : Ω) : EqOn E (P x) (B x) := by
    intro z hz
    have hzΩ := hBΩ x hz
    let y : Ω := ⟨z,hzΩ⟩
    change (if h : z ∈ Ω then P ⟨z,h⟩ z else 0) = P x z
    rw [dif_pos hzΩ]
    apply continuous_eqOn_of_dense_on_open D (B x ∩ B y) hD ((hB x).inter (hB y))
      (P y) (P x) ((hPa y).continuousOn.mono inter_subset_right)
      ((hPa x).continuousOn.mono inter_subset_left) ?_ ⟨hz,hxB y⟩
    intro w hw
    exact (hmatch y ⟨hw.1.2,hw.2⟩).trans (hmatch x ⟨hw.1.1,hw.2⟩).symm
  have hEgerm (x : Ω) : E =ᶠ[𝓝 x.val] P x := by
    filter_upwards [(hB x).mem_nhds (hxB x)] with z hz
    exact hE x hz
  have hEa : AnalyticOnNhd ℂ E Ω := by
    intro z hz
    exact (hPa ⟨z,hz⟩ z (hxB ⟨z,hz⟩)).congr (hEgerm ⟨z,hz⟩).symm
  have hEf : EqOn E f (Ω ∩ D) := by
    intro z hz
    exact (hE ⟨z,hz.1⟩ (hxB ⟨z,hz.1⟩)).trans (hmatch ⟨z,hz.1⟩ ⟨hxB ⟨z,hz.1⟩,hz.2⟩)
  refine ⟨E,hEa,?_,hEf,?_⟩
  · intro z hz
    exact (hPd ⟨z,hz⟩ z (hxB ⟨z,hz⟩)).congr_of_eventuallyEq (hEgerm ⟨z,hz⟩)
  · intro V Q hV hVΩ hQ hQf
    exact continuous_eqOn_of_dense_on_open D V hD hV E Q
      (hEa.continuousOn.mono hVΩ) hQ (fun z hz =>
        (hEf ⟨hVΩ hz.1,hz.2⟩).trans (hQf hz).symm)

/-- Glue the normalized exterior primitive and all cut-interior charts
on the entire regular prescribed-sheet domain. Continuity uniquely fixes
the glued extension from its exterior values. -/
theorem exists_glued_normalized_root_primitive
    (N Q R F : ℂ → ℂ) (Ω Λ K : Set ℂ) (A : ℂ)
    (hΩ : IsOpen Ω) (hΛ : IsOpen Λ) (hK : IsClosed K) (hDense : Dense Kᶜ)
    (hQ : ContinuousOn Q (Ω \ K)) (hR : ContinuousOn R Λ)
    (hsq : ∀ z ∈ (Ω ∩ Λ) \ K, Q z^2 = R z^2)
    (hne : ∀ z ∈ Λ, R z ≠ 0)
    (hF : ∀ z ∈ Ω \ K, HasDerivAt F (N z/Q z) z)
    (hcut : ∀ z ∈ Ω ∩ Λ, z ∈ K → ∃ B : Set ℂ, ∃ P : ℂ → ℂ,
      IsOpen B ∧ z ∈ B ∧ B ⊆ Ω ∩ Λ ∧ AnalyticOnNhd ℂ P B ∧
      (∀ w ∈ B, HasDerivAt P (N w/R w) w) ∧
      EqOn P (rootRatioPrimitive Q R F A) (B \ K)) :
    ∃ E : ℂ → ℂ, AnalyticOnNhd ℂ E (Ω ∩ Λ) ∧
      (∀ z ∈ Ω ∩ Λ, HasDerivAt E (N z/R z) z) ∧
      EqOn E (rootRatioPrimitive Q R F A) ((Ω ∩ Λ) \ K) ∧
      ∀ B : Set ℂ, ∀ P : ℂ → ℂ, IsOpen B → B ⊆ Ω ∩ Λ →
        ContinuousOn P B → EqOn P (rootRatioPrimitive Q R F A) (B \ K) → EqOn E P B := by
  apply exists_primitive_of_local_dense_extensions _ _ (Ω ∩ Λ) Kᶜ hDense
  intro z hz
  by_cases hzK : z ∈ K
  · exact hcut z hz hzK
  · let D := (Ω ∩ Λ) \ K
    have hD : IsOpen D := (hΩ.inter hΛ).sdiff hK
    have hDΩ : D ⊆ Ω \ K := fun w hw => ⟨hw.1.1,hw.2⟩
    have hDR : ContinuousOn R D := hR.mono (fun w hw => hw.1.2)
    have hneD : ∀ w ∈ D, R w ≠ 0 := fun w hw => hne w hw.1.2
    have hd := rootRatioPrimitive_hasDerivAt N Q R F D A hD (hQ.mono hDΩ) hDR hsq hneD
      (fun w hw => hF w (hDΩ hw))
    have ha := rootRatioPrimitive_analyticOnNhd N Q R F D A hD (hQ.mono hDΩ) hDR hsq hneD
      (fun w hw => hF w (hDΩ hw))
    exact ⟨D,rootRatioPrimitive Q R F A,hD,⟨hz,hzK⟩,sdiff_subset,ha,hd,fun _ _ => rfl⟩

end NLS.ComplexAnalysis
