import NLS.ComplexAnalysis.ParametricCosineChart

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem exists_local_parametricCosine_chart_on_real_segment
    (τ δ : A → ℂ) (O : Set A) (hO : IsOpen O)
    (hτ : AnalyticOnNhd ℂ τ O) (hδ : AnalyticOnNhd ℂ δ O)
    (D : Set (ℂ × A)) (hD : IsOpen D) (a : A) (ha : a ∈ O) (l r : ℝ)
    (hgap : ∀ z ∈ segment ℝ (τ a-δ a) (τ a+δ a), (z,a) ∈ D) :
    ∃ V : Set A, ∃ Ω : Set ℂ, IsOpen V ∧ a ∈ V ∧ V ⊆ O ∧
      IsOpen Ω ∧ Convex ℝ Ω ∧ segment ℝ (l:ℂ) (r:ℂ) ⊆ Ω ∧
      ∀ b ∈ V, ∀ θ ∈ Ω, (cosineGapPoint (τ b) (δ b) θ,b) ∈ D := by
  let T : ℂ × A → ℂ × A := fun x => (cosineGapPoint (τ x.2) (δ x.2) x.1,x.2)
  let E : Set (ℂ × A) := {x | x.2 ∈ O ∧ T x ∈ D}
  have hE : IsOpen E := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have ht := (hτ x.2 hx.1).comp (f := fun x : ℂ × A => x.2) analyticAt_snd
    have hd := (hδ x.2 hx.1).comp (f := fun x : ℂ × A => x.2) analyticAt_snd
    have hTa : AnalyticAt ℂ T x :=
      (ht.add (hd.mul (Complex.analyticAt_cos.comp (f := fun x : ℂ × A => x.1)
        analyticAt_fst))).prod analyticAt_snd
    exact inter_mem ((hO.preimage continuous_snd).mem_nhds hx.1)
      (hTa.continuousAt.preimage_mem_nhds (hD.mem_nhds hx.2))
  let K := segment ℝ (l:ℂ) (r:ℂ)
  have hK : IsCompact K := by
    change IsCompact (segment ℝ (l:ℂ) (r:ℂ))
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hKE : K ×ˢ {a} ⊆ E := by
    rintro ⟨θ,b⟩ ⟨hθ,hb⟩
    have : b = a := hb
    subst b
    have hi : θ.im = 0 := by
      have hθseg : θ ∈ segment ℝ (l:ℂ) (r:ℂ) := hθ
      obtain ⟨t,ht,he⟩ := by rw [segment_eq_image_lineMap] at hθseg; exact hθseg
      rw [← he]
      simp [AffineMap.lineMap_apply_module,Complex.real_smul]
    have hθreal : θ = (θ.re : ℂ) := by apply Complex.ext <;> simp [hi]
    refine ⟨ha,?_⟩
    change (cosineGapPoint (τ a) (δ a) θ,a) ∈ D
    rw [hθreal]
    exact hgap _ (cosineGapPoint_real_mem_segment (τ a) (δ a) θ.re)
  obtain ⟨U,V,hU,hV,hKU,haV,hUV⟩ := generalized_tube_lemma hK isCompact_singleton hE hKE
  obtain ⟨Ω,hΩ,hconv,hKΩ,hΩU⟩ := exists_convex_open_neighborhood_of_segment
    (l:ℂ) (r:ℂ) U hU hKU
  have hlΩ : (l:ℂ) ∈ Ω := hKΩ (left_mem_segment ℝ _ _)
  have hVO : V ⊆ O := by
    intro b hb
    have hm : ((l:ℂ),b) ∈ U ×ˢ V := ⟨hΩU hlΩ,hb⟩
    exact (hUV hm).1
  refine ⟨V,Ω,hV,haV (mem_singleton a),hVO,hΩ,hconv,hKΩ,?_⟩
  intro b hb θ hθ
  have hm : (θ,b) ∈ U ×ˢ V := ⟨hΩU hθ,hb⟩
  exact (hUV hm).2

end NLS.ComplexAnalysis
