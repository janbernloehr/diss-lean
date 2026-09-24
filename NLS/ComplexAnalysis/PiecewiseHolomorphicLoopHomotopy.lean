import NLS.ComplexAnalysis.AffineLoopHomotopy
import NLS.ComplexAnalysis.HolomorphicCurveHomotopy

/-!
# Holomorphic homotopy of four-piece loops

A contour assembled from four smooth paths need not be smooth at its
joins. Apply the open-path homotopy identity to each moving piece and
cancel the four connecting side integrals. This gives homotopy
invariance without imposing smoothness across the corners.
-/

noncomputable section
open Set
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- Equal moving endpoints give equal integrals along the corresponding
side traces, even when the traces have differently typed endpoints. -/
private theorem curveIntegral_evalAt_eq_of_join
    {a₀ b₀ c₀ d₀ a₁ b₁ c₁ d₁ : ℂ}
    {γ₀ : Path a₀ b₀} {η₀ : Path c₀ d₀}
    {γ₁ : Path a₁ b₁} {η₁ : Path c₁ d₁}
    (f : ℂ → ℂ)
    (H : (γ₀ : C(I, ℂ)).Homotopy γ₁)
    (K : (η₀ : C(I, ℂ)).Homotopy η₁)
    (hjoin : ∀ s : I, H (s,1) = K (s,0)) :
    (∫ᶜ z in H.evalAt 1, holomorphicOneForm f z) =
      ∫ᶜ z in K.evalAt 0, holomorphicOneForm f z := by
  have h₀ : η₀ (0:I) = γ₀ 1 := by simpa using (hjoin 0).symm
  have h₁ : η₁ (0:I) = γ₁ 1 := by simpa using (hjoin 1).symm
  have hpath : (H.evalAt 1).cast h₀ h₁ = K.evalAt 0 := by
    apply Path.ext
    funext s
    exact hjoin s
  calc
    (∫ᶜ z in H.evalAt 1, holomorphicOneForm f z) =
        ∫ᶜ z in (H.evalAt 1).cast h₀ h₁, holomorphicOneForm f z := by simp
    _ = ∫ᶜ z in K.evalAt 0, holomorphicOneForm f z := by rw [hpath]

/-- The signed sum of four smooth path integrals is invariant under
piecewise smooth homotopies whose moving endpoints remain joined. -/
theorem four_piece_curveIntegral_sum_eq_of_holomorphic_homotopy
    {a₀ b₀ c₀ d₀ a₁ b₁ c₁ d₁ : ℂ}
    {γ₁₀ : Path a₀ b₀} {γ₂₀ : Path b₀ c₀}
    {γ₃₀ : Path c₀ d₀} {γ₄₀ : Path d₀ a₀}
    {γ₁₁ : Path a₁ b₁} {γ₂₁ : Path b₁ c₁}
    {γ₃₁ : Path c₁ d₁} {γ₄₁ : Path d₁ a₁}
    (f : ℂ → ℂ)
    (H₁ : (γ₁₀ : C(I, ℂ)).Homotopy γ₁₁)
    (H₂ : (γ₂₀ : C(I, ℂ)).Homotopy γ₂₁)
    (H₃ : (γ₃₀ : C(I, ℂ)).Homotopy γ₃₁)
    (H₄ : (γ₄₀ : C(I, ℂ)).Homotopy γ₄₁)
    (h₁₂ : ∀ s : I, H₁ (s,1) = H₂ (s,0))
    (h₂₃ : ∀ s : I, H₂ (s,1) = H₃ (s,0))
    (h₃₄ : ∀ s : I, H₃ (s,1) = H₄ (s,0))
    (h₄₁ : ∀ s : I, H₄ (s,1) = H₁ (s,0))
    {t : Set ℂ}
    (hH₁t : ∀ s ∈ Ioo (0:I) 1, ∀ u ∈ Ioo (0:I) 1, H₁ (s,u) ∈ t)
    (hH₂t : ∀ s ∈ Ioo (0:I) 1, ∀ u ∈ Ioo (0:I) 1, H₂ (s,u) ∈ t)
    (hH₃t : ∀ s ∈ Ioo (0:I) 1, ∀ u ∈ Ioo (0:I) 1, H₃ (s,u) ∈ t)
    (hH₄t : ∀ s ∈ Ioo (0:I) 1, ∀ u ∈ Ioo (0:I) 1, H₄ (s,u) ∈ t)
    (hf : ∀ z ∈ closure t, DifferentiableAt ℂ f z)
    (hH₁smooth : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (H₁.extend xy.1) xy.2) (Icc 0 1))
    (hH₂smooth : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (H₂.extend xy.1) xy.2) (Icc 0 1))
    (hH₃smooth : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (H₃.extend xy.1) xy.2) (Icc 0 1))
    (hH₄smooth : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (H₄.extend xy.1) xy.2) (Icc 0 1)) :
    (((∫ᶜ z in γ₁₀, holomorphicOneForm f z) +
       (∫ᶜ z in γ₂₀, holomorphicOneForm f z)) +
       (∫ᶜ z in γ₃₀, holomorphicOneForm f z)) +
       (∫ᶜ z in γ₄₀, holomorphicOneForm f z) =
    (((∫ᶜ z in γ₁₁, holomorphicOneForm f z) +
       (∫ᶜ z in γ₂₁, holomorphicOneForm f z)) +
       (∫ᶜ z in γ₃₁, holomorphicOneForm f z)) +
       (∫ᶜ z in γ₄₁, holomorphicOneForm f z) := by
  have hs₁₂ := curveIntegral_evalAt_eq_of_join f H₁ H₂ h₁₂
  have hs₂₃ := curveIntegral_evalAt_eq_of_join f H₂ H₃ h₂₃
  have hs₃₄ := curveIntegral_evalAt_eq_of_join f H₃ H₄ h₃₄
  have hs₄₁ := curveIntegral_evalAt_eq_of_join f H₄ H₁ h₄₁
  have he₁ := curveIntegral_add_sides_eq_of_holomorphic_homotopy
    f H₁ hH₁t hf hH₁smooth
  have he₂ := curveIntegral_add_sides_eq_of_holomorphic_homotopy
    f H₂ hH₂t hf hH₂smooth
  have he₃ := curveIntegral_add_sides_eq_of_holomorphic_homotopy
    f H₃ hH₃t hf hH₃smooth
  have he₄ := curveIntegral_add_sides_eq_of_holomorphic_homotopy
    f H₄ hH₄t hf hH₄smooth
  rw [hs₁₂] at he₁
  rw [hs₂₃] at he₂
  rw [hs₃₄] at he₃
  rw [hs₄₁] at he₄
  linear_combination (norm := abel) he₁ + he₂ + he₃ + he₄

/-- The same four-piece homotopy statement for the concatenated loop.
The integrability hypotheses allow the integral of each concatenation
to be split into its four path integrals. -/
theorem four_piece_curveIntegral_eq_of_holomorphic_homotopy
    {a₀ b₀ c₀ d₀ a₁ b₁ c₁ d₁ : ℂ}
    {γ₁₀ : Path a₀ b₀} {γ₂₀ : Path b₀ c₀}
    {γ₃₀ : Path c₀ d₀} {γ₄₀ : Path d₀ a₀}
    {γ₁₁ : Path a₁ b₁} {γ₂₁ : Path b₁ c₁}
    {γ₃₁ : Path c₁ d₁} {γ₄₁ : Path d₁ a₁}
    (f : ℂ → ℂ)
    (H₁ : (γ₁₀ : C(I, ℂ)).Homotopy γ₁₁)
    (H₂ : (γ₂₀ : C(I, ℂ)).Homotopy γ₂₁)
    (H₃ : (γ₃₀ : C(I, ℂ)).Homotopy γ₃₁)
    (H₄ : (γ₄₀ : C(I, ℂ)).Homotopy γ₄₁)
    (h₁₂ : ∀ s : I, H₁ (s,1) = H₂ (s,0))
    (h₂₃ : ∀ s : I, H₂ (s,1) = H₃ (s,0))
    (h₃₄ : ∀ s : I, H₃ (s,1) = H₄ (s,0))
    (h₄₁ : ∀ s : I, H₄ (s,1) = H₁ (s,0))
    {t : Set ℂ}
    (hH₁t : ∀ s ∈ Ioo (0:I) 1, ∀ u ∈ Ioo (0:I) 1, H₁ (s,u) ∈ t)
    (hH₂t : ∀ s ∈ Ioo (0:I) 1, ∀ u ∈ Ioo (0:I) 1, H₂ (s,u) ∈ t)
    (hH₃t : ∀ s ∈ Ioo (0:I) 1, ∀ u ∈ Ioo (0:I) 1, H₃ (s,u) ∈ t)
    (hH₄t : ∀ s ∈ Ioo (0:I) 1, ∀ u ∈ Ioo (0:I) 1, H₄ (s,u) ∈ t)
    (hf : ∀ z ∈ closure t, DifferentiableAt ℂ f z)
    (hH₁smooth : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (H₁.extend xy.1) xy.2) (Icc 0 1))
    (hH₂smooth : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (H₂.extend xy.1) xy.2) (Icc 0 1))
    (hH₃smooth : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (H₃.extend xy.1) xy.2) (Icc 0 1))
    (hH₄smooth : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (H₄.extend xy.1) xy.2) (Icc 0 1))
    (h₁₀int : CurveIntegrable (holomorphicOneForm f) γ₁₀)
    (h₂₀int : CurveIntegrable (holomorphicOneForm f) γ₂₀)
    (h₃₀int : CurveIntegrable (holomorphicOneForm f) γ₃₀)
    (h₄₀int : CurveIntegrable (holomorphicOneForm f) γ₄₀)
    (h₁₁int : CurveIntegrable (holomorphicOneForm f) γ₁₁)
    (h₂₁int : CurveIntegrable (holomorphicOneForm f) γ₂₁)
    (h₃₁int : CurveIntegrable (holomorphicOneForm f) γ₃₁)
    (h₄₁int : CurveIntegrable (holomorphicOneForm f) γ₄₁) :
    (∫ᶜ z in ((γ₁₀.trans γ₂₀).trans γ₃₀).trans γ₄₀,
      holomorphicOneForm f z) =
    ∫ᶜ z in ((γ₁₁.trans γ₂₁).trans γ₃₁).trans γ₄₁,
      holomorphicOneForm f z := by
  rw [curveIntegral_trans ((h₁₀int.trans h₂₀int).trans h₃₀int) h₄₀int,
    curveIntegral_trans (h₁₀int.trans h₂₀int) h₃₀int,
    curveIntegral_trans h₁₀int h₂₀int,
    curveIntegral_trans ((h₁₁int.trans h₂₁int).trans h₃₁int) h₄₁int,
    curveIntegral_trans (h₁₁int.trans h₂₁int) h₃₁int,
    curveIntegral_trans h₁₁int h₂₁int]
  exact four_piece_curveIntegral_sum_eq_of_holomorphic_homotopy
    f H₁ H₂ H₃ H₄ h₁₂ h₂₃ h₃₄ h₄₁
    hH₁t hH₂t hH₃t hH₄t hf
    hH₁smooth hH₂smooth hH₃smooth hH₄smooth

/-- Affine deformation of a four-piece loop preserves its integral
when each intermediate piece stays in a holomorphic domain. -/
theorem four_piece_curveIntegral_eq_of_affine_homotopy
    {a₀ b₀ c₀ d₀ a₁ b₁ c₁ d₁ : ℂ}
    {γ₁₀ : Path a₀ b₀} {γ₂₀ : Path b₀ c₀}
    {γ₃₀ : Path c₀ d₀} {γ₄₀ : Path d₀ a₀}
    {γ₁₁ : Path a₁ b₁} {γ₂₁ : Path b₁ c₁}
    {γ₃₁ : Path c₁ d₁} {γ₄₁ : Path d₁ a₁}
    (f : ℂ → ℂ) {t : Set ℂ}
    (havoid : ∀ (s u : I),
      (ContinuousMap.Homotopy.affine (γ₁₀ : C(I, ℂ)) (γ₁₁ : C(I, ℂ))) (s,u) ∈ t ∧
      (ContinuousMap.Homotopy.affine (γ₂₀ : C(I, ℂ)) (γ₂₁ : C(I, ℂ))) (s,u) ∈ t ∧
      (ContinuousMap.Homotopy.affine (γ₃₀ : C(I, ℂ)) (γ₃₁ : C(I, ℂ))) (s,u) ∈ t ∧
      (ContinuousMap.Homotopy.affine (γ₄₀ : C(I, ℂ)) (γ₄₁ : C(I, ℂ))) (s,u) ∈ t)
    (hf : ∀ z ∈ closure t, DifferentiableAt ℂ f z)
    (h₁₀smooth : ContDiffOn ℝ 2 γ₁₀.extend (Icc 0 1))
    (h₂₀smooth : ContDiffOn ℝ 2 γ₂₀.extend (Icc 0 1))
    (h₃₀smooth : ContDiffOn ℝ 2 γ₃₀.extend (Icc 0 1))
    (h₄₀smooth : ContDiffOn ℝ 2 γ₄₀.extend (Icc 0 1))
    (h₁₁smooth : ContDiffOn ℝ 2 γ₁₁.extend (Icc 0 1))
    (h₂₁smooth : ContDiffOn ℝ 2 γ₂₁.extend (Icc 0 1))
    (h₃₁smooth : ContDiffOn ℝ 2 γ₃₁.extend (Icc 0 1))
    (h₄₁smooth : ContDiffOn ℝ 2 γ₄₁.extend (Icc 0 1))
    (h₁₀int : CurveIntegrable (holomorphicOneForm f) γ₁₀)
    (h₂₀int : CurveIntegrable (holomorphicOneForm f) γ₂₀)
    (h₃₀int : CurveIntegrable (holomorphicOneForm f) γ₃₀)
    (h₄₀int : CurveIntegrable (holomorphicOneForm f) γ₄₀)
    (h₁₁int : CurveIntegrable (holomorphicOneForm f) γ₁₁)
    (h₂₁int : CurveIntegrable (holomorphicOneForm f) γ₂₁)
    (h₃₁int : CurveIntegrable (holomorphicOneForm f) γ₃₁)
    (h₄₁int : CurveIntegrable (holomorphicOneForm f) γ₄₁) :
    (∫ᶜ z in ((γ₁₀.trans γ₂₀).trans γ₃₀).trans γ₄₀,
      holomorphicOneForm f z) =
    ∫ᶜ z in ((γ₁₁.trans γ₂₁).trans γ₃₁).trans γ₄₁,
      holomorphicOneForm f z := by
  let H₁ := ContinuousMap.Homotopy.affine
    (γ₁₀ : C(I, ℂ)) (γ₁₁ : C(I, ℂ))
  let H₂ := ContinuousMap.Homotopy.affine
    (γ₂₀ : C(I, ℂ)) (γ₂₁ : C(I, ℂ))
  let H₃ := ContinuousMap.Homotopy.affine
    (γ₃₀ : C(I, ℂ)) (γ₃₁ : C(I, ℂ))
  let H₄ := ContinuousMap.Homotopy.affine
    (γ₄₀ : C(I, ℂ)) (γ₄₁ : C(I, ℂ))
  apply four_piece_curveIntegral_eq_of_holomorphic_homotopy
    f H₁ H₂ H₃ H₄
  · intro s
    simp [H₁, H₂, ContinuousMap.Homotopy.affine_apply]
  · intro s
    simp [H₂, H₃, ContinuousMap.Homotopy.affine_apply]
  · intro s
    simp [H₃, H₄, ContinuousMap.Homotopy.affine_apply]
  · intro s
    simp [H₄, H₁, ContinuousMap.Homotopy.affine_apply]
  · intro s _ u _
    exact (havoid s u).1
  · intro s _ u _
    exact (havoid s u).2.1
  · intro s _ u _
    exact (havoid s u).2.2.1
  · intro s _ u _
    exact (havoid s u).2.2.2
  · exact hf
  · exact affineHomotopy_contDiffOn h₁₀smooth h₁₁smooth
  · exact affineHomotopy_contDiffOn h₂₀smooth h₂₁smooth
  · exact affineHomotopy_contDiffOn h₃₀smooth h₃₁smooth
  · exact affineHomotopy_contDiffOn h₄₀smooth h₄₁smooth
  · exact h₁₀int
  · exact h₂₀int
  · exact h₃₀int
  · exact h₄₀int
  · exact h₁₁int
  · exact h₂₁int
  · exact h₃₁int
  · exact h₄₁int

end NLS.ComplexAnalysis
