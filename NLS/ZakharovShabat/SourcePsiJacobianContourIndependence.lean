import NLS.ZakharovShabat.SourcePsiGapLimitOperator

/-!
# Real contour independence of the actual finite psi Jacobians

Contour comparison identifies the full scalar equation formulas for
every deleted numerator root vector. Existence of a sequence-valued
realization is therefore equivalent across valid real-centered
families, including the default-zero case in the selected definition.
The selected equations agree as functions of the roots, so their
actual bounded derivatives and full block extensions agree as well.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Real-centered contour independence holds for the selected
sequence maps themselves, without supplied coordinate realizations. -/
theorem sourcePsiSelectedEquationSequence_eq_of_realCentered_families
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c₀ c₁ : ℤ → ℂ) (R₀ R₁ : ℤ → ℝ)
    (h₀ : sourcePsiRealCenteredContourFamily hp hp1 φ c₀ R₀)
    (h₁ : sourcePsiRealCenteredContourFamily hp hp1 φ c₁ R₁)
    (n : ℤ) (a : DeletedCoeff p n) :
    sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ a φ =
      sourcePsiSelectedEquationSequence hp hp1 n c₁ R₁ a φ := by
  classical
  have heq (m : ℤ) : sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) φ (c₀ m) (R₀ m) =
      sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) φ (c₁ m) (R₁ m) :=
    sourcePsiEquationCoordinate_eq_of_realCentered_enclosingCircles hp hp1 n m (a : Coeff p) φ hφ
      (c₀ m) (c₁ m) (R₀ m) (R₁ m) (h₀.1 m) (h₁.1 m)
      (h₀.2 m).1 (h₁.2 m).1 (h₀.2 m).2.1 (h₁.2 m).2.1
      (h₀.2 m).2.2.1 (h₁.2 m).2.2.1
  have hex : (∃ F : DeletedCoeff p n, ∀ m : ℤ, (F : Coeff p) m =
      sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) φ (c₀ m) (R₀ m)) ↔
      (∃ F : DeletedCoeff p n, ∀ m : ℤ, (F : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) φ (c₁ m) (R₁ m)) := by
    constructor
    · rintro ⟨F,hF⟩
      exact ⟨F,fun m => (hF m).trans (heq m)⟩
    · rintro ⟨F,hF⟩
      exact ⟨F,fun m => (hF m).trans (heq m).symm⟩
  by_cases h : ∃ F : DeletedCoeff p n, ∀ m : ℤ, (F : Coeff p) m =
      sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) φ (c₀ m) (R₀ m)
  · apply Subtype.ext
    ext m
    rw [sourcePsiSelectedEquationSequence_apply_of_exists hp hp1 n c₀ R₀ a φ h,
      sourcePsiSelectedEquationSequence_apply_of_exists hp hp1 n c₁ R₁ a φ (hex.mp h),heq]
  · have h' := fun h' => h (hex.mpr h')
    simp only [sourcePsiSelectedEquationSequence,dif_neg h,dif_neg h']

/-- At a fixed real-type source the root derivatives agree on every
valid real-centered family because their root functions agree. -/
theorem sourcePsiSelectedRootJacobian_eq_of_realCentered_families
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c₀ c₁ : ℤ → ℂ) (R₀ R₁ : ℤ → ℝ)
    (h₀ : sourcePsiRealCenteredContourFamily hp hp1 φ c₀ R₀)
    (h₁ : sourcePsiRealCenteredContourFamily hp hp1 φ c₁ R₁)
    (n : ℤ) (a : DeletedCoeff p n) :
    sourcePsiSelectedRootJacobian hp hp1 n c₀ R₀ a φ =
      sourcePsiSelectedRootJacobian hp hp1 n c₁ R₁ a φ := by
  unfold sourcePsiSelectedRootJacobian
  congr 1
  funext b
  exact sourcePsiSelectedEquationSequence_eq_of_realCentered_families
    hp hp1 φ hφ c₀ c₁ R₀ R₁ h₀ h₁ n b

theorem sourcePsiFullRootJacobian_eq_of_realCentered_families
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c₀ c₁ : ℤ → ℂ) (R₀ R₁ : ℤ → ℝ)
    (h₀ : sourcePsiRealCenteredContourFamily hp hp1 φ c₀ R₀)
    (h₁ : sourcePsiRealCenteredContourFamily hp hp1 φ c₁ R₁)
    (n : ℤ) (a : DeletedCoeff p n) :
    sourcePsiFullRootJacobian hp hp1 n c₀ R₀ a φ =
      sourcePsiFullRootJacobian hp hp1 n c₁ R₁ a φ := by
  unfold sourcePsiFullRootJacobian
  rw [sourcePsiSelectedRootJacobian_eq_of_realCentered_families
    hp hp1 φ hφ c₀ c₁ R₀ R₁ h₀ h₁]

/-- Every valid real-centered family gives the actual pointwise
operator-norm limit at each full gap-contained root vector. -/
theorem tendsto_sourcePsiFullRootJacobian_to_gapLimit_on_realCentered_family
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R)
    (a : sourcePeriodicGapRootSet hp hp1 φ) :
    Tendsto (fun n : ℤ => sourcePsiFullRootJacobian hp hp1 n c R
      (Coeff.deleteCoordinateTo n a.val) φ)
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 (sourcePsiGapLimitOperator hp hp1 φ hφ a)) := by
  obtain ⟨c',R',hfamily',hlimit,_⟩ := exists_contours_tendsto_sourcePsiGapLimitOperator hp hp1 φ hφ a
  have heq : (fun n : ℤ => sourcePsiFullRootJacobian hp hp1 n c R
      (Coeff.deleteCoordinateTo n a.val) φ) =
      (fun n : ℤ => sourcePsiFullRootJacobian hp hp1 n c' R'
        (Coeff.deleteCoordinateTo n a.val) φ) := by
    funext n
    exact sourcePsiFullRootJacobian_eq_of_realCentered_families hp hp1 φ hφ
      c c' R R' hfamily hfamily' n (Coeff.deleteCoordinateTo n a.val)
  rw [heq]
  exact hlimit

end NLS.ZakharovShabat
