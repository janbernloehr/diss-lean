import NLS.ZakharovShabat.SourceAngularDirichletAngle

/-!
# The actual angular root on the cosine cover

The sign selected by the actual Dirichlet sine gives a literal lift
of the discriminant root. Its square is the original radicand and its
terminal value is the actual anti-discriminant, also at endpoints.
Away from sine zeros, pulling back the original psi/root differential
cancels its endpoint factor and gives the analytic cosine numerator.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The derivative factor used in the literal angular pullback is
the actual derivative of the canonical spectral cosine coordinate. -/
theorem hasDerivAt_sourceCanonicalCosinePoint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (ψ : CoeffPair p) (θ : ℂ) :
    HasDerivAt (fun e => sourceCanonicalCosinePoint hp hp1 m (e,ψ))
      (-(canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m / 2) *
        Complex.sin θ) θ := by
  simpa only [sourceCanonicalCosinePoint] using hasDerivAt_cosineGapPoint
    (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m / 2) θ

/-- The discriminant root on the cosine cover, with one fixed sheet sign. -/
def sourceAngularCosineLiftedRoot (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) (κ : ℂ) :
    ℂ × CoeffPair p → ℂ := fun x => κ *
  canonicalPeriodicGap hp hp1 (periodOnePotential x.2) (periodOnePotential_mem x.2) m *
    sourceStandardRootOmittedProduct hp hp1 m x.2 (sourceCanonicalCosinePoint hp hp1 m x) *
      Complex.sin x.1

/-- The literal pullback of the original angular differential to
the cosine cover, before cancelling its removable endpoint factors. -/
def sourceAngularCosineLiftedIntegrand (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (κ : ℂ) : ℂ × CoeffPair p → ℂ :=
  fun x => sourcePsiCandidate n (sourceCanonicalCosinePoint hp hp1 m x,(s n x.2 : Coeff p)) /
    sourceAngularCosineLiftedRoot hp hp1 m κ x *
      (-(canonicalPeriodicGap hp hp1 (periodOnePotential x.2) (periodOnePotential_mem x.2) m / 2) *
        Complex.sin x.1)

namespace SourceAngularCanonicalCosineChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {W V : Set (CoeffPair p)}
  {Ω : Set ℂ} {c : ℤ → ℂ} {R : ℤ → ℝ}

/-- Away from sine zeros the actual lifted root is nonzero, so the
uncancelled pullback is a differential on the regular covering chart. -/
theorem cosineLiftedRoot_ne_zero
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (θ : ℂ) (hθ : θ ∈ Ω)
    (κ : ℂ) (hκ : κ = 1 ∨ κ = -1) (hsin : Complex.sin θ ≠ 0) :
    sourceAngularCosineLiftedRoot hp hp1 m κ (θ,ψ) ≠ 0 := by
  have hκne : κ ≠ 0 := by rcases hκ with rfl | rfl <;> norm_num
  have hP := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ
    (sourceCanonicalCosinePoint hp hp1 m (θ,ψ)) m
    (((D.disc_family ψ hψ).contour_family.2 m).2.2.1
      (ball_subset_closedBall (D.cosine_enclosed ψ hψ θ hθ)))
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hκne (D.gap_ne_zero ψ hψ)) hP) hsin

/-- The lifted root has the original discriminant square everywhere
on the angle chart, including either singular endpoint. -/
theorem cosineLiftedRoot_sq
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (θ : ℂ) (hθ : θ ∈ Ω)
    (κ : ℂ) (hκ : κ = 1 ∨ κ = -1) :
    sourceAngularCosineLiftedRoot hp hp1 m κ (θ,ψ) ^ 2 =
      sourceAngularRadicand hp (sourceCanonicalCosinePoint hp hp1 m (θ,ψ),ψ) := by
  let z := sourceCanonicalCosinePoint hp hp1 m (θ,ψ)
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let γ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let δ := γ / 2
  let P := sourceStandardRootOmittedProduct hp hp1 m ψ z
  have hzD : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m :=
    ((D.disc_family ψ hψ).contour_family.2 m).2.2.1
      (ball_subset_closedBall (D.cosine_enclosed ψ hψ θ hθ))
  have hl : τ - δ = canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    dsimp only [τ,δ,γ,canonicalPeriodicMidpoint,canonicalPeriodicGap]
    ring
  have hr : τ + δ = canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    dsimp only [τ,δ,γ,canonicalPeriodicMidpoint,canonicalPeriodicGap]
    ring
  have hpoly : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m - z) *
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m - z) =
        -δ ^ 2 * Complex.sin θ ^ 2 := by
    rw [← hl,← hr]
    have hz : z = cosineGapPoint τ δ θ := rfl
    rw [hz]
    simpa only [neg_mul] using cosineGapPoint_endpoint_factor τ δ θ
  have hκsq : κ ^ 2 = 1 := by rcases hκ with rfl | rfl <;> norm_num
  change (κ * γ * P * Complex.sin θ) ^ 2 =
    canonicalDiscriminant hp (periodOnePotential ψ) z ^ 2 - 4
  rw [canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 _ (periodOnePotential_mem ψ) m z,
    ← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 ψ m z hzD]
  change (κ * γ * P * Complex.sin θ) ^ 2 = -4 * _ * _ * P ^ 2
  simp only [mul_pow,hκsq,one_mul]
  have hγ : γ = 2 * δ := by dsimp only [δ]; ring
  rw [hγ]
  linear_combination 4 * P ^ 2 * hpoly

/-- Both terminal equations normalize the lifted root to the actual
Dirichlet anti-discriminant, including when that value is zero. -/
theorem cosineLiftedRoot_eq_dirichlet_anti
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (θ κ : ℂ) (hκ : κ = 1 ∨ κ = -1)
    (hpoint : sourceCanonicalCosinePoint hp hp1 m (θ,ψ) = canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
    (hsin : Complex.sin θ = κ * sourceAngularDirichletSine hp hp1 m ψ) :
    sourceAngularCosineLiftedRoot hp hp1 m κ (θ,ψ) =
      sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) := by
  let γ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let P := sourceStandardRootOmittedProduct hp hp1 m ψ μ
  let w := sourceAntiDiscriminantCandidate hp hp1 ψ μ
  have hγ : γ ≠ 0 := D.gap_ne_zero ψ hψ
  have hP : P ≠ 0 := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ μ m
    (((D.disc_family ψ hψ).contour_family.2 m).2.2.1
      (ball_subset_closedBall ((D.disc_family ψ hψ).dirichlet_mem_ball m)))
  have hκsq : κ ^ 2 = 1 := by rcases hκ with rfl | rfl <;> norm_num
  simp only [sourceAngularCosineLiftedRoot,hpoint,hsin]
  change κ * γ * P * (κ * (w / (γ * P))) = w
  calc
    _ = κ ^ 2 * (γ * P) * (w / (γ * P)) := by ring
    _ = w := by rw [hκsq,one_mul,mul_div_cancel₀ _ (mul_ne_zero hγ hP)]

/-- Pulling back the original angular differential gives the regular
cosine numerator with exactly the terminal-normalized sheet coefficient.
The numerator index may equal the selected gap index. -/
theorem cosineLiftedIntegrand_eq_gapNumerator
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (θ : ℂ) (hθ : θ ∈ Ω)
    (hsin : Complex.sin θ ≠ 0) (κ : ℂ) (hκ : κ = 1 ∨ κ = -1) :
    sourceAngularCosineLiftedIntegrand hp hp1 n m s κ (θ,ψ) =
      (-κ * I) * sourceAngularGapNumerator hp hp1 n m s ψ (sourceCanonicalCosinePoint hp hp1 m (θ,ψ)) := by
  have hγ := D.gap_ne_zero ψ hψ
  have hP := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ
    (sourceCanonicalCosinePoint hp hp1 m (θ,ψ)) m
    (((D.disc_family ψ hψ).contour_family.2 m).2.2.1
      (ball_subset_closedBall (D.cosine_enclosed ψ hψ θ hθ)))
  rcases hκ with rfl | rfl <;>
    dsimp only [sourceAngularCosineLiftedIntegrand,sourceAngularCosineLiftedRoot,sourceAngularGapNumerator] <;>
    field_simp [hγ,hP,hsin,I_ne_zero]

end SourceAngularCanonicalCosineChartData
end NLS.ZakharovShabat
