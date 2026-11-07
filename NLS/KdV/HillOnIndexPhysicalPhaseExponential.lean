import NLS.KdV.HillOnIndexPhysicalPhaseCharts
import NLS.KdV.HillHminusOneCanonicalGapSquares
import NLS.KdV.HillAbelianPhysicalEnergyPullback

/-! Exact phase-exponential formulas at the ACTUAL physical divisor.
Multiplication by the ORIGINAL energy gap gives analytic local
Cartesian factors without gap division, including complex collapse.
Their product is the ACTUAL canonical Hill gap square. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem onIndexAbelianCosinePhase_at_physical_terminal (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (δ θ : ℂ)
    (hpoint : cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ θ =
      P.physicalDirichletFrequency ((n:ℕ):ℤ) q)
    (hroot : -I*δ*Complex.sin θ = P.physicalDirichletRootCoefficient n q) :
    P.onIndexAbelianCosinePhase n q δ θ = θ-(Real.pi:ℂ)+P.physicalOnIndexAbelianCorrection n q := by
  unfold onIndexAbelianCosinePhase quadraticCosinePrimitive physicalOnIndexAbelianCorrection
  rw [hpoint,hroot]

theorem physicalOnIndexCartesianPlus_eq_gap_mul_phase_exp (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (δ θ : ℂ)
    (hpoint : cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ θ =
      P.physicalDirichletFrequency ((n:ℕ):ℤ) q)
    (hroot : -I*δ*Complex.sin θ = P.physicalDirichletRootCoefficient n q) :
    P.physicalOnIndexCartesianPlus n q =
      (4*sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)*δ)*
        Complex.exp (I*P.onIndexAbelianCosinePhase n q δ θ) := by
  rw [P.onIndexAbelianCosinePhase_at_physical_terminal n q δ θ hpoint hroot]
  have he : Complex.exp (I*(θ-(Real.pi:ℂ)+P.physicalOnIndexAbelianCorrection n q)) =
      -(Complex.cos θ+Complex.sin θ*I)*Complex.exp (I*P.physicalOnIndexAbelianCorrection n q) := by
    rw [show I*(θ-(Real.pi:ℂ)+P.physicalOnIndexAbelianCorrection n q) =
      θ*I-(Real.pi:ℂ)*I+I*P.physicalOnIndexAbelianCorrection n q by ring,
      Complex.exp_add,Complex.exp_sub,Complex.exp_mul_I,Complex.exp_pi_mul_I]
    ring
  rw [he]
  unfold physicalOnIndexCartesianPlus
  rw [← hpoint,← hroot]
  unfold cosineGapPoint
  ring

theorem physicalOnIndexCartesianMinus_eq_gap_mul_phase_exp (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (δ θ : ℂ)
    (hpoint : cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ θ =
      P.physicalDirichletFrequency ((n:ℕ):ℤ) q)
    (hroot : -I*δ*Complex.sin θ = P.physicalDirichletRootCoefficient n q) :
    P.physicalOnIndexCartesianMinus n q =
      (4*sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)*δ)*
        Complex.exp (-I*P.onIndexAbelianCosinePhase n q δ θ) := by
  rw [P.onIndexAbelianCosinePhase_at_physical_terminal n q δ θ hpoint hroot]
  have he : Complex.exp (-I*(θ-(Real.pi:ℂ)+P.physicalOnIndexAbelianCorrection n q)) =
      -(Complex.cos θ-Complex.sin θ*I)*Complex.exp (-I*P.physicalOnIndexAbelianCorrection n q) := by
    rw [show -I*(θ-(Real.pi:ℂ)+P.physicalOnIndexAbelianCorrection n q) =
      ((-θ)*I+(Real.pi:ℂ)*I)+ -I*P.physicalOnIndexAbelianCorrection n q by ring,
      Complex.exp_add,Complex.exp_add,Complex.exp_mul_I,Complex.exp_pi_mul_I,Complex.cos_neg,Complex.sin_neg]
    ring
  rw [he]
  unfold physicalOnIndexCartesianMinus
  rw [← hpoint,← hroot]
  unfold cosineGapPoint
  ring

theorem physicalOnIndexCartesian_product_eq_original_gap_square (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    P.physicalOnIndexCartesianPlus n q*P.physicalOnIndexCartesianMinus n q = hillHminusCanonicalGapSquare n q := by
  rw [P.physicalOnIndexCartesian_product n q hq,
    P.parent.parent.miuraBall.canonical_gapSquare_eq n q (P.parent.subset (P.subset hq.1)).1]
  unfold HillHminusMiuraGapBall.gapSquare HillHminusMiuraGapBall.diracSum
  dsimp only [sourcePsi]
  ring

theorem onIndexCosine_full_root_square (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (δ θ : ℂ)
    (hδ : δ^2 = (canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2/4)
    (hθ : cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ θ ∈ ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ))) :
    let z := cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ θ
    (P.abelianGapRootMultiplier n (z,q)*(-I*δ*Complex.sin θ))^2 =
      hillHminusRadicand q (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ)) := by
  dsimp only
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)
  have hs : (-I*δ*Complex.sin θ)^2 = sourceAngularSelectedPolynomial (by norm_num) (by norm_num)
      (P.sourcePsi q) ((n:ℕ):ℤ) (cosineGapPoint τ δ θ) := by
    unfold sourceAngularSelectedPolynomial quadraticRootPolynomial
    rw [← hδ]
    dsimp only [cosineGapPoint,τ]
    rw [mul_pow,mul_pow,neg_sq,I_sq]
    linear_combination -δ^2*(Complex.sin_sq_add_cos_sq θ)
  rw [mul_pow,hs]
  exact P.abelianGapRootMultiplier_sq_mul_polynomial n _ ⟨hθ,hq⟩

theorem onIndexCosine_regular_Hill_pullback (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (δ θ : ℂ)
    (hδ : δ^2 = (canonicalPeriodicGap (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2/4)
    (hθ : cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ θ ∈ ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)))
    (hr : -I*δ*Complex.sin θ ≠ 0) :
    let z := cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ θ
    HasDerivAt (P.onIndexAbelianCosinePhase n q δ)
      ((2*z*hillHminusCanonicalPsi n (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q)/
        (P.abelianGapRootMultiplier n (z,q)*(-I*δ*Complex.sin θ)))*(-δ*Complex.sin θ)) θ := by
  dsimp only
  have hd := P.hasDerivAt_onIndexAbelianCosinePhase n q hq δ θ hδ hθ
  have hK := P.abelianGapRootMultiplier_ne_zero n
    (cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ θ,q) ⟨hθ,hq⟩
  let z := cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ θ
  let A := 2*z*hillHminusCanonicalPsi n (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q)
  let K := P.abelianGapRootMultiplier n (z,q)
  let R := -I*δ*Complex.sin θ
  have hjac : -δ*Complex.sin θ = (-I)*R := by
    dsimp only [R]
    have he : (-I)*(-I*δ*Complex.sin θ) = I^2*(δ*Complex.sin θ) := by ring
    rw [he,I_sq]
    ring
  have halgebra (a k r : ℂ) (hk : k ≠ 0) (hr' : r ≠ 0) :
      (a/(k*r))*((-I)*r) = -I*(a/k) := by field_simp [hk,hr']
  convert hd using 1
  change (A/(K*R))*(-δ*Complex.sin θ) = -I*(A/K)
  rw [hjac]
  exact halgebra A K R hK hr

theorem onIndexAbelianCosinePhase_mod_pi_of_physical_terminals (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (δ σ θ η : ℂ) (hδ : δ ≠ 0) (hsq : δ^2 = σ^2)
    (hθ : cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ θ = P.physicalDirichletFrequency ((n:ℕ):ℤ) q)
    (hη : cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) σ η = P.physicalDirichletFrequency ((n:ℕ):ℤ) q)
    (hrθ : -I*δ*Complex.sin θ = P.physicalDirichletRootCoefficient n q)
    (hrη : -I*σ*Complex.sin η = P.physicalDirichletRootCoefficient n q) :
    ∃ k : ℤ, P.onIndexAbelianCosinePhase n q δ θ-P.onIndexAbelianCosinePhase n q σ η = (k:ℂ)*(Real.pi:ℂ) := by
  have hcos : δ*Complex.cos θ = σ*Complex.cos η := by
    dsimp only [cosineGapPoint] at hθ hη
    linear_combination hθ-hη
  have hsin : δ*Complex.sin θ = σ*Complex.sin η := by
    apply mul_left_cancel₀ (neg_ne_zero.mpr I_ne_zero)
    linear_combination hrθ-hrη
  have hσ : σ ≠ 0 := by intro he; rw [he,zero_pow (by norm_num : 2 ≠ 0)] at hsq; exact hδ (eq_zero_of_pow_eq_zero hsq)
  have hangle : ∃ k : ℤ, θ-η = (k:ℂ)*(Real.pi:ℂ) := by
    rcases eq_or_eq_neg_of_sq_eq_sq δ σ hsq with h | h
    · rw [h] at hcos hsin
      exact angle_sub_eq_int_pi_of_coordinates_up_to_sign θ η 1 (Or.inl rfl)
        (by simpa only [one_mul] using mul_left_cancel₀ hσ hsin)
        (by simpa only [one_mul] using mul_left_cancel₀ hσ hcos)
    · rw [h] at hcos hsin
      apply angle_sub_eq_int_pi_of_coordinates_up_to_sign θ η (-1) (Or.inr rfl)
      · apply mul_left_cancel₀ hσ
        linear_combination -hsin
      · apply mul_left_cancel₀ hσ
        linear_combination -hcos
  obtain ⟨k,hk⟩ := hangle
  refine ⟨k,?_⟩
  rw [P.onIndexAbelianCosinePhase_at_physical_terminal n q δ θ hθ hrθ,
    P.onIndexAbelianCosinePhase_at_physical_terminal n q σ η hη hrη]
  linear_combination hk

theorem original_energy_gap_eq_four_midpoint_halfgap_of_real (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    4*sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)*
      sourceStandardRootHalfGap (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ) =
        ((hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1):ℝ):ℂ) := by
  have he := P.abelian_gap_endpoint_energies_eq_original_labels n q hq hr
  rw [ofReal_sub,← he.2,← he.1]
  unfold sourceStandardRootMidpoint sourceStandardRootHalfGap canonicalPeriodicMidpoint canonicalPeriodicGap
  ring

end NLS.KdV.HillProductEquationPatch
