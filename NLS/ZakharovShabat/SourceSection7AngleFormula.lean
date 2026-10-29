import NLS.ZakharovShabat.SourceAngularOriginalTheta

/-! # The literal path sum in the Section 7 angle formula

One constructed path per original gap gives all off-diagonal terms and
the diagonal eta integral. The series converges absolutely, and the full
sum agrees with the original angle modulo 2pi. The terminal root signs
are the actual anti-discriminant values, including zero values.
-/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Equation (2.3) as an absolutely convergent sum of constructed, normalized path integrals. -/
theorem section7_exists_angle_path_sum_of_circles (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (P : (m : ℤ) → SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hμ : ∀ m : ℤ, canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈
      ball ((P m).center : ℂ) (P m).radius) :
    ∃ Q : ℤ → ℂ × CoeffPair p → ℂ,
    ∃ γ : (m : ℤ) → Path
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m),
      (∀ m : ℤ,
        SourceAngularAdmissiblePathRootData hp hp1 m ψ ((P m).center : ℂ) (P m).radius (Q m) (γ m) ∧
        ContDiffOn ℝ 1 (γ m).extend (Icc 0 1) ∧
        Q m (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
          sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ∧
        CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s (Q m) (z,ψ))) (γ m)) ∧
      Summable (fun m : ℤ => ‖if m = n then 0 else sourceAngularPathIntegral n s (Q m) ψ (γ m)‖) ∧
      ∃ k : ℤ,
        (sourceAngularPathIntegral n s (Q n) ψ (γ n) +
          ∑' m : ℤ, if m = n then 0 else sourceAngularPathIntegral n s (Q m) ψ (γ m)) -
          sourceAngularOriginalTheta hp hp1 n s ψ = (k : ℂ)*(2*Real.pi) := by
  classical
  choose Q γ hQ hγ hnorm hbeta heta using
    (fun m => H.original_dirichlet_integral_path ψ hψ m (P m) (hμ m))
  have hgap' : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
    intro he
    exact hgap (by simp only [canonicalPeriodicGap,he,sub_self])
  have hterm (m : ℤ) :
      (if m = n then 0 else sourceAngularPathIntegral n s (Q m) ψ (γ m)) =
        sourceAngularBetaSeriesTerm hp hp1 n s ψ m := by
    by_cases hm : m = n
    · simp [sourceAngularBetaSeriesTerm,hm]
    · simp only [sourceAngularBetaSeriesTerm,if_neg hm]
      exact (hbeta m n hm).2
  refine ⟨Q,γ,?_,?_,?_⟩
  · intro m
    refine ⟨hQ m,hγ m,hnorm m,?_⟩
    by_cases hm : m = n
    · subst m
      exact (heta n hgap').1
    · exact (hbeta m n hm).1
  · simpa only [hterm] using H.beta_original_series.summable_norm ψ hψ n
  · simp only [hterm]
    exact H.theta_original_integral_choice_period ψ hψ n hgap
      ⟨P n,hμ n,Q n,γ n,hQ n,hγ n,(fun _ => hnorm n),
        (heta n hgap').1,(heta n hgap').2,rfl⟩

/-- The original domain supplies all circles, paths, signs and integrability in (2.3). -/
theorem section7_exists_angle_path_sum (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0) :
    ∃ P : (m : ℤ) → SourceCriticalRootPeriodCircle hp hp1 ψ m,
    ∃ Q : ℤ → ℂ × CoeffPair p → ℂ,
    ∃ γ : (m : ℤ) → Path
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m),
      (∀ m : ℤ,
        SourceAngularAdmissiblePathRootData hp hp1 m ψ ((P m).center : ℂ) (P m).radius (Q m) (γ m) ∧
        ContDiffOn ℝ 1 (γ m).extend (Icc 0 1) ∧
        Q m (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
          sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ∧
        CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s (Q m) (z,ψ))) (γ m)) ∧
      Summable (fun m : ℤ => ‖if m = n then 0 else sourceAngularPathIntegral n s (Q m) ψ (γ m)‖) ∧
      ∃ k : ℤ,
        (sourceAngularPathIntegral n s (Q n) ψ (γ n) +
          ∑' m : ℤ, if m = n then 0 else sourceAngularPathIntegral n s (Q m) ψ (γ m)) -
          sourceAngularOriginalTheta hp hp1 n s ψ = (k : ℂ)*(2*Real.pi) := by
  obtain ⟨P,hμ⟩ := H.angular_original_circles ψ hψ
  obtain ⟨Q,γ,hd,hs,hθ⟩ := H.section7_exists_angle_path_sum_of_circles ψ hψ n hgap P hμ
  exact ⟨P,Q,γ,hd,hs,hθ⟩

end SourceLemma12_12Data
end NLS.ZakharovShabat
