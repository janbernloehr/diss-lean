import NLS.ZakharovShabat.SourceAngularBetaRegularAnalytic

/-!
# Endpoint normalization and the actual Dirichlet sine coordinate

The actual off-diagonal cosine primitive vanishes at both endpoint angles.
The normalized Dirichlet anti-discriminant is analytic through a zero at
an endpoint of an open gap. Its square and the normalized terminal cosine
satisfy the exact trigonometric identity used to construct endpoint angles.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Dirichlet sine normalized by the actual gap and omitted product. -/
def sourceAngularDirichletSine (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) : CoeffPair p → ℂ :=
  fun ψ => sourceAntiDiscriminantCandidate hp hp1 ψ
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) /
    (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m *
      sourceStandardRootOmittedProduct hp hp1 m ψ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))

namespace SourceAngularCanonicalCosineChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {W V : Set (CoeffPair p)}
  {Ω : Set ℂ} {c : ℤ → ℂ} {R : ℤ → ℝ}

/-- Zero off-diagonal periods force the actual joint cosine primitive
to vanish at the right endpoint angle as well as its left anchor pi. -/
theorem primitive_zero
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (hmn : m ≠ n) :
    sourceAngularCanonicalCosinePrimitive hp hp1 n m s (0,ψ) = 0 := by
  let H : ℂ → ℂ := fun e => sourceAngularCanonicalCosinePrimitive hp hp1 n m s (e,ψ)
  let T : ℂ → ℂ := fun e => sourceCanonicalCosinePoint hp hp1 m (e,ψ)
  have h0Ω : (0:ℂ) ∈ Ω := D.angle_segment (left_mem_segment ℝ _ _)
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp D.angle_open 0 h0Ω
  have hsum (e : ℂ) (he : e ∈ ball (0:ℂ) ρ) :
      HasDerivAt (fun t => H t+H (-t)) 0 e := by
    have hnegball : -e ∈ ball (0:ℂ) ρ := by simpa only [mem_ball,dist_zero_right,norm_neg] using he
    have hderiv := (D.primitive_derivative n ψ hψ e (hball he)).add
      ((D.primitive_derivative n ψ hψ (-e) (hball hnegball)).comp e ((hasDerivAt_id e).neg))
    have hTneg : T (-e) = T e := by simp [T,sourceCanonicalCosinePoint,cosineGapPoint,Complex.cos_neg]
    change HasDerivAt (fun t => H t+H (-t))
      (sourceAngularGapNumerator hp hp1 n m s ψ (T e)+
        sourceAngularGapNumerator hp hp1 n m s ψ (T (-e))*(-1)) e at hderiv
    simpa only [hTneg,mul_neg,mul_one,add_neg_cancel] using hderiv
  have hconstant (e : ℂ) (he : e ∈ ball (0:ℂ) ρ) : H e+H (-e) = 2*H 0 := by
    have hn := (convex_ball (0:ℂ) ρ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun q hq => (hsum q hq).hasDerivWithinAt)
      (fun _ _ => (by simp : ‖(0:ℂ)‖ ≤ (0:ℝ))) (mem_ball_self hρ) he
    have hz : (H e+H (-e))-(H 0+H (-0)) = 0 :=
      norm_eq_zero.mp (le_antisymm (by simpa only [zero_mul] using hn) (norm_nonneg _))
    simpa only [neg_zero,← two_mul] using sub_eq_zero.mp hz
  let a : ℂ := ((ρ/2:ℝ):ℂ)*I
  have ha : a ∈ ball (0:ℂ) ρ := by
    simp only [mem_ball,dist_zero_right,a,norm_mul,norm_real,Real.norm_eq_abs,norm_I,mul_one]
    rw [abs_of_pos (by positivity : 0 < ρ/2)]
    linarith
  have hnega : -a ∈ ball (0:ℂ) ρ := by simpa only [mem_ball,dist_zero_right,norm_neg] using ha
  have hai : a.im ≠ 0 := by simp only [a,mul_im,ofReal_re,I_im,ofReal_im,I_re,mul_one,mul_zero,add_zero]; positivity
  have hδ : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2 ≠ 0 :=
    div_ne_zero (D.gap_ne_zero ψ hψ) (by norm_num)
  obtain ⟨F,A,E,hE⟩ := (D.disc_family ψ hψ).exists_sheet_primitive_data n m hmn
    (by intro heq; apply D.gap_ne_zero ψ hψ; simp only [canonicalPeriodicGap,heq,sub_self])
    (D.endpoint_data ψ hψ) 1 one_ne_zero
  let C := cosineRootCoefficient (sourceStandardRoot hp hp1 ψ m)
    (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2) a
  have hC : C ≠ 0 := by
    apply div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hδ) (sin_ne_zero_of_im_ne_zero a hai))
    apply sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m (T a)
    have hl : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m -
        canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2 =
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
      dsimp [canonicalPeriodicMidpoint,canonicalPeriodicGap]; ring
    have hr : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m +
        canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2 =
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
      dsimp [canonicalPeriodicMidpoint,canonicalPeriodicGap]; ring
    change T a ∉ segment ℝ _ _
    rw [← hl,← hr]
    exact cosineGapPoint_not_mem_segment _ _ a hδ hai
  have hpos := D.spectral_matching_of_im_ne_zero ψ hψ n F A hE.hasDerivAt_exterior
    hE.tendsto_left_exterior a (hball ha) hai
  have hneg := D.spectral_matching_of_im_ne_zero ψ hψ n F A hE.hasDerivAt_exterior
    hE.tendsto_left_exterior (-a) (hball hnega) (by simpa only [neg_im] using neg_ne_zero.mpr hai)
  have hTneg : T (-a) = T a := by simp [T,sourceCanonicalCosinePoint,cosineGapPoint,Complex.cos_neg]
  change F (T a)-A = C*H a at hpos
  rw [cosineRootCoefficient_neg] at hneg
  change F (T (-a))-A = -C*H (-a) at hneg
  rw [hTneg] at hneg
  have hprod : C*(H a+H (-a)) = 0 := by linear_combination hneg-hpos
  have hsumzero := (mul_eq_zero.mp hprod).resolve_left hC
  have hzero : 2*H 0 = 0 := (hconstant a ha).symm.trans hsumzero
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)

/-- The actual terminal square identity, before dividing by the gap
and the nonzero omitted product. -/
theorem dirichlet_anti_sq
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
    sourceAntiDiscriminantCandidate hp hp1 ψ μ^2 = -4*
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-μ)*
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-μ)*
      sourceStandardRootOmittedProduct hp hp1 m ψ μ^2 := by
  dsimp only
  rw [← sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 ψ m,
    canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 _ (periodOnePotential_mem ψ) m]
  rw [← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 ψ m _
    (((D.disc_family ψ hψ).contour_family.2 m).2.2.1
      (ball_subset_closedBall ((D.disc_family ψ hψ).dirichlet_mem_ball m)))]

/-- The analytic normalized terminal sine and cosine obey the exact
trigonometric square identity throughout the complex source chart. -/
theorem dirichlet_sine_sq_add_cosine_sq
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) :
    sourceAngularDirichletSine hp hp1 m ψ^2 +
      ((canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)/
        (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2))^2 = 1 := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let γ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let P := sourceStandardRootOmittedProduct hp hp1 m ψ μ
  let w := sourceAntiDiscriminantCandidate hp hp1 ψ μ
  have hP : P ≠ 0 := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ μ m
    (((D.disc_family ψ hψ).contour_family.2 m).2.2.1
      (ball_subset_closedBall ((D.disc_family ψ hψ).dirichlet_mem_ball m)))
  have hγ : γ ≠ 0 := D.gap_ne_zero ψ hψ
  have hid : w^2 = (γ^2-4*(μ-τ)^2)*P^2 := by
    rw [D.dirichlet_anti_sq ψ hψ]
    dsimp only [γ,τ,canonicalPeriodicGap,canonicalPeriodicMidpoint,P]
    ring
  change (w/(γ*P))^2+((μ-τ)/(γ/2))^2 = 1
  field_simp [hγ,hP]
  linear_combination hid

/-- Endpoint terminals have zero actual normalized sine. -/
theorem dirichlet_sine_eq_zero_of_endpoint
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (hend : SourceAngularDirichletTerminalIsEndpoint hp hp1 ψ m) :
    sourceAngularDirichletSine hp hp1 m ψ = 0 := by
  have hw : sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) = 0 := by
    apply sq_eq_zero_iff.mp
    rw [D.dirichlet_anti_sq ψ hψ]
    rcases hend with hleft | hright
    · rw [hleft]; ring
    · rw [hright]; ring
  simp only [sourceAngularDirichletSine,hw,zero_div]

/-- The normalized sine is analytic through a zero terminal
anti-discriminant on an open gap chart. -/
theorem analyticAt_dirichletSine
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (φ : CoeffPair p) (hφ : φ ∈ V)
    (hμ : AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ) :
    AnalyticAt ℂ (sourceAngularDirichletSine hp hp1 m) φ := by
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  have hgraph : AnalyticAt ℂ (fun ψ => (μ ψ,ψ)) φ := hμ.prod analyticAt_id
  have hP : AnalyticAt ℂ (fun ψ => sourceStandardRootOmittedProduct hp hp1 m ψ (μ ψ)) φ :=
    (D.omitted_analytic (μ φ,φ) ⟨(D.disc_family φ hφ).dirichlet_mem_ball m,hφ⟩).comp
      (x := φ) (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph
  have hanti : AnalyticAt ℂ (fun ψ => sourceAntiDiscriminantCandidate hp hp1 ψ (μ ψ)) φ :=
    (analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1 (μ φ,φ) (mem_univ _)).comp
      (x := φ) (f := fun ψ : CoeffPair p => (μ ψ,ψ)) hgraph
  exact hanti.div ((D.gap_analytic φ hφ).mul hP)
    (mul_ne_zero (D.gap_ne_zero φ hφ) (sourceStandardRootOmittedProduct_ne_zero hp hp1 φ (μ φ) m
      (((D.disc_family φ hφ).contour_family.2 m).2.2.1
        (ball_subset_closedBall ((D.disc_family φ hφ).dirichlet_mem_ball m)))))

end SourceAngularCanonicalCosineChartData
end NLS.ZakharovShabat
