import NLS.ZakharovShabat.SourcePsiCriticalQuotientExterior
import NLS.ZakharovShabat.SourceDirichletRootCircleSelection
import NLS.ZakharovShabat.RealCriticalSimplicity
import NLS.ComplexAnalysis.SimplePoleCauchyInterpolation

/-! # Actual Cauchy interpolation at the complete critical sequence

The residues are evaluated at the actual simple canonical critical
points. Exact symmetric root selection and the derived exterior bound
make the outer Cauchy error tend uniformly to zero on bounded sets.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourcePsiCriticalResidue (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : Coeff p) (φ : CoeffPair p) (m : ℤ) : ℂ :=
  let β := canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m
  sourcePsiCandidate n (β,a)/deriv (deriv (canonicalDiscriminant hp (periodOnePotential φ))) β

def sourcePsiCriticalInterpolationTerm (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : Coeff p) (φ : CoeffPair p) (m : ℤ) (w : ℂ) : ℂ :=
  sourcePsiCriticalResidue hp hp1 n a φ m /
    (w-canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m)

theorem eventually_canonicalCriticalPoints_mem_centralBall_iff
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ K : ℕ, ∀ N : ℕ, K ≤ N → ∀ m : ℤ,
      ‖canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m‖ <
        centralCircleRadius N ↔ m.natAbs ≤ N := by
  let a := canonicalCriticalDisplacement hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
  have he (m : ℤ) : displacedRoots a m =
      canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m := by
    simp only [displacedRoots,a,canonicalCriticalDisplacement_apply]
    ring
  simpa only [he] using eventually_displacedRoots_mem_centralBall_iff hp a

theorem eventually_sourcePsiCritical_interpolation_error
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∀ N : ℕ, K ≤ N → ∀ w : ℂ, ‖w‖ < centralCircleRadius N →
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) w ≠ 0 →
      (∮ z in C(0,centralCircleRadius N),
        sourcePsiCandidate n (z,a)/deriv (canonicalDiscriminant hp (periodOnePotential φ)) z/(z-w)) =
        (2*Real.pi*I)*(sourcePsiCandidate n (w,a)/deriv (canonicalDiscriminant hp (periodOnePotential φ)) w-
          ∑ m ∈ Finset.Icc (-(N:ℤ)) N, sourcePsiCriticalInterpolationTerm hp hp1 n a φ m w) := by
  obtain ⟨K₀,hK₀⟩ := eventually_canonicalCriticalPoints_mem_centralBall_iff hp hp1 φ
  obtain ⟨K₁,hK₁⟩ := eventually_centralCircle_sourcePsiCandidate_criticalQuotient_le hp hp1 n a φ
  refine ⟨max K₀ K₁,?_⟩
  intro N hN w hw hgw
  let β := canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
  let f : ℂ → ℂ := fun z => sourcePsiCandidate n (z,a)
  let g := deriv (canonicalDiscriminant hp (periodOnePotential φ))
  let t := Finset.Icc (-(N:ℤ)) N
  let s := t.image β
  have hR : 0 < centralCircleRadius N := by unfold centralCircleRadius; positivity
  have hβinj : Function.Injective β := canonicalCriticalPoints_injective_of_realType hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hreal)
  have hselect := hK₀ N ((le_max_left _ _).trans hN)
  have hboundary := hK₁ N ((le_max_right _ _).trans hN)
  have hf : AnalyticOnNhd ℂ f (closedBall (0:ℂ) (centralCircleRadius N)) := by
    intro z _
    exact (analyticOnNhd_sourcePsiCandidate hp hp1 n (z,a) (mem_univ _)).comp
      (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
  have hg : AnalyticOnNhd ℂ g (closedBall (0:ℂ) (centralCircleRadius N)) :=
    (analyticOnNhd_discriminant_derivative hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)).mono (subset_univ _)
  have hs : (s : Set ℂ) ⊆ ball (0:ℂ) (centralCircleRadius N) := by
    intro z hz
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hz
    have hmN : m.natAbs ≤ N := by change m ∈ Finset.Icc (-(N:ℤ)) N at hm; simp only [Finset.mem_Icc] at hm; omega
    simpa only [mem_ball,dist_zero_right] using (hselect m).mpr hmN
  have hzero : ∀ z ∈ s, g z = 0 := by
    intro z hz
    obtain ⟨m,_,rfl⟩ := Finset.mem_image.mp hz
    exact canonicalCriticalPoints_is_critical hp hp1 _ (periodOnePotential_mem φ) m
  have hsimple : ∀ z ∈ s, deriv g z ≠ 0 := by
    intro z hz
    obtain ⟨m,_,rfl⟩ := Finset.mem_image.mp hz
    exact discriminant_second_derivative_ne_zero_at_critical_of_realType hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hreal) _
      (canonicalCriticalPoints_is_critical hp hp1 _ (periodOnePotential_mem φ) m)
  have hcover : ∀ z ∈ closedBall (0:ℂ) (centralCircleRadius N), g z = 0 → z ∈ s := by
    intro z hz hgz
    obtain ⟨m,rfl⟩ := (canonicalCriticalPoints_exhaustive hp hp1 _ (periodOnePotential_mem φ) z).mp hgz
    have hle : ‖β m‖ ≤ centralCircleRadius N := by simpa only [mem_closedBall,dist_zero_right] using hz
    have hlt : ‖β m‖ < centralCircleRadius N := by
      by_contra he
      have heq : ‖β m‖ = centralCircleRadius N := le_antisymm hle (le_of_not_gt he)
      exact (hboundary (β m) (by simpa only [mem_sphere,dist_zero_right] using heq)).1 hgz
    have hmN := (hselect m).mp hlt
    apply Finset.mem_image.mpr
    refine ⟨m,?_,rfl⟩
    change m ∈ Finset.Icc (-(N:ℤ)) N
    simp only [Finset.mem_Icc]
    omega
  have he := circleIntegral_simpleQuotient_cauchy_eq_interpolation_error hR hf hg s hs hzero hsimple hcover
    (by simpa only [mem_ball,dist_zero_right] using hw) hgw
  have hsum : simpleQuotientPrincipalParts f g s w =
      ∑ m ∈ Finset.Icc (-(N:ℤ)) N, sourcePsiCriticalInterpolationTerm hp hp1 n a φ m w := by
    dsimp only [simpleQuotientPrincipalParts,s]
    rw [Finset.sum_image (fun m _ j _ he => hβinj he)]
    rfl
  rw [hsum] at he
  exact he

theorem tendstoUniformlyOn_sourcePsiCriticalInterpolation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (L : ℝ) (hL : 0 ≤ L) :
    TendstoUniformlyOn (fun N : ℕ => fun w : ℂ =>
      ∑ m ∈ Finset.Icc (-(N:ℤ)) N, sourcePsiCriticalInterpolationTerm hp hp1 n a φ m w)
      (fun w => sourcePsiCandidate n (w,a)/deriv (canonicalDiscriminant hp (periodOnePotential φ)) w)
      atTop {w | ‖w‖ ≤ L ∧ deriv (canonicalDiscriminant hp (periodOnePotential φ)) w ≠ 0} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨K₀,hK₀⟩ := eventually_sourcePsiCritical_interpolation_error hp hp1 n a φ hreal
  obtain ⟨K₁,hK₁⟩ := eventually_sourcePsiCritical_outerCauchy_small hp hp1 n a φ L hL
    (by positivity : 0 < (2*Real.pi)*ε)
  obtain ⟨K₂,hK₂⟩ := exists_nat_gt (L/Real.pi)
  filter_upwards [eventually_ge_atTop K₀,eventually_ge_atTop K₁,eventually_ge_atTop K₂] with N hN₀ hN₁ hN₂
  intro w hw
  have hK₂ : L < (K₂:ℝ)*Real.pi := (div_lt_iff₀ Real.pi_pos).mp (by exact_mod_cast hK₂)
  have hN₂ : (K₂:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN₂
  have hwR : ‖w‖ < centralCircleRadius N := by unfold centralCircleRadius; nlinarith [hw.1,Real.pi_pos]
  have he := hK₀ N hN₀ w hwR hw.2
  have hb := hK₁ N hN₁ w hw.1
  have hnorm : ‖(2*Real.pi*I:ℂ)‖ = 2*Real.pi := by
    simp only [norm_mul,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,norm_I,mul_one]
  rw [he,norm_mul,hnorm] at hb
  rw [dist_eq_norm]
  change ‖sourcePsiCandidate n (w,a)/deriv (canonicalDiscriminant hp (periodOnePotential φ)) w-
    ∑ m ∈ Finset.Icc (-(N:ℤ)) N, sourcePsiCriticalInterpolationTerm hp hp1 n a φ m w‖ < ε
  nlinarith [Real.pi_pos]

end NLS.ZakharovShabat
