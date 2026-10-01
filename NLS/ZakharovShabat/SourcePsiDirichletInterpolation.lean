import NLS.ComplexAnalysis.SimplePoleCauchyInterpolation
import NLS.ZakharovShabat.SourcePsiDirichletInterpolationExterior
import NLS.ZakharovShabat.SourceDirichletRootCircleSelection
import NLS.ZakharovShabat.SourceBoundaryRootDifferential

/-! # Actual Dirichlet interpolation of the psi numerators

The actual simple Dirichlet roots supply the residues. Large circles
enclose exactly the symmetric index cutoffs, and the derived outer
Cauchy error tends uniformly to zero on bounded evaluation sets.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A literal Dirichlet interpolation contribution, with the original
characteristic derivative normalization. -/
def sourcePsiDirichletInterpolationTerm (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : Coeff p) (φ : CoeffPair p) (m : ℤ) (w : ℂ) : ℂ :=
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m
  sourcePsiCandidate n (μ,a)/deriv (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ) μ/(w-μ)

/-- The actual finite interpolation error is the outer Cauchy integral
for every sufficiently large symmetric root cutoff. -/
theorem eventually_sourcePsiDirichlet_interpolation_error
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : realTypeSourceLocus p) :
    ∃ K : ℕ, ∀ N : ℕ, K ≤ N → ∀ w : ℂ,
      ‖w‖ < centralCircleRadius N →
      periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val w ≠ 0 →
      (∮ z in C(0,centralCircleRadius N),
        sourcePsiCandidate n (z,a)/periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val z/(z-w)) =
        (2*Real.pi*I)*(sourcePsiCandidate n (w,a)/periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val w-
          ∑ m ∈ Finset.Icc (-(N : ℤ)) N, sourcePsiDirichletInterpolationTerm hp hp1 n a φ.val m w) := by
  obtain ⟨K₀,hK₀⟩ := eventually_canonicalDirichletRoots_mem_centralBall_iff hp hp1 φ.val
  obtain ⟨K₁,hK₁⟩ := eventually_centralCircle_sourcePsiCandidate_dirichletQuotient_le hp hp1 n a φ.val
  refine ⟨max K₀ K₁,?_⟩
  intro N hN w hw hgw
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val
  let f : ℂ → ℂ := fun z => sourcePsiCandidate n (z,a)
  let g := periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val
  let t := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let s := t.image μ
  have hR : 0 < centralCircleRadius N := by unfold centralCircleRadius; positivity
  have hμinj : Function.Injective μ :=
    injective_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property
  have hselect := hK₀ N ((le_max_left _ _).trans hN)
  have hboundary := hK₁ N ((le_max_right _ _).trans hN)
  have hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) (centralCircleRadius N)) := by
    intro z _
    exact (analyticOnNhd_sourcePsiCandidate hp hp1 n (z,a) (mem_univ _)).comp
      (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
  have hg : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) (centralCircleRadius N)) :=
    (analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val).mono (subset_univ _)
  have hs : (s : Set ℂ) ⊆ ball (0 : ℂ) (centralCircleRadius N) := by
    intro z hz
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hz
    have hmN : m.natAbs ≤ N := by
      change m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) at hm
      simp only [Finset.mem_Icc] at hm
      omega
    simpa only [mem_ball,dist_zero_right] using (hselect m).mpr hmN
  have hzero : ∀ z ∈ s, g z = 0 := by
    intro z hz
    obtain ⟨m,_,rfl⟩ := Finset.mem_image.mp hz
    exact periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero hp hp1 .dirichlet φ.val m
  have hsimple : ∀ z ∈ s, deriv g z ≠ 0 := by
    intro z hz
    obtain ⟨m,_,rfl⟩ := Finset.mem_image.mp hz
    exact deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType hp hp1
      .dirichlet φ.val φ.property m
  have hcover : ∀ z ∈ closedBall (0 : ℂ) (centralCircleRadius N), g z = 0 → z ∈ s := by
    intro z hz hgz
    obtain ⟨m,rfl⟩ := (canonicalPeriodOneBoundaryRoots_exhaustive hp hp1 .dirichlet φ.val z).mp
      ((periodOneBoundaryCharacteristic_eq_zero_iff hp hp1 .dirichlet φ.val z).mp hgz)
    have hle : ‖μ m‖ ≤ centralCircleRadius N := by simpa only [mem_closedBall,dist_zero_right] using hz
    have hlt : ‖μ m‖ < centralCircleRadius N := by
      by_contra he
      have heq : ‖μ m‖ = centralCircleRadius N := le_antisymm hle (le_of_not_gt he)
      exact (hboundary (μ m) (by simpa only [mem_sphere,dist_zero_right] using heq)).1 hgz
    have hmN := (hselect m).mp hlt
    apply Finset.mem_image.mpr
    refine ⟨m,?_,rfl⟩
    change m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
    simp only [Finset.mem_Icc]
    omega
  have he := circleIntegral_simpleQuotient_cauchy_eq_interpolation_error hR hf hg s hs
    hzero hsimple hcover (by simpa only [mem_ball,dist_zero_right] using hw) hgw
  have hsum : simpleQuotientPrincipalParts f g s w =
      ∑ m ∈ Finset.Icc (-(N : ℤ)) N, sourcePsiDirichletInterpolationTerm hp hp1 n a φ.val m w := by
    dsimp only [simpleQuotientPrincipalParts,s]
    rw [Finset.sum_image (fun m _ j _ he => hμinj he)]
    rfl
  rw [hsum] at he
  exact he

/-- The actual psi/Dirichlet quotient is the uniform limit of its
symmetric simple-root interpolation sums on every bounded zero-free
evaluation set. Neither a residue formula nor summability is assumed. -/
theorem tendstoUniformlyOn_sourcePsiDirichletInterpolation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : realTypeSourceLocus p)
    (L : ℝ) (hL : 0 ≤ L) :
    TendstoUniformlyOn (fun N : ℕ => fun w : ℂ =>
      ∑ m ∈ Finset.Icc (-(N : ℤ)) N, sourcePsiDirichletInterpolationTerm hp hp1 n a φ.val m w)
      (fun w => sourcePsiCandidate n (w,a)/periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val w)
      atTop {w | ‖w‖ ≤ L ∧ periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val w ≠ 0} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨K₀,hK₀⟩ := eventually_sourcePsiDirichlet_interpolation_error hp hp1 n a φ
  obtain ⟨K₁,hK₁⟩ := eventually_sourcePsiDirichlet_outerCauchy_small hp hp1 n a φ.val L hL
    (by positivity : 0 < (2*Real.pi)*ε)
  obtain ⟨K₂,hK₂⟩ := exists_nat_gt (L/Real.pi)
  filter_upwards [eventually_ge_atTop K₀,eventually_ge_atTop K₁,eventually_ge_atTop K₂] with N hN₀ hN₁ hN₂
  intro w hw
  have hK₂ : L < (K₂ : ℝ)*Real.pi := (div_lt_iff₀ Real.pi_pos).mp (by exact_mod_cast hK₂)
  have hN₂ : (K₂ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN₂
  have hwR : ‖w‖ < centralCircleRadius N := by
    unfold centralCircleRadius
    nlinarith [hw.1,Real.pi_pos]
  have he := hK₀ N hN₀ w hwR hw.2
  have hb := hK₁ N hN₁ w hw.1
  have hnorm : ‖(2*Real.pi*I : ℂ)‖ = 2*Real.pi := by
    simp only [norm_mul,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,norm_I,mul_one]
  rw [he,norm_mul,hnorm] at hb
  rw [dist_eq_norm]
  change ‖sourcePsiCandidate n (w,a)/periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val w-
    ∑ m ∈ Finset.Icc (-(N : ℤ)) N, sourcePsiDirichletInterpolationTerm hp hp1 n a φ.val m w‖ < ε
  nlinarith [Real.pi_pos]

/-- The characteristic-weighted interpolation has the exact orientation
needed by the actual action contour kernels. -/
theorem tendsto_sourcePsiDirichlet_weightedInterpolation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : realTypeSourceLocus p)
    (w : ℂ) (hw : periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val w ≠ 0) :
    Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
      let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m
      sourcePsiCandidate n (μ,a)*periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val w/
        ((μ-w)*deriv (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val) μ))
      atTop (𝓝 (-sourcePsiCandidate n (w,a))) := by
  let g := periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val
  have ht := (tendstoUniformlyOn_sourcePsiDirichletInterpolation hp hp1 n a φ ‖w‖ (norm_nonneg w)).tendsto_at
    (show w ∈ {z | ‖z‖ ≤ ‖w‖ ∧ g z ≠ 0} from ⟨le_rfl,hw⟩)
  have hs := ht.const_mul (-g w)
  have hvalue : (-g w)*(sourcePsiCandidate n (w,a)/g w) = -sourcePsiCandidate n (w,a) := by
    field_simp [show g w ≠ 0 from hw]
  rw [hvalue] at hs
  apply hs.congr'
  filter_upwards [] with N
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  dsimp only [sourcePsiDirichletInterpolationTerm,g]
  rw [show canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m-w =
      -(w-canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m) by ring]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_neg]
  ring

end NLS.ZakharovShabat
