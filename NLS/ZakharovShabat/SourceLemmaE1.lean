import NLS.ComplexAnalysis.SimplePoleCauchyInterpolation
import NLS.ZakharovShabat.AppendixEInterpolationProducts
import NLS.ZakharovShabat.AppendixEInterpolationDecay
import NLS.ZakharovShabat.SourceDirichletRootCircleSelection

/-! # Lemma E.1: interpolation at a simple displaced lattice

For every finite Banach exponent, the symmetric sums of the literal
omitted-root cardinal products converge to the entire numerator. The
hypothesis is the source's actual supremum limit on half-integer circles.
The product's diagonal index is omitted, as in the source residue proof.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite interpolation error on every sufficiently large source circle. -/
theorem eventually_appendixE_interpolation_error (hp : p ≠ ⊤) (a : Coeff p)
    (ha : Function.Injective (displacedRoots a)) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ) :
    ∃ K : ℕ, ∀ N : ℕ, K ≤ N → ∀ w : ℂ,
      ‖w‖ < centralCircleRadius N → appendixDProduct (w,a) ≠ 0 →
      (∮ z in C(0,centralCircleRadius N), f z/appendixDProduct (z,a)/(z-w)) =
        (2*Real.pi*I)*(f w/appendixDProduct (w,a)-
          ∑ m ∈ Finset.Icc (-(N:ℤ)) N,
            (f (displacedRoots a m)/deriv (fun z => appendixDProduct (z,a)) (displacedRoots a m))/
              (w-displacedRoots a m)) := by
  obtain ⟨K₀,hK₀⟩ := eventually_displacedRoots_mem_centralBall_iff hp a
  obtain ⟨K₁,hK₁⟩ := eventually_atTop.mp (eventually_appendixDProduct_circle_lower hp a)
  refine ⟨max K₀ K₁,?_⟩
  intro N hN w hw hgw
  let μ := displacedRoots a
  let g : ℂ → ℂ := fun z => appendixDProduct (z,a)
  let t := Finset.Icc (-(N:ℤ)) (N:ℤ)
  let s := t.image μ
  have hR : 0 < centralCircleRadius N := centralCircleRadius_pos N
  have hselect := hK₀ N ((le_max_left _ _).trans hN)
  have hboundary := hK₁ N ((le_max_right _ _).trans hN)
  have hg : AnalyticOnNhd ℂ g (closedBall (0:ℂ) (centralCircleRadius N)) := by
    intro z _
    exact ((analyticOnNhd_appendixDProduct hp) _ (mem_univ _)).comp
      (analyticAt_id.prod analyticAt_const)
  have hs : (s : Set ℂ) ⊆ ball (0:ℂ) (centralCircleRadius N) := by
    intro z hz
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hz
    have hmN : m.natAbs ≤ N := by
      change m ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) at hm
      simp only [Finset.mem_Icc] at hm
      omega
    simpa only [mem_ball,dist_zero_right] using (hselect m).mpr hmN
  have hzero : ∀ z ∈ s, g z = 0 := by
    intro z hz
    obtain ⟨m,_,rfl⟩ := Finset.mem_image.mp hz
    exact (appendixDProduct_eq_zero_iff hp a _).mpr ⟨m,rfl⟩
  have hsimple : ∀ z ∈ s, deriv g z ≠ 0 := by
    intro z hz
    obtain ⟨m,_,rfl⟩ := Finset.mem_image.mp hz
    exact deriv_appendixDProduct_ne_zero hp a ha m
  have hcover : ∀ z ∈ closedBall (0:ℂ) (centralCircleRadius N), g z = 0 → z ∈ s := by
    intro z hz hgz
    obtain ⟨m,rfl⟩ := (appendixDProduct_eq_zero_iff hp a z).mp hgz
    have hle : ‖μ m‖ ≤ centralCircleRadius N := by simpa only [mem_closedBall,dist_zero_right] using hz
    have hlt : ‖μ m‖ < centralCircleRadius N := by
      by_contra he
      have heq : ‖μ m‖ = centralCircleRadius N := le_antisymm hle (le_of_not_gt he)
      exact (hboundary (μ m) (by simpa only [mem_sphere,dist_zero_right] using heq)).1 hgz
    have hmN := (hselect m).mp hlt
    apply Finset.mem_image.mpr
    refine ⟨m,?_,rfl⟩
    change m ∈ Finset.Icc (-(N:ℤ)) (N:ℤ)
    simp only [Finset.mem_Icc]
    omega
  have he := circleIntegral_simpleQuotient_cauchy_eq_interpolation_error hR
    (hf.mono (subset_univ _)) hg s hs hzero hsimple hcover
    (by simpa only [mem_ball,dist_zero_right] using hw) hgw
  have hsum : simpleQuotientPrincipalParts f g s w =
      ∑ m ∈ Finset.Icc (-(N:ℤ)) N, (f (μ m)/deriv g (μ m))/(w-μ m) := by
    dsimp only [simpleQuotientPrincipalParts,s]
    rw [Finset.sum_image (fun m _ j _ he => ha he)]
  rw [hsum] at he
  exact he

/-- Symmetric residue sums converge uniformly on bounded zero-free evaluation sets.
This convergence is proved from the contour error; it is not a summability hypothesis. -/
theorem tendstoUniformlyOn_appendixEQuotientInterpolation (hp : p ≠ ⊤) (a : Coeff p)
    (ha : Function.Injective (displacedRoots a)) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius N), ‖f z/sin z‖ ≤ ε)
    (L : ℝ) :
    TendstoUniformlyOn (fun N : ℕ => fun w : ℂ =>
      ∑ m ∈ Finset.Icc (-(N:ℤ)) N,
        (f (displacedRoots a m)/deriv (fun z => appendixDProduct (z,a)) (displacedRoots a m))/
          (w-displacedRoots a m))
      (fun w => f w/appendixDProduct (w,a)) atTop
      {w | ‖w‖ ≤ L ∧ appendixDProduct (w,a) ≠ 0} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨K,hK⟩ := eventually_appendixE_interpolation_error hp a ha f hf
  filter_upwards [eventually_ge_atTop K,
    eventually_appendixE_outerCauchy_small hp a f hdecay L (by positivity : 0 < (2*Real.pi)*ε),
    tendsto_centralCircleRadius_atTop.eventually (eventually_gt_atTop L)] with N hN hsmall hlarge
  intro w hw
  have he := hK N hN w (hw.1.trans_lt hlarge) hw.2
  have hb := hsmall w hw.1
  have hnorm : ‖(2*Real.pi*I:ℂ)‖ = 2*Real.pi := by
    simp only [norm_mul,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,norm_I,mul_one]
  rw [he,norm_mul,hnorm] at hb
  rw [dist_eq_norm]
  nlinarith [Real.pi_pos]

/-- E.1 with the equivalent uniform-epsilon circle hypothesis and explicit symmetric sums. -/
theorem sourceLemmaE1_of_circle_decay (hp : p ≠ ⊤) (a : Coeff p)
    (ha : Function.Injective (displacedRoots a)) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius N), ‖f z/sin z‖ ≤ ε)
    (w : ℂ) (hw : ∀ n : ℤ, w ≠ displacedRoots a n) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N:ℤ)) N,
      f (displacedRoots a n)*appendixEInterpolationKernel a n w) atTop (𝓝 (f w)) := by
  have hgw : appendixDProduct (w,a) ≠ 0 := by
    intro he
    obtain ⟨n,hn⟩ := (appendixDProduct_eq_zero_iff hp a w).mp he
    exact hw n hn.symm
  have ht := (tendstoUniformlyOn_appendixEQuotientInterpolation hp a ha f hf hdecay ‖w‖).tendsto_at
    (show w ∈ {z | ‖z‖ ≤ ‖w‖ ∧ appendixDProduct (z,a) ≠ 0} from ⟨le_rfl,hgw⟩)
  have h := ht.const_mul (appendixDProduct (w,a))
  have hv : appendixDProduct (w,a)*(f w/appendixDProduct (w,a)) = f w := by field_simp
  rw [hv] at h
  apply h.congr'
  filter_upwards [] with N
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [appendixEInterpolationKernel_eq_deriv hp a n w (hw n)]
  ring

/-- Lemma E.1 with its literal supremum-decay hypothesis, for all 1 ≤ p < infinity.
The cardinal product is identified with its literal cutoffs by
`tendsto_appendixEInterpolationKernel`; the outer sum uses symmetric cutoffs. -/
theorem sourceLemmaE1 (hp : p ≠ ⊤) (a : Coeff p)
    (ha : Function.Injective (displacedRoots a)) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (hdecay : Tendsto (appendixESineCircleSup f) atTop (𝓝 0))
    (w : ℂ) (hw : ∀ n : ℤ, w ≠ displacedRoots a n) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N:ℤ)) N,
      f (displacedRoots a n)*appendixEInterpolationKernel a n w) atTop (𝓝 (f w)) :=
  sourceLemmaE1_of_circle_decay hp a ha f hf
    (fun _ hε => eventually_sineQuotient_small_of_sup_tendsto f hf hdecay hε) w hw

/-- Both levels of the source formula expressed as literal cutoff limits:
each omitted product converges, and the symmetric sums of those limits recover f. -/
theorem sourceLemmaE1_literal (hp : p ≠ ⊤) (a : Coeff p)
    (ha : Function.Injective (displacedRoots a)) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (hdecay : Tendsto (appendixESineCircleSup f) atTop (𝓝 0))
    (w : ℂ) (hw : ∀ n : ℤ, w ≠ displacedRoots a n) :
    ∃ P : ℤ → ℂ,
      (∀ n : ℤ, Tendsto (fun M : ℕ =>
        ∏ m ∈ (Finset.Icc (-(M:ℤ)) (M:ℤ)).erase n,
          (displacedRoots a m-w)/(displacedRoots a m-displacedRoots a n)) atTop (𝓝 (P n))) ∧
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N:ℤ)) N,
        f (displacedRoots a n)*P n) atTop (𝓝 (f w)) :=
  ⟨fun n => appendixEInterpolationKernel a n w,
    fun n => tendsto_appendixEInterpolationKernel hp a ha n w,
    sourceLemmaE1 hp a ha f hf hdecay w hw⟩

end NLS.ZakharovShabat
