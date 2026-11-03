import NLS.KdV.HillHminusOneFreeSquareComparison
import NLS.ComplexAnalysis.QuadraticClusterCount

/-! # Actual high H^-1 two-root clusters

Rouché compares the filled primitive square with the quadratic free
model on a common family of energy discs. The resulting unordered pair
has exactly the analytic multiplicities of the actual H^-1 radicand.
The endpoints may coincide; no analytic ordering is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped Classical
namespace NLS.KdV

/-- A local actual spectral pair on a specified complete energy disc. -/
structure HillHminusHighGapPair (q : PeriodOneHminusOne) (n : ℕ+) (r : ℝ)
    (l u : ℂ) : Prop where
  left_mem : l ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)
  right_mem : u ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)
  left_zero : hillHminusRadicand q l = 0
  right_zero : hillHminusRadicand q u = 0
  zeros_iff : ∀ z ∈ hillHminusGapSquareDisc n r,
    hillHminusRadicand q z = 0 ↔ z = l ∨ z = u
  multiplicity : ∀ z ∈ hillHminusGapSquareDisc n r,
    analyticOrderNatAt (fun w => hillHminusRadicand q w) z = ({l,u} : Multiset ℂ).count z
  trace_left : hillHminusDiscriminant q l = 2*(-1 : ℂ)^(n : ℕ)
  trace_right : hillHminusDiscriminant q u = 2*(-1 : ℂ)^(n : ℕ)

theorem HillHminusHighGapPair.swap
    {q : PeriodOneHminusOne} {n : ℕ+} {r : ℝ} {l u : ℂ}
    (h : HillHminusHighGapPair q n r l u) : HillHminusHighGapPair q n r u l := by
  refine ⟨h.right_mem,h.left_mem,h.right_zero,h.left_zero,?_,?_,h.trace_right,h.trace_left⟩
  · intro z hz
    rw [h.zeros_iff z hz,or_comm]
  · intro z hz
    rw [h.multiplicity z hz,Multiset.pair_comm]

/-- The whole analytic square gives the exact physical multiplicity at
every interior zero. The product neighborhood supplies the germ identity. -/
theorem hillHminus_square_order_on_disc
    (n : ℕ+) (r : ℝ) (V : Set PeriodOneHminusOne) (hV : IsOpen V)
    (K : ℂ × PeriodOneHminusOne → ℂ)
    (hK : AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V))
    (hrel : ∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V,
      squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant t.2 t.1/2)
    (a : PeriodOneHminusOne) (ha : a ∈ V) (z : ℂ)
    (hz : z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r))
    (hzero : K (z,a) = 0) :
    analyticOrderNatAt (fun w => K (w,a)) z =
      analyticOrderNatAt (fun w => hillHminusRadicand a w) z := by
  have hsign : ((-1 : ℂ)^(n : ℕ))^2 = 1 := by rw [pow_two,← mul_pow]; simp
  apply hillHminus_squared_primitive_energy_order (z,a) _ hsign K
    (hK (z,a) ⟨ball_subset_closedBall hz,ha⟩) hzero
  filter_upwards [(isOpen_ball.prod hV).mem_nhds ⟨hz,ha⟩] with t ht
  exact hrel t ⟨ball_subset_closedBall ht.1,ht.2⟩

/-- A common radius, cutoff and H^-1-open neighborhood precede every
high index and every nearby potential. Each full disc contains exactly
two actual radicand roots, including their exact analytic multiplicities. -/
theorem exists_hillHminus_quadratic_square_pairs (q : PeriodOneHminusOne) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi/4 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1/16 →
        ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V, ‖K t‖ < 1) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V,
          squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant t.2 t.1/2) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V,
          K t = 0 ↔ hillHminusRadicand t.2 t.1 = 0) ∧
        (∀ t ∈ (hillHminusGapSquareDisc n r ×ˢ V) ∩ hillHminusContinuationDomain,
          K t = (hillHminusContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V,
          ‖K t-classicalHillFreeQuadraticModel n t.1‖ ≤ epsilon*r^2) ∧
        ∀ a ∈ V, analyticZeroCount (fun z => K (z,a)) (hillHminusGapSquareDisc n r) = 2 ∧
          ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
            ∀ z ∈ hillHminusGapSquareDisc n r,
              analyticOrderNatAt (fun w => K (w,a)) z = ({l,u} : Multiset ℂ).count z := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := exists_hillHminus_quadratic_square_comparison q
  refine ⟨r,hr,hrpi,?_⟩
  intro epsilon hepsilon hepsilon16
  obtain ⟨N,V,hN,hV,hq,hfamily⟩ := hfamily epsilon hepsilon
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro n hn
  obtain ⟨K,hK,hbound,hrel,hzero,hmatch,herror⟩ := hfamily n hn
  refine ⟨K,hK,hbound,hrel,hzero,hmatch,herror,?_⟩
  intro a ha
  let c : ℝ := Real.pi*(n : ℕ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hf : AnalyticOnNhd ℂ (fun z => K (z,a)) (closedBall ((c : ℂ)^2) (c*r)) := by
    intro z hz
    exact (hK (z,a) ⟨by simpa [hillHminusGapSquareDisc,classicalHillGapSquareDisc,c] using hz,ha⟩).comp
      (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
  have he : ∀ z ∈ sphere ((c : ℂ)^2) (c*r),
      ‖K (z,a)- (-(z-(c : ℂ)^2)^2/(4*(c : ℂ)^2))‖ ≤ r^2/16 := by
    intro z hz
    have hh := herror (z,a) ⟨by
      simpa [hillHminusGapSquareDisc,classicalHillGapSquareDisc,c] using sphere_subset_closedBall hz,ha⟩
    have hh' : ‖K (z,a)-classicalHillFreeQuadraticModel n z‖ ≤ r^2/16 :=
      hh.trans (by nlinarith [sq_nonneg r])
    simpa [classicalHillFreeQuadraticModel,c] using hh'
  have hcount := analyticZeroCount_eq_two_of_quadratic_model c r hc hr _ hf he
  refine ⟨by simpa [hillHminusGapSquareDisc,classicalHillGapSquareDisc,c] using hcount,?_⟩
  obtain ⟨l,hl,u,hu,hfl,hfu,hm,hzeros⟩ := exists_two_zeros_of_quadratic_model c r hc hr _ hf he
  have hl' : l ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) := by simpa [c] using hl
  have hu' : u ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) := by simpa [c] using hu
  have hlK : l ∈ hillHminusGapSquareDisc n r := ball_subset_closedBall hl'
  have huK : u ∈ hillHminusGapSquareDisc n r := ball_subset_closedBall hu'
  have hmult (z : ℂ) (hz : z ∈ hillHminusGapSquareDisc n r) :
      analyticOrderNatAt (fun w => K (w,a)) z = ({l,u} : Multiset ℂ).count z := by
    have hh := hm z
    have hz' : z ∈ closedBall ((c : ℂ)^2) (c*r) := by
      simpa [hillHminusGapSquareDisc,classicalHillGapSquareDisc,c] using hz
    simpa only [if_pos hz'] using hh
  have hiff (z : ℂ) (hz : z ∈ hillHminusGapSquareDisc n r) :
      K (z,a) = 0 ↔ z = l ∨ z = u := hzeros z (by
        simpa [hillHminusGapSquareDisc,classicalHillGapSquareDisc,c] using hz)
  have horder (z : ℂ) (hz : z ∈ hillHminusGapSquareDisc n r) :
      analyticOrderNatAt (fun w => K (w,a)) z =
        analyticOrderNatAt (fun w => hillHminusRadicand a w) z := by
    by_cases hz0 : K (z,a) = 0
    · have hzball : z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) := by
        rcases (hiff z hz).mp hz0 with rfl | rfl <;> assumption
      exact hillHminus_square_order_on_disc n r V hV K hK hrel a ha z hzball hz0
    · have hr0 : hillHminusRadicand a z ≠ 0 := fun hh => hz0 ((hzero (z,a) ⟨hz,ha⟩).mpr hh)
      have hkorder : analyticOrderAt (fun w => K (w,a)) z = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr hz0)
      have hrorder : analyticOrderAt (fun w => hillHminusRadicand a w) z = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr hr0)
      exact congrArg ENat.toNat (hkorder.trans hrorder.symm)
  have hlevel (z : ℂ) (hz : z ∈ hillHminusGapSquareDisc n r) (hz0 : K (z,a) = 0) :
      hillHminusDiscriminant a z = 2*(-1 : ℂ)^(n : ℕ) := by
    have hh := hrel (z,a) ⟨hz,ha⟩
    rw [hz0,squaredCosh_zero] at hh
    have hsign : ((-1 : ℂ)^(n : ℕ))^2 = 1 := by rw [pow_two,← mul_pow]; simp
    linear_combination -2*(-1 : ℂ)^(n : ℕ)*hh-hillHminusDiscriminant a z*hsign
  refine ⟨l,u,⟨hl',hu',(hzero (l,a) ⟨hlK,ha⟩).mp hfl,(hzero (u,a) ⟨huK,ha⟩).mp hfu,
    ?_,?_,hlevel l hlK hfl,hlevel u huK hfu⟩,hmult⟩
  · intro z hz
    rw [← hzero (z,a) ⟨hz,ha⟩]
    exact hiff z hz
  · intro z hz
    rw [← horder z hz]
    exact hmult z hz

theorem exists_hillHminus_high_gap_pairs (q : PeriodOneHminusOne) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V, ‖K t‖ < 1) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V,
          squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant t.2 t.1/2) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V,
          K t = 0 ↔ hillHminusRadicand t.2 t.1 = 0) ∧
        (∀ t ∈ (hillHminusGapSquareDisc n r ×ˢ V) ∩ hillHminusContinuationDomain,
          K t = (hillHminusContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
        ∀ a ∈ V, analyticZeroCount (fun z => K (z,a)) (hillHminusGapSquareDisc n r) = 2 ∧
          ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
            ∀ z ∈ hillHminusGapSquareDisc n r,
              analyticOrderNatAt (fun w => K (w,a)) z = ({l,u} : Multiset ℂ).count z := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := exists_hillHminus_quadratic_square_pairs q
  obtain ⟨N,V,hN,hV,hq,hfamily⟩ := hfamily (1/16) (by norm_num) le_rfl
  refine ⟨r,N,V,hr,hrpi,hN,hV,hq,?_⟩
  intro n hn
  obtain ⟨K,hK,hbound,hrel,hzero,hmatch,_,hpairs⟩ := hfamily n hn
  exact ⟨K,hK,hbound,hrel,hzero,hmatch,hpairs⟩

end NLS.KdV
