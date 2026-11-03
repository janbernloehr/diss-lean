import NLS.KdV.HillHminusOneHighGapPairs
import NLS.KdV.HillHminusOneSmallGapCoverage
import NLS.ComplexAnalysis.TwoZeroDeflation

/-! # Uniform endpoint-deflated actual Hill squares in H^-1

Actual high endpoints and their exact multiplicities give a filled
analytic quotient. It is nonzero on the full open energy disc and has
the bound 4/(n*pi*r)^2 uniformly on one complex H^-1 neighborhood.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillHminusHighGapPair.squared_primitive_multiplicity
    {q : PeriodOneHminusOne} {n : ℕ+} {rho : ℝ} {l r : ℂ} (h : HillHminusHighGapPair q n rho l r)
    (lambda : ℂ) (hlambda : lambda ∈ hillHminusGapSquareDisc n rho)
    (sigma : ℂ) (hsigma : sigma^2 = 1) (K : ℂ × PeriodOneHminusOne → ℂ)
    (hK : AnalyticAt ℂ K (lambda,q)) (hK0 : K (lambda,q) = 0)
    (hrel : (fun t => squaredCosh (K t)) =ᶠ[𝓝 (lambda,q)]
      (fun t => sigma*hillHminusDiscriminant t.2 t.1/2)) :
    analyticOrderNatAt (fun z => K (z,q)) lambda = ({l,r} : Multiset ℂ).count lambda := by
  rw [hillHminus_squared_primitive_energy_order (lambda,q) sigma hsigma K hK hK0 hrel]
  exact h.multiplicity lambda hlambda

theorem exists_hillHminus_gap_quotient_bounds (q : PeriodOneHminusOne) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set (PeriodOneHminusOne),
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V,
          squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant t.2 t.1/2) ∧
        (∀ t ∈ hillHminusGapSquareDisc n r ×ˢ V,
          K t = 0 ↔ hillHminusRadicand t.2 t.1 = 0) ∧
        (∀ t ∈ (hillHminusGapSquareDisc n r ×ˢ V) ∩ hillHminusContinuationDomain,
          K t = (hillHminusContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
        ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u ∧
          l ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/32) ∧
          u ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/32) ∧
          AnalyticOnNhd ℂ (twoZeroQuotient (fun z => K (z,a)) l u) (hillHminusGapSquareDisc n r) ∧
          (∀ z, K (z,a) = (z-l)*(z-u)*twoZeroQuotient (fun z => K (z,a)) l u z) ∧
          (∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
            twoZeroQuotient (fun z => K (z,a)) l u z ≠ 0) ∧
          ∀ z ∈ hillHminusGapSquareDisc n r,
            ‖twoZeroQuotient (fun z => K (z,a)) l u z‖ ≤ 4/(Real.pi*(n : ℕ)*r)^2 := by
  obtain ⟨r,Nk,Vk,hr,hrpi,hNk,hVk,hqk,hfamily⟩ := exists_hillHminus_high_gap_pairs q
  obtain ⟨Nr,Vr,_,hVr,hqr,hcover⟩ := exists_hillHminus_small_gap_coverage q (r/128)
    (by positivity)
  let N := max Nk Nr
  let V := Vk ∩ Vr
  refine ⟨r,N,V,hr,hrpi,hNk.trans_le (le_max_left _ _),hVk.inter hVr,⟨hqk,hqr⟩,?_⟩
  intro n hn
  have hnk : Nk ≤ (n : ℕ) := (le_max_left Nk Nr).trans hn
  have hnr : Nr ≤ (n : ℕ) := (le_max_right Nk Nr).trans hn
  obtain ⟨K,hK,hbound,hrel,hzero,hmatch,hpairs⟩ := hfamily n hnk
  have hsub : hillHminusGapSquareDisc n r ×ˢ V ⊆ hillHminusGapSquareDisc n r ×ˢ Vk :=
    fun _ ht => ⟨ht.1,ht.2.1⟩
  refine ⟨K,hK.mono hsub,fun t ht => hrel t (hsub ht),fun t ht => hzero t (hsub ht),
    fun t ht => hmatch t ⟨hsub ht.1,ht.2⟩,?_⟩
  intro a ha
  obtain ⟨_,l,u,hpair,hmult⟩ := hpairs a ha.1
  let c : ℂ := ((Real.pi : ℂ)*(n : ℕ))^2
  let R : ℝ := Real.pi*(n : ℕ)*r
  have hR : 0 < R := by dsimp only [R]; positivity
  have hrc : r/32 ≤ Real.pi*(n : ℕ) := by
    have hnreal : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.property
    nlinarith [Real.pi_pos]
  have endpoint_mem (lambda : ℂ) (hlambda : lambda ∈ hillHminusGapSquareDisc n r)
      (hz : hillHminusRadicand a lambda = 0) : lambda ∈ ball c (R/32) := by
    let z : ℂ := Complex.sqrt lambda
    have hzsq : z^2 = lambda := complex_sqrt_sq lambda
    have hzball : z ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) := by
      have hh := sqrt_mem_closedBall_of_energy_disc (Real.pi*(n : ℕ)) r (by positivity) lambda
        (by simpa only [hillHminusGapSquareDisc,classicalHillGapSquareDisc,ofReal_mul,ofReal_natCast] using hlambda)
      exact closedBall_subset_closedBall hrpi (by simpa only [ofReal_mul,ofReal_natCast] using hh)
    have hzsmall := hcover a ha.2 (n : ℕ) hnr z hzball (by simpa only [hzsq] using hz)
    have h := square_mem_energy_ball_of_small_frequency (Real.pi*(n : ℕ)) (r/32)
      (by positivity) (by positivity) hrc z (by
        simpa only [ofReal_mul,ofReal_natCast,show (r/32)/4 = r/128 by ring] using hzsmall)
    simpa only [c,R,hzsq,ofReal_mul,ofReal_natCast,mul_div_assoc] using h
  have hl := endpoint_mem l (ball_subset_closedBall hpair.left_mem) hpair.left_zero
  have hu := endpoint_mem u (ball_subset_closedBall hpair.right_mem) hpair.right_zero
  have hlhalf : l ∈ closedBall c (R/2) :=
    ball_subset_closedBall (ball_subset_ball (by linarith : R/32 ≤ R/2) hl)
  have huhalf : u ∈ closedBall c (R/2) :=
    ball_subset_closedBall (ball_subset_ball (by linarith : R/32 ≤ R/2) hu)
  have hlball : l ∈ ball c R := ball_subset_ball (by linarith : R/32 ≤ R) hl
  have huball : u ∈ ball c R := ball_subset_ball (by linarith : R/32 ≤ R) hu
  have hla : (l,a) ∈ hillHminusGapSquareDisc n r ×ˢ Vk := ⟨ball_subset_closedBall hlball,ha.1⟩
  have hua : (u,a) ∈ hillHminusGapSquareDisc n r ×ˢ Vk := ⟨ball_subset_closedBall huball,ha.1⟩
  have hfa : K (l,a) = 0 := (hzero (l,a) hla).mpr hpair.left_zero
  have hfb : K (u,a) = 0 := (hzero (u,a) hua).mpr hpair.right_zero
  have hf : AnalyticOnNhd ℂ (fun z => K (z,a)) (closedBall c R) := by
    intro z hz
    exact (hK (z,a) ⟨hz,ha.1⟩).comp (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
  have hdouble : l = u → deriv (fun z => K (z,a)) l = 0 := by
    intro he
    have ho : analyticOrderNatAt (fun z => K (z,a)) l = 2 := by
      simpa [he] using hmult l (ball_subset_closedBall hlball)
    by_contra hd
    have horder := (hf l (ball_subset_closedBall hlball)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hfa hd
    have hone : analyticOrderNatAt (fun z => K (z,a)) l = 1 := congrArg ENat.toNat horder
    omega
  refine ⟨l,u,hpair,hl,hu,analyticOnNhd_twoZeroQuotient _ _ l u hf
    (ball_subset_closedBall hlball) (ball_subset_closedBall huball),
    twoZeroQuotient_factor _ l u hfa hfb hdouble,?_,?_⟩
  · intro z hz
    apply twoZeroQuotient_ne_zero (fun z => K (z,a)) (closedBall c R) l u z hf
      (ball_subset_closedBall hlball) (ball_subset_closedBall huball) (ball_subset_closedBall hz)
      hfa hfb hdouble
    · intro hzeroK
      exact (hpair.zeros_iff z (ball_subset_closedBall hz)).mp ((hzero (z,a) ⟨ball_subset_closedBall hz,ha.1⟩).mp hzeroK)
    · intro hzeroK
      exact hmult z (ball_subset_closedBall hz)
  have hQ := norm_twoZeroQuotient_le (fun z => K (z,a)) l u c R 1 hR hf hlhalf huhalf hfa hfb hdouble
    (fun z hz => (hbound (z,a) ⟨sphere_subset_closedBall hz,ha.1⟩).le)
  simpa only [c,R,hillHminusGapSquareDisc,classicalHillGapSquareDisc,mul_one] using hQ

end NLS.KdV
