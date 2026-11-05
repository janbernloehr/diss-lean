import NLS.KdV.HillL2GapSquareFamilies
import NLS.ComplexAnalysis.TwoZeroDeflation

/-! # Uniform endpoint-deflated actual Hill squares in L2

Actual high endpoints and their exact multiplicities give a filled
analytic quotient. It is nonzero on the full open energy disc and has
the bound 4/(n*pi*r)^2 uniformly on one complex L2 neighborhood.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillL2HighGapPair.squared_primitive_multiplicity
    {q : Coeff 2} {n : ℕ+} {l r : ℂ} (h : HillL2HighGapPair q n l r)
    (lambda : ℂ) (hlambda : lambda ∈ hillL2HighEnergyRegion n)
    (sigma : ℂ) (hsigma : sigma^2 = 1) (K : ℂ × Coeff 2 → ℂ)
    (hK : AnalyticAt ℂ K (lambda,q)) (hK0 : K (lambda,q) = 0)
    (hrel : (fun t => squaredCosh (K t)) =ᶠ[𝓝 (lambda,q)]
      (fun t => sigma*hillL2Discriminant t.2 t.1/2)) :
    analyticOrderNatAt (fun z => K (z,q)) lambda = ({l,r} : Multiset ℂ).count lambda := by
  rw [hillL2_squared_primitive_energy_order (lambda,q) sigma hsigma K hK hK0 hrel]
  exact h.multiplicity lambda hlambda

theorem exists_hillL2_gap_quotient_bounds (q : Coeff 2) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set (Coeff 2),
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ K (hillL2GapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V,
          squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*hillL2Discriminant t.2 t.1/2) ∧
        (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V,
          K t = 0 ↔ hillL2Radicand t.2 t.1 = 0) ∧
        (∀ t ∈ (hillL2GapSquareDisc n r ×ˢ V) ∩ hillL2ContinuationDomain,
          K t = (hillL2ContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
        ∀ a ∈ V, ∃ l u : ℂ, HillL2HighGapPair a n l u ∧
          l ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/32) ∧
          u ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/32) ∧
          AnalyticOnNhd ℂ (twoZeroQuotient (fun z => K (z,a)) l u) (hillL2GapSquareDisc n r) ∧
          (∀ z, K (z,a) = (z-l)*(z-u)*twoZeroQuotient (fun z => K (z,a)) l u z) ∧
          (∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
            twoZeroQuotient (fun z => K (z,a)) l u z ≠ 0) ∧
          ∀ z ∈ hillL2GapSquareDisc n r,
            ‖twoZeroQuotient (fun z => K (z,a)) l u z‖ ≤ 4/(Real.pi*(n : ℕ)*r)^2 := by
  obtain ⟨r,Nk,Vk,hr,hrpi,hNk,hVk,hqk,hfamily⟩ := exists_hillL2_whole_gap_squares q
  obtain ⟨Nr,Vr,_,hVr,hqr,hcover⟩ := exists_hillL2_small_gap_coverage q (r/128)
    (by positivity) (by linarith)
  let N := max Nk Nr
  let V := Vk ∩ Vr
  refine ⟨r,N,V,hr,hrpi,hNk.trans_le (le_max_left _ _),hVk.inter hVr,⟨hqk,hqr⟩,?_⟩
  intro n hn
  have hnk : Nk ≤ (n : ℕ) := (le_max_left Nk Nr).trans hn
  have hnr : Nr ≤ (n : ℕ) := (le_max_right Nk Nr).trans hn
  obtain ⟨K,hK,hbound,hrel,hzero,hmatch,hpairs⟩ := hfamily n hnk
  have hsub : hillL2GapSquareDisc n r ×ˢ V ⊆ hillL2GapSquareDisc n r ×ˢ Vk :=
    fun _ ht => ⟨ht.1,ht.2.1⟩
  refine ⟨K,hK.mono hsub,fun t ht => hrel t (hsub ht),fun t ht => hzero t (hsub ht),
    fun t ht => hmatch t ⟨hsub ht.1,ht.2⟩,?_⟩
  intro a ha
  obtain ⟨l,u,hpair,_⟩ := hpairs a ha.1
  let c : ℂ := ((Real.pi : ℂ)*(n : ℕ))^2
  let R : ℝ := Real.pi*(n : ℕ)*r
  have hR : 0 < R := by dsimp only [R]; positivity
  have hrc : r/32 ≤ Real.pi*(n : ℕ) := by
    have hnreal : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.property
    nlinarith [Real.pi_pos]
  have endpoint_mem (lambda : ℂ) (hlambda : lambda ∈ hillL2HighEnergyRegion n)
      (hz : hillL2Radicand a lambda = 0) : lambda ∈ ball c (R/32) := by
    obtain ⟨z,hzball,hzsq⟩ := hlambda
    change z^2 = lambda at hzsq
    have hzsmall := hcover a ha.2 (n : ℕ) (by simpa only [Int.natAbs_natCast] using hnr) z
      (by simpa only [Int.cast_natCast] using ball_subset_closedBall hzball)
      (by simpa only [hzsq] using hz)
    have h := square_mem_energy_ball_of_small_frequency (Real.pi*(n : ℕ)) (r/32)
      (by positivity) (by positivity) hrc z (by
        simpa only [ofReal_mul,ofReal_natCast,Int.cast_natCast,
          show (r/32)/4 = r/128 by ring] using hzsmall)
    simpa only [c,R,hzsq,ofReal_mul,ofReal_natCast,mul_div_assoc] using h
  have hl := endpoint_mem l hpair.left_mem hpair.left_zero
  have hu := endpoint_mem u hpair.right_mem hpair.right_zero
  have hlhalf : l ∈ closedBall c (R/2) :=
    ball_subset_closedBall (ball_subset_ball (by linarith : R/32 ≤ R/2) hl)
  have huhalf : u ∈ closedBall c (R/2) :=
    ball_subset_closedBall (ball_subset_ball (by linarith : R/32 ≤ R/2) hu)
  have hlball : l ∈ ball c R := ball_subset_ball (by linarith : R/32 ≤ R) hl
  have huball : u ∈ ball c R := ball_subset_ball (by linarith : R/32 ≤ R) hu
  have hla : (l,a) ∈ hillL2GapSquareDisc n r ×ˢ Vk := ⟨ball_subset_closedBall hlball,ha.1⟩
  have hua : (u,a) ∈ hillL2GapSquareDisc n r ×ˢ Vk := ⟨ball_subset_closedBall huball,ha.1⟩
  have hfa : K (l,a) = 0 := (hzero (l,a) hla).mpr hpair.left_zero
  have hfb : K (u,a) = 0 := (hzero (u,a) hua).mpr hpair.right_zero
  have hf : AnalyticOnNhd ℂ (fun z => K (z,a)) (closedBall c R) := by
    intro z hz
    exact (hK (z,a) ⟨hz,ha.1⟩).comp (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
  have hdouble : l = u → deriv (fun z => K (z,a)) l = 0 := by
    intro he
    have hrelg : (fun t => squaredCosh (K t)) =ᶠ[𝓝 (l,a)]
        (fun t => (-1 : ℂ)^(n : ℕ)*hillL2Discriminant t.2 t.1/2) := by
      filter_upwards [(isOpen_ball.prod hVk).mem_nhds ⟨hlball,ha.1⟩] with t ht
      exact hrel t ⟨ball_subset_closedBall ht.1,ht.2⟩
    have hsign : ((-1 : ℂ)^(n : ℕ))^2 = 1 := by rw [pow_two,← mul_pow]; simp
    have ho : analyticOrderNatAt (fun z => K (z,a)) l = 2 := by
      simpa [he] using
        hpair.squared_primitive_multiplicity l hpair.left_mem ((-1 : ℂ)^(n : ℕ)) hsign K
          (hK (l,a) hla) hfa hrelg
    by_contra hd
    have horder := (hf l (ball_subset_closedBall hlball)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hfa hd
    have hone : analyticOrderNatAt (fun z => K (z,a)) l = 1 := congrArg ENat.toNat horder
    omega
  refine ⟨l,u,hpair,hl,hu,analyticOnNhd_twoZeroQuotient _ _ l u hf
    (ball_subset_closedBall hlball) (ball_subset_closedBall huball),
    twoZeroQuotient_factor _ l u hfa hfb hdouble,?_,?_⟩
  · intro z hz
    have hzfreq := sqrt_mem_ball_of_energy_disc (Real.pi*(n : ℕ)) r (by positivity) z
      (by simpa only [ofReal_mul,ofReal_natCast] using hz)
    have hzregion : z ∈ hillL2HighEnergyRegion n := by
      refine ⟨Complex.sqrt z,?_,?_⟩
      · simpa only [ofReal_mul,ofReal_natCast] using ball_subset_ball hrpi hzfreq
      · have he := Complex.cpow_nat_inv_pow z (Nat.succ_ne_zero 1)
        norm_num at he
        simpa only [Complex.sqrt,one_div] using he
    apply twoZeroQuotient_ne_zero (fun z => K (z,a)) (closedBall c R) l u z hf
      (ball_subset_closedBall hlball) (ball_subset_closedBall huball) (ball_subset_closedBall hz)
      hfa hfb hdouble
    · intro hzeroK
      exact (hpair.zeros_iff z hzregion).mp ((hzero (z,a) ⟨ball_subset_closedBall hz,ha.1⟩).mp hzeroK)
    · intro hzeroK
      have hrelg : (fun t => squaredCosh (K t)) =ᶠ[𝓝 (z,a)]
          (fun t => (-1 : ℂ)^(n : ℕ)*hillL2Discriminant t.2 t.1/2) := by
        filter_upwards [(isOpen_ball.prod hVk).mem_nhds ⟨hz,ha.1⟩] with t ht
        exact hrel t ⟨ball_subset_closedBall ht.1,ht.2⟩
      have hsign : ((-1 : ℂ)^(n : ℕ))^2 = 1 := by rw [pow_two,← mul_pow]; simp
      exact hpair.squared_primitive_multiplicity z hzregion ((-1 : ℂ)^(n : ℕ)) hsign K
        (hK (z,a) ⟨ball_subset_closedBall hz,ha.1⟩) hzeroK hrelg
  have hQ := norm_twoZeroQuotient_le (fun z => K (z,a)) l u c R 1 hR hf hlhalf huhalf hfa hfb hdouble
    (fun z hz => (hbound (z,a) ⟨sphere_subset_closedBall hz,ha.1⟩).le)
  simpa only [c,R,hillL2GapSquareDisc,classicalHillGapSquareDisc,mul_one] using hQ

end NLS.KdV
