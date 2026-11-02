import NLS.KdV.HillL2GapScaleBounds
import NLS.ComplexAnalysis.AnalyticTwoZeroRoot

/-! # Actual L2 Hill cut roots with uniform gap-length bounds

The actual filled endpoint quotient produces an analytic square root
off the entire straight complex gap. Collapsed gaps extend through the
endpoint. Local source matching fixes the physical sign as a germ.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

/-- At any admissible regular anchor, one of the two analytic cut roots
agrees as a germ with the actual free-normalized shifted primitive.
This does not assert the same sign on disconnected overlap components. -/
theorem exists_hillL2_cut_root_local_sign
    (a : Coeff 2) (n : ℕ+) (B : ℂ → ℂ) (U : Set ℂ) (z : ℂ)
    (hU : IsOpen U) (hz : z ∈ U) (hdom : (z,a) ∈ hillL2ContinuationDomain)
    (hB : AnalyticOnNhd ℂ B U) (hBne : B z ≠ 0)
    (hsq : ∀ w ∈ U, (w,a) ∈ hillL2ContinuationDomain →
      B w^2 = (hillL2ContinuedPrimitive (w,a)+I*(n : ℂ)*Real.pi)^2) :
    ∃ k : ℂ, (k = 1 ∨ k = -1) ∧
      (fun w => k*B w) =ᶠ[𝓝 z]
        (fun w => hillL2ContinuedPrimitive (w,a)+I*(n : ℂ)*Real.pi) := by
  let F : ℂ → ℂ := fun w => hillL2ContinuedPrimitive (w,a)+I*(n : ℂ)*Real.pi
  have hF : AnalyticAt ℂ F z :=
    ((analyticOnNhd_hillL2ContinuedPrimitive (z,a) hdom).comp
      (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)).add analyticAt_const
  have hsqnear : (fun w => B w^2) =ᶠ[𝓝 z] (fun w => F w^2) := by
    have hd : ∀ᶠ w in 𝓝 z, (w,a) ∈ hillL2ContinuationDomain :=
      ((continuous_id.prodMk continuous_const).tendsto z).eventually
        (isOpen_hillL2ContinuationDomain.mem_nhds hdom)
    filter_upwards [hU.mem_nhds hz,hd] with w hw hwd
    exact hsq w hw hwd
  have hFne : F z ≠ 0 := by
    intro he
    have hh := hsqnear.eq_of_nhds
    rw [he,zero_pow (by norm_num : 2 ≠ 0)] at hh
    exact hBne (sq_eq_zero_iff.mp hh)
  rcases eq_or_eq_neg_of_sq_eq_sq (B z) (F z) hsqnear.eq_of_nhds with he | he
  · refine ⟨1,Or.inl rfl,?_⟩
    simpa only [one_mul] using eventuallyEq_of_sq_eq_of_continuousAt B F z
      (hB z hz).continuousAt hF.continuousAt he hFne hsqnear
  · refine ⟨-1,Or.inr rfl,?_⟩
    have hb : -B z = F z := by rw [he,neg_neg]
    have hh := eventuallyEq_of_sq_eq_of_continuousAt (fun w => -B w) F z
      (hB z hz).continuousAt.neg hF.continuousAt hb hFne (by
        filter_upwards [hsqnear] with w hw
        simpa only [neg_sq] using hw)
    simpa only [neg_one_mul] using hh

theorem exists_hillL2_gap_cut_roots (q : Coeff 2) :
    ∃ r C : ℝ, ∃ N : ℕ, ∃ V : Set (Coeff 2),
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < C ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ K (hillL2GapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ (hillL2GapSquareDisc n r ×ˢ V) ∩ hillL2ContinuationDomain,
          K t = (hillL2ContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
        ∀ a ∈ V, ∃ l u : ℂ, ∃ B : ℂ → ℂ,
          HillL2HighGapPair a n l u ∧
          l ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/32) ∧
          u ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/32) ∧
          closedBall ((l+u)/2) ‖l-u‖ ⊆
            ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ∧
          AnalyticOnNhd ℂ B
            (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u) ∧
          (∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) \ segment ℝ l u,
            B z ≠ 0 ∧ B z^2 = K (z,a)) ∧
          (l = u → AnalyticOnNhd ℂ B
            (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r))) ∧
          ∀ z ∈ closedBall ((l+u)/2) ‖l-u‖ \ segment ℝ l u,
            ‖B z‖ ≤ C*‖l-u‖/(n : ℕ) := by
  obtain ⟨r,N,V,hr,hrpi,hN,hV,hq,hfamily⟩ := exists_hillL2_gap_quotient_bounds q
  let C : ℝ := 3/(Real.pi*r)
  refine ⟨r,C,N,V,hr,hrpi,by dsimp only [C]; positivity,hN,hV,hq,?_⟩
  intro n hn
  obtain ⟨K,hK,_,_,hmatch,hpairs⟩ := hfamily n hn
  refine ⟨K,hK,hmatch,?_⟩
  intro a ha
  obtain ⟨l,u,hpair,hl,hu,hQ,hfactor,hunit,hbound⟩ := hpairs a ha
  let c : ℂ := ((Real.pi : ℂ)*(n : ℕ))^2
  let R : ℝ := Real.pi*(n : ℕ)*r
  have hR : 0 < R := by dsimp only [R]; positivity
  have hQball : AnalyticOnNhd ℂ (twoZeroQuotient (fun z => K (z,a)) l u) (ball c R) :=
    hQ.mono ball_subset_closedBall
  obtain ⟨B,hB,hBsq,hBcollapsed⟩ := exists_analytic_squareRoot_on_two_zero_cut
    (fun z => K (z,a)) (twoZeroQuotient (fun z => K (z,a)) l u) l u c R hR
      hQball hunit (fun z _ => hfactor z)
  have hl' : ‖l-c‖ ≤ R/8 := by
    have hh : ‖l-c‖ < R/32 := by simpa only [mem_ball,dist_eq_norm] using hl
    linarith
  have hu' : ‖u-c‖ ≤ R/8 := by
    have hh : ‖u-c‖ < R/32 := by simpa only [mem_ball,dist_eq_norm] using hu
    linarith
  have hsub := closed_gap_ball_subset_energy_ball l u c R hR hl' hu'
  refine ⟨l,u,B,hpair,hl,hu,hsub,hB,hBsq,hBcollapsed,?_⟩
  intro z hz
  have hzin := hsub hz.1
  have hk := norm_two_zero_square_on_gap_ball (fun z => K (z,a))
    (twoZeroQuotient (fun z => K (z,a)) l u) l u z R (hfactor z)
    (hbound z (ball_subset_closedBall hzin)) hz.1
  have hb := norm_le_gap_scale_of_square_bound (B z) (K (z,a)) ‖l-u‖ R
    (norm_nonneg _) hR (hBsq z ⟨hzin,hz.2⟩).2 hk
  calc
    _ ≤ 3*‖l-u‖/R := hb
    _ = C*‖l-u‖/(n : ℕ) := by
      have hnpos : (0 : ℝ) < (n : ℕ) := by positivity
      dsimp only [C,R]
      field_simp [Real.pi_ne_zero,hr.ne',hnpos.ne']

end NLS.KdV
