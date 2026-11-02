import NLS.KdV.HillHminusOnePhysicalCut

/-! # A common H^-1 neighborhood for physically normalized high cuts

For every real input in one complex neighborhood, all sufficiently high
cut roots match the actual source primitive on the complete integration
circle. Their strict half-plane signs and real filled squares are proved
on the same discs, including collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_physical_high_cuts (q : PeriodOneHminusOne) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set (PeriodOneHminusOne),
      0 < r ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ a ∈ V, IsRealPeriodOneHminusOne a →
        ∃ l u : ℝ, ∃ K B : ℂ → ℂ,
          HillHminusHighGapPair a n r (l : ℂ) (u : ℂ) ∧
          AnalyticOnNhd ℂ K (hillHminusGapSquareDisc n r) ∧
          AnalyticOnNhd ℂ B
            (ball (freeHillValue (n : ℕ) : ℂ) (Real.pi*(n : ℕ)*r) \
              segment ℝ (l : ℂ) (u : ℂ)) ∧
          (∀ z ∈ ball (freeHillValue (n : ℕ) : ℂ) (Real.pi*(n : ℕ)*r) \
              segment ℝ (l : ℂ) (u : ℂ), B z ≠ 0 ∧ B z^2 = K z) ∧
          (∀ z ∈ sphere (freeHillValue (n : ℕ) : ℂ) (Real.pi*(n : ℕ)*r/4),
            B z = hillHminusContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi) ∧
          (∀ z ∈ ball (freeHillValue (n : ℕ) : ℂ) (Real.pi*(n : ℕ)*r),
            0 < z.im → 0 < (B z).re) ∧
          (∀ z ∈ ball (freeHillValue (n : ℕ) : ℂ) (Real.pi*(n : ℕ)*r),
            z.im < 0 → (B z).re < 0) ∧
          (∀ x : ℝ, (x : ℂ) ∈ ball (freeHillValue (n : ℕ) : ℂ) (Real.pi*(n : ℕ)*r) →
            (K (x : ℂ)).im = 0) ∧
          (l = u → AnalyticOnNhd ℂ B
            (ball (freeHillValue (n : ℕ) : ℂ) (Real.pi*(n : ℕ)*r))) := by
  obtain ⟨r,_,Nk,Vk,hr,hrpi,_,hNk,hVk,hqk,hfamily⟩ := exists_hillHminus_gap_cut_roots q
  let rho : ℝ := Real.pi*r/4
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hrho1 : rho ≤ 1 := by
    have hs : Real.pi^2 < 16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
    dsimp only [rho]
    nlinarith [mul_le_mul_of_nonneg_left hrpi Real.pi_pos.le]
  obtain ⟨Nm,Vm,_,hVm,hqm,hcover,_⟩ :=
    exists_hillHminus_high_power_period_radius_independence q rho hrho
  refine ⟨r,max Nk Nm,Vk ∩ Vm,hr,hNk.trans_le (le_max_left _ _),hVk.inter hVm,⟨hqk,hqm⟩,?_⟩
  intro n hn a ha hreal
  have hnk : Nk ≤ (n : ℕ) := (le_max_left Nk Nm).trans hn
  have hnm : Nm ≤ (n : ℕ) := (le_max_right Nk Nm).trans hn
  obtain ⟨K,hK,hmatch,hpairs⟩ := hfamily n hnk
  obtain ⟨l,u,B,hpair,hl,hu,_,hB,hsq,hcollapsed,_⟩ := hpairs a ha.1
  obtain ⟨hli,hui⟩ := HillHminusHighGapPair.im_eq_zero hreal hpair
  have hel : (l.re : ℂ) = l := by apply Complex.ext <;> simp [hli]
  have heu : (u.re : ℂ) = u := by apply Complex.ext <;> simp [hui]
  let c : ℝ := freeHillValue (n : ℕ)
  let R : ℝ := Real.pi*(n : ℕ)*r
  have hR : 0 < R := by dsimp only [R]; positivity
  have hcenter : ((Real.pi : ℂ)*(n : ℕ))^2 = (c : ℂ) := by
    dsimp only [c,freeHillValue]
    push_cast
    ring
  have hrad : rho*(n : ℝ) = R/4 := by dsimp only [rho,R]; ring
  have hradn : R/4 ≤ (n : ℝ) := by
    rw [← hrad]
    exact mul_le_of_le_one_left (by positivity) hrho1
  have hB' : AnalyticOnNhd ℂ B (ball (c : ℂ) R \ segment ℝ (l.re : ℂ) (u.re : ℂ)) := by
    simpa only [hel,heu,hcenter,R] using hB
  have hsq' : ∀ z ∈ ball (c : ℂ) R \ segment ℝ (l.re : ℂ) (u.re : ℂ),
      B z ≠ 0 ∧ B z^2 = K (z,a) := by simpa only [hel,heu,hcenter,R] using hsq
  have hmatch' (z : ℂ) (hz : z ∈ closedBall (c : ℂ) R)
      (hd : (z,a) ∈ hillHminusContinuationDomain) :
      K (z,a) = (hillHminusContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi)^2 := by
    exact hmatch (z,a) ⟨⟨by
      simpa only [hillHminusGapSquareDisc,classicalHillGapSquareDisc,hcenter,R] using hz,ha.1⟩,hd⟩
  have hsource (z : ℂ) (hz : z ∈ sphere (c : ℂ) (R/4)) : (z,a) ∈ hillHminusContinuationDomain := by
    apply hcover a ha.2 n hnm z
      (closedBall_subset_closedBall hradn (sphere_subset_closedBall hz))
    have he : ‖z-(c : ℂ)‖ = R/4 := by simpa only [mem_sphere,dist_eq_norm] using hz
    simpa only [c,hrad,he] using (le_rfl : R/4 ≤ R/4)
  obtain ⟨k,hk,hcircle,hupper,hlower⟩ := exists_hillHminus_physical_cut_sign a hreal n c
    l.re u.re R (fun z => K (z,a)) B hR
    (by simpa only [hel,hcenter,R] using hl) (by simpa only [heu,hcenter,R] using hu)
    hB' hsq' hmatch' hsource
  have hk2 : k^2 = 1 := by rcases hk with rfl | rfl <;> norm_num
  have hkne : k ≠ 0 := by intro he; rw [he] at hk2; norm_num at hk2
  have hKa : AnalyticOnNhd ℂ (fun z => K (z,a)) (hillHminusGapSquareDisc n r) := by
    intro z hz
    exact (hK (z,a) ⟨hz,ha.1⟩).comp
      (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
  refine ⟨l.re,u.re,(fun z => K (z,a)),(fun z => k*B z),?_,hKa,?_,?_,hcircle,hupper,hlower,?_,?_⟩
  · simpa only [hel,heu] using hpair
  · exact analyticOnNhd_const.mul hB'
  · intro z hz
    refine ⟨mul_ne_zero hkne (hsq' z hz).1,?_⟩
    rw [mul_pow,hk2,one_mul,(hsq' z hz).2]
  · intro x hx
    apply hillHminus_filled_square_real a hreal n c R x (fun z => K (z,a))
    · intro z hz
      exact hKa z (by
        simpa only [hillHminusGapSquareDisc,classicalHillGapSquareDisc,hcenter,R] using ball_subset_closedBall hz)
    · exact hx
    · intro z hz hi
      exact hmatch' z (ball_subset_closedBall hz)
        (mem_hillHminusContinuationDomain_of_im_ne_zero a hreal z hi)
  · intro he
    have hlu : l = u := by rw [← hel,← heu,he]
    have hh : AnalyticOnNhd ℂ B (ball (c : ℂ) R) := by
      simpa only [hcenter,R] using hcollapsed hlu
    exact analyticOnNhd_const.mul hh

end NLS.KdV
