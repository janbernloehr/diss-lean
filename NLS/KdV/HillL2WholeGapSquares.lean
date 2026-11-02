import NLS.KdV.HillL2PrimitiveStrip
import NLS.KdV.ClassicalHillWholeGapSquares

/-! # Actual analytic squared Hill primitives on full high L2 discs

The squared-cosh inverse fills every complete high energy disc, with
joint energy and L2-potential analyticity. Source-strip normalization
identifies the filled function with the square of the actual shifted
primitive wherever source continuation is admissible. No simple-root
hypothesis is imposed, so multiple branch points are included.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

/-- The same literal energy disc used in the continuous theory. -/
abbrev hillL2GapSquareDisc (n : ℕ+) (r : ℝ) : Set ℂ := classicalHillGapSquareDisc n r

/-- A single inverse and a common complex potential neighborhood give
one analytic square on every complete high energy disc. The actual
shifted primitive agrees wherever its source continuation is admissible. -/
theorem exists_hillL2_whole_disc_small_squares (q : Coeff 2) (B : ℝ) (hB : 0 < B) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set (Coeff 2),
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ K (hillL2GapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V, ‖K t‖ < B) ∧
        (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V,
          squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*hillL2Discriminant t.2 t.1/2) ∧
        (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V,
          K t = 0 ↔ hillL2Radicand t.2 t.1 = 0) ∧
        ∀ t ∈ (hillL2GapSquareDisc n r ×ˢ V) ∩ hillL2ContinuationDomain,
          K t = (hillL2ContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2 := by
  obtain ⟨U,W,hU,hW,h0,h1,G,hG,hG1,hleft,hright⟩ := exists_squaredCosh_inverse
  have hpre : IsOpen ((fun z : ℂ => z^2) ⁻¹' U) := hU.preimage (continuous_id.pow 2)
  have h0pre : (0 : ℂ) ∈ (fun z : ℂ => z^2) ⁻¹' U := by simpa using h0
  obtain ⟨epsilon,hepsilon,hsmallU⟩ := Metric.mem_nhds_iff.mp (hpre.mem_nhds h0pre)
  obtain ⟨d,hd,hcontrol⟩ := exists_delta_cosh_strip_control epsilon hepsilon
  obtain ⟨eta,heta,hsmallW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h1)
  obtain ⟨etaG,hetaG,hsmallG⟩ := Metric.continuousAt_iff.mp
    ((hG 1 h1).continuousAt : ContinuousAt G (1 : ℂ)) B hB
  let delta : ℝ := min 1 (min d (min eta etaG))
  have hdelta : 0 < delta := lt_min (by norm_num) (lt_min hd (lt_min heta hetaG))
  have hdelta1 : delta ≤ 1 := min_le_left _ _
  have hdeltad : delta ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaeta : delta ≤ eta :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaG : delta ≤ etaG :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨r,Nt,Vt,hr,hrpi,hNt,hVt,hqt,htrace⟩ :=
    exists_hillL2_small_disc_normalized_trace q delta hdelta
  obtain ⟨Ns,Vs,_,hVs,hqs,hstrip⟩ := exists_hillL2_high_primitive_strip q
  refine ⟨r,max Nt Ns,Vt ∩ Vs,hr,hrpi,hNt.trans_le (le_max_left _ _),
    hVt.inter hVs,⟨hqt,hqs⟩,?_⟩
  intro n hn
  let D : ℂ × Coeff 2 → ℂ := fun t => (-1 : ℂ)^(n : ℕ)*hillL2Discriminant t.2 t.1/2
  let K : ℂ × Coeff 2 → ℂ := G ∘ D
  have hD : AnalyticOnNhd ℂ D univ :=
    (analyticOnNhd_const.mul analyticOnNhd_hillL2Discriminant_joint).div_const
  have hfreq (t : ℂ × Coeff 2) (ht : t ∈ hillL2GapSquareDisc n r ×ˢ (Vt ∩ Vs)) :
      Complex.sqrt t.1 ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) r := by
    have hc : (0 : ℝ) < Real.pi*(n : ℕ) := by positivity
    have h := sqrt_mem_closedBall_of_energy_disc (Real.pi*(n : ℕ)) r hc t.1
      (by simpa only [hillL2GapSquareDisc,classicalHillGapSquareDisc,ofReal_mul,ofReal_natCast] using ht.1)
    simpa only [ofReal_mul,ofReal_natCast] using h
  have hnorm (t : ℂ × Coeff 2) (ht : t ∈ hillL2GapSquareDisc n r ×ˢ (Vt ∩ Vs)) :
      ‖D t-1‖ < delta := by
    have h := htrace t.2 ht.2.1 1 (by constructor <;> norm_num) n
      ((le_max_left Nt Ns).trans hn) (Complex.sqrt t.1) (hfreq t ht)
    simpa only [D,ofReal_one,one_smul,complex_sqrt_sq] using h
  have hDW (t : ℂ × Coeff 2) (ht : t ∈ hillL2GapSquareDisc n r ×ˢ (Vt ∩ Vs)) : D t ∈ W := by
    apply hsmallW
    simpa only [mem_ball,dist_eq_norm] using (hnorm t ht).trans_le hdeltaeta
  refine ⟨K,?_,?_,?_,?_,?_⟩
  · intro t ht
    exact (hG (D t) (hDW t ht)).comp (hD t (mem_univ _))
  · intro t ht
    have h := hsmallG (by simpa only [dist_eq_norm] using (hnorm t ht).trans_le hdeltaG)
    simpa only [K,Function.comp_def,hG1,dist_zero_right] using h
  · intro t ht
    exact (hright (D t) (hDW t ht)).2
  · intro t ht
    have hsign : ((-1 : ℂ)^(n : ℕ))^2 = 1 := by rw [pow_two,← mul_pow]; simp
    constructor
    · intro hz
      have hrel : squaredCosh (K t) = D t := (hright (D t) (hDW t ht)).2
      rw [hz,squaredCosh_zero] at hrel
      change (1 : ℂ) = (-1 : ℂ)^(n : ℕ)*hillL2Discriminant t.2 t.1/2 at hrel
      have hvalue : hillL2Discriminant t.2 t.1 = 2*(-1 : ℂ)^(n : ℕ) := by
        linear_combination -2*(-1 : ℂ)^(n : ℕ)*hrel-hillL2Discriminant t.2 t.1*hsign
      change hillL2Discriminant t.2 t.1^2-4 = 0
      rw [hvalue,mul_pow,hsign]
      norm_num
    · intro hz
      have hroot : D t^2 = (1 : ℂ)^2 := by
        have hzero : hillL2Discriminant t.2 t.1^2 = 4 := sub_eq_zero.mp hz
        dsimp only [D]
        rw [div_pow,mul_pow,hsign,hzero]
        norm_num
      rcases eq_or_eq_neg_of_sq_eq_sq _ _ hroot with he | he
      · change G (D t) = 0
        rw [he,hG1]
      · have h := hnorm t ht
        rw [he] at h
        norm_num at h
        linarith
  · intro t ht
    have hF : |(hillL2ContinuedPrimitive t+I*(n : ℂ)*Real.pi).im| < Real.pi/2 := by
      have hz : Complex.sqrt t.1 ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) :=
        closedBall_subset_closedBall hrpi (hfreq t ht.1)
      have h := hstrip t.2 ht.1.2.2 n ((le_max_right Nt Ns).trans hn) (Complex.sqrt t.1) hz
        (by simpa only [complex_sqrt_sq] using ht.2)
      simpa only [complex_sqrt_sq] using h
    have hcosh : cosh (hillL2ContinuedPrimitive t+I*(n : ℂ)*Real.pi) = D t := by
      rw [cosh_add_hill_index]
      have h := (hillL2ContinuedPrimitive_trace t ht.2).1
      dsimp only [D]
      linear_combination (-1 : ℂ)^(n : ℕ)*h/2
    have hnormF := hcontrol _ hF (by rw [hcosh]; exact (hnorm t ht.1).trans_le hdeltad)
    have hFU : (hillL2ContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2 ∈ U := by
      exact hsmallU (by simpa only [mem_ball,dist_zero_right] using hnormF)
    change G (D t) = _
    rw [← hcosh,← squaredCosh_sq]
    exact hleft _ hFU

/-- Unit-bounded version of the arbitrarily small whole-disc square
construction, retained for the endpoint deflation and contour bounds. -/
theorem exists_hillL2_whole_disc_squares (q : Coeff 2) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set (Coeff 2),
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ K (hillL2GapSquareDisc n r ×ˢ V) ∧
        (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V, ‖K t‖ < 1) ∧
        (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V,
          squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*hillL2Discriminant t.2 t.1/2) ∧
        (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V,
          K t = 0 ↔ hillL2Radicand t.2 t.1 = 0) ∧
        ∀ t ∈ (hillL2GapSquareDisc n r ×ˢ V) ∩ hillL2ContinuationDomain,
          K t = (hillL2ContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2 :=
  exists_hillL2_whole_disc_small_squares q 1 (by norm_num)

/-- The normalized square has exactly the physical radicand's analytic
energy order, including multiple zeros. No nonzero energy derivative of
the chart is needed. -/
theorem hillL2_squared_primitive_energy_order
    (p : ℂ × Coeff 2) (sigma : ℂ) (hsigma : sigma^2 = 1)
    (K : ℂ × Coeff 2 → ℂ) (hK : AnalyticAt ℂ K p) (hK0 : K p = 0)
    (hrel : (fun t => squaredCosh (K t)) =ᶠ[𝓝 p]
      (fun t => sigma*hillL2Discriminant t.2 t.1/2)) :
    analyticOrderNatAt (fun z => K (z,p.2)) p.1 =
      analyticOrderNatAt (fun z => hillL2Radicand p.2 z) p.1 := by
  let H : ℂ → ℂ := fun w => 4*squaredCosh w^2-4
  let g : ℂ → ℂ := fun z => K (z,p.2)
  have hH : AnalyticAt ℂ H 0 :=
    (analyticAt_const.mul ((analyticOnNhd_squaredCosh 0 (mem_univ _)).pow 2)).sub analyticAt_const
  have hd : HasDerivAt H 4 0 := by
    convert! (hasDerivAt_squaredCosh_zero.pow 2).const_mul 4 |>.sub_const 4 using 1
    norm_num [squaredCosh_zero]
  have hH0 : H 0 = 0 := by simp [H]
  have ho : analyticOrderAt H 0 = 1 :=
    hH.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hH0 (by rw [hd.deriv]; norm_num)
  have hg : AnalyticAt ℂ g p.1 := hK.comp
    (f := fun z : ℂ => (z,p.2)) (analyticAt_id.prod analyticAt_const)
  have hg0 : g p.1 = 0 := hK0
  have hrelg := hrel.comp_tendsto
    ((continuous_id.prodMk continuous_const).tendsto p.1)
  have he : H ∘ g =ᶠ[𝓝 p.1] (fun z => hillL2Radicand p.2 z) := by
    filter_upwards [hrelg] with z hz
    change squaredCosh (g z) = sigma*hillL2Discriminant p.2 z/2 at hz
    change 4*squaredCosh (g z)^2-4 = hillL2Discriminant p.2 z^2-4
    rw [hz,div_pow,mul_pow,hsigma]
    ring
  have hH' : AnalyticAt ℂ H (g p.1) := by rw [hg0]; exact hH
  have hc := hH'.analyticOrderAt_comp hg
  simp only [hg0,ho,one_mul,sub_zero] at hc
  exact congrArg ENat.toNat (hc.symm.trans (analyticOrderAt_congr he))

/-- A continuous filled square vanishing at a branch point forces the
actual shifted primitive to tend to zero from every admissible direction. -/
theorem tendsto_hillL2ShiftedPrimitive_of_filled_square
    (n : ℕ) (S : Set (ℂ × Coeff 2)) (p : ℂ × Coeff 2) (K : ℂ × Coeff 2 → ℂ)
    (hK : ContinuousAt K p) (hK0 : K p = 0)
    (hmatch : ∀ t ∈ S, K t = (hillL2ContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) :
    Tendsto (fun t => hillL2ContinuedPrimitive t+I*(n : ℂ)*Real.pi) (𝓝[S] p) (𝓝 0) := by
  have hs : Tendsto (fun t => (hillL2ContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2)
      (𝓝[S] p) (𝓝 0) := by
    have hlim : Tendsto K (𝓝[S] p) (𝓝 0) := by
      simpa only [hK0] using hK.tendsto.mono_left nhdsWithin_le_nhds
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hmatch t ht
  have hn : Tendsto (fun t => ‖(hillL2ContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2‖)
      (𝓝[S] p) (𝓝 0) := by simpa only [norm_zero] using hs.norm
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def,norm_pow,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hroot

/-- The actual indexed endpoint value is uniform in the joint energy/L2
topology on complete high discs. The statement includes multiple zeros
and approaches along every admissible nearby complex potential. -/
theorem exists_hillL2_high_joint_indexed_branch_limits (q : Coeff 2) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set (Coeff 2),
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ p ∈ hillL2GapSquareDisc n r ×ˢ V,
        hillL2Radicand p.2 p.1 = 0 →
          Tendsto hillL2ContinuedPrimitive
            (𝓝[(hillL2GapSquareDisc n r ×ˢ V) ∩ hillL2ContinuationDomain] p)
            (𝓝 (-I*(n : ℂ)*Real.pi)) := by
  obtain ⟨r,N,V,hr,hrpi,hN,hV,hq,hfamily⟩ := exists_hillL2_whole_disc_squares q
  refine ⟨r,N,V,hr,hrpi,hN,hV,hq,?_⟩
  intro n hn p hp hzero
  obtain ⟨K,hK,_,_,hzeros,hmatch⟩ := hfamily n hn
  have hlim := tendsto_hillL2ShiftedPrimitive_of_filled_square (n : ℕ)
    ((hillL2GapSquareDisc n r ×ˢ V) ∩ hillL2ContinuationDomain) p K
    (hK p hp).continuousAt ((hzeros p hp).mpr hzero) hmatch
  have hsub := hlim.sub_const (I*(n : ℂ)*Real.pi)
  simpa only [add_sub_cancel_right,zero_sub,neg_mul] using hsub

end NLS.KdV
