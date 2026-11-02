import NLS.KdV.ClassicalHillFreeSquareComparison
import NLS.KdV.ClassicalHighGapFamilies
import NLS.ComplexAnalysis.TwoZeroDeflation
import NLS.ComplexAnalysis.NormalizedSquareRootBounds

/-! # The actual high Hill endpoint quotient has its free normalization

The whole-disc square comparison and arbitrarily small actual endpoint
confinement imply 4*n^2*pi^2*Q_n -> -1 on a fixed family of energy discs.
The common radius precedes the tolerance, cutoff and complex potential
neighborhood. The estimate is valid at double roots as well.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_classicalHill_normalized_gap_quotients (q : Curve ℂ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi/4 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 → ∃ N : ℕ, ∃ V : Set (Curve ℂ),
        0 < N ∧ IsOpen V ∧ q ∈ V ∧
        ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × Curve ℂ → ℂ,
          AnalyticOnNhd ℂ K (classicalHillGapSquareDisc n r ×ˢ V) ∧
          (∀ t ∈ classicalHillGapSquareDisc n r ×ˢ V,
            squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*classicalHillDiscriminant t.2 t.1/2) ∧
          (∀ t ∈ (classicalHillGapSquareDisc n r ×ˢ V) ∩ classicalHillContinuationDomain,
            K t = (classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
          ∀ a ∈ V, ∃ l u : ℂ, ClassicalHillHighGapPair a n l u ∧
            l ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) ((epsilon/64)*(Real.pi*(n : ℕ)*r)) ∧
            u ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) ((epsilon/64)*(Real.pi*(n : ℕ)*r)) ∧
            AnalyticOnNhd ℂ (twoZeroQuotient (fun z => K (z,a)) l u) (classicalHillGapSquareDisc n r) ∧
            (∀ z, K (z,a) = (z-l)*(z-u)*twoZeroQuotient (fun z => K (z,a)) l u z) ∧
            ∀ z ∈ classicalHillGapSquareDisc n r,
              ‖(4*((Real.pi : ℂ)*(n : ℕ))^2)*twoZeroQuotient (fun z => K (z,a)) l u z+1‖ ≤ epsilon := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := exists_classicalHill_quadratic_square_comparison q
  refine ⟨r,hr,hrpi,?_⟩
  intro epsilon hepsilon hepsilon1
  let eta : ℝ := epsilon/64
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have heta1 : eta ≤ 1 := by dsimp only [eta]; linarith
  have hetar : eta*r ≤ r := by nlinarith [mul_nonneg (sub_nonneg.mpr heta1) hr.le]
  obtain ⟨Nk,Vk,hNk,hVk,hqk,hKfamily⟩ := hfamily eta heta
  obtain ⟨Np,Vp,_,hVp,hqp,hpairs⟩ := exists_analytic_classicalHillHighGapFamilies q
  obtain ⟨Nr,Vr,_,hVr,hqr,hcover⟩ := exists_classicalHill_small_gap_coverage q (eta*r/4)
    (by positivity) (by linarith)
  let N := max Nk (max (Np+1) Nr)
  let V := Vk ∩ (Vp ∩ Vr)
  refine ⟨N,V,hNk.trans_le (le_max_left _ _),hVk.inter (hVp.inter hVr),⟨hqk,hqp,hqr⟩,?_⟩
  intro n hn
  have hnk : Nk ≤ (n : ℕ) := (le_max_left Nk _).trans hn
  have hnp : Np < (n : ℕ) := by
    have := (le_max_left (Np+1) Nr).trans ((le_max_right Nk _).trans hn)
    omega
  have hnr : Nr ≤ (n : ℕ) := (le_max_right (Np+1) Nr).trans ((le_max_right Nk _).trans hn)
  obtain ⟨K,hK,_,hrel,hzero,hmatch,herror⟩ := hKfamily n hnk
  have hsub : classicalHillGapSquareDisc n r ×ˢ V ⊆ classicalHillGapSquareDisc n r ×ˢ Vk :=
    fun _ ht => ⟨ht.1,ht.2.1⟩
  refine ⟨K,hK.mono hsub,fun t ht => hrel t (hsub ht),fun t ht => hmatch t ⟨hsub ht.1,ht.2⟩,?_⟩
  intro a ha
  obtain ⟨l,u,hpair⟩ := (hpairs n hnp).2.2.2 a ha.2.1
  let c : ℝ := Real.pi*(n : ℕ)
  let E : ℂ := (c : ℂ)^2
  let R : ℝ := c*r
  have hc : 0 < c := by dsimp only [c]; positivity
  have hR : 0 < R := mul_pos hc hr
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hrc : r ≤ c := by
    have hnreal : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.property
    dsimp only [c]
    nlinarith [Real.pi_pos]
  have endpoint_mem (lambda : ℂ) (hlambda : lambda ∈ classicalHillHighEnergyRegion n)
      (hz : classicalHillRadicand (lambda,a) = 0) : lambda ∈ ball E (eta*R) := by
    obtain ⟨z,hzball,hzsq⟩ := hlambda
    change z^2 = lambda at hzsq
    have hzsmall := hcover a ha.2.2 (n : ℤ) (by simpa only [Int.natAbs_natCast] using hnr) z
      (by simpa only [Int.cast_natCast] using ball_subset_closedBall hzball)
      (by simpa only [hzsq] using hz)
    have hh := square_mem_energy_ball_of_small_frequency c (eta*r) hc (by positivity)
      (hetar.trans hrc) z (by simpa only [c,ofReal_mul,ofReal_natCast,Int.cast_natCast] using hzsmall)
    have he : c*(eta*r) = eta*R := by dsimp only [R]; ring
    simpa only [E,hzsq,he] using hh
  have hl := endpoint_mem l hpair.left_mem hpair.left_zero
  have hu := endpoint_mem u hpair.right_mem hpair.right_zero
  have heta2 : eta ≤ 1/2 := by dsimp only [eta]; linarith
  have hetaR : eta*R < R := by nlinarith
  have hlball : l ∈ ball E R := ball_subset_ball hetaR.le hl
  have huball : u ∈ ball E R := ball_subset_ball hetaR.le hu
  have hla : (l,a) ∈ classicalHillGapSquareDisc n r ×ˢ Vk := by
    refine ⟨?_,ha.1⟩
    simpa only [classicalHillGapSquareDisc,E,R,c,ofReal_mul,ofReal_natCast] using ball_subset_closedBall hlball
  have hua : (u,a) ∈ classicalHillGapSquareDisc n r ×ˢ Vk := by
    refine ⟨?_,ha.1⟩
    simpa only [classicalHillGapSquareDisc,E,R,c,ofReal_mul,ofReal_natCast] using ball_subset_closedBall huball
  have hfa : K (l,a) = 0 := (hzero (l,a) hla).mpr hpair.left_zero
  have hfb : K (u,a) = 0 := (hzero (u,a) hua).mpr hpair.right_zero
  have hf : AnalyticOnNhd ℂ (fun z => K (z,a)) (closedBall E R) := by
    intro z hz
    exact (hK (z,a) ⟨by simpa only [classicalHillGapSquareDisc,E,R,c,ofReal_mul,ofReal_natCast] using hz,ha.1⟩).comp
      (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
  have hdouble : l = u → deriv (fun z => K (z,a)) l = 0 := by
    intro he
    have hrelg : (fun t => squaredCosh (K t)) =ᶠ[𝓝 (l,a)]
        (fun t => (-1 : ℂ)^(n : ℕ)*classicalHillDiscriminant t.2 t.1/2) := by
      filter_upwards [(isOpen_ball.prod hVk).mem_nhds ⟨hlball,ha.1⟩] with t ht
      exact hrel t ⟨by simpa only [classicalHillGapSquareDisc,E,R,c,ofReal_mul,ofReal_natCast] using
        ball_subset_closedBall ht.1,ht.2⟩
    have hsign : ((-1 : ℂ)^(n : ℕ))^2 = 1 := by rw [pow_two,← mul_pow]; simp
    have ho : analyticOrderNatAt (fun z => K (z,a)) l = 2 := by
      simpa [he] using hpair.squared_primitive_multiplicity l hpair.left_mem
        ((-1 : ℂ)^(n : ℕ)) hsign K (hK (l,a) hla) hfa hrelg
    by_contra hd
    have hone := (hf l (ball_subset_closedBall hlball)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hfa hd
    have hone' : analyticOrderNatAt (fun z => K (z,a)) l = 1 := congrArg ENat.toNat hone
    omega
  let Q := twoZeroQuotient (fun z => K (z,a)) l u
  have hQ : AnalyticOnNhd ℂ Q (closedBall E R) := analyticOnNhd_twoZeroQuotient _ _ l u hf
    (ball_subset_closedBall hlball) (ball_subset_closedBall huball)
  have hfactor : ∀ z, K (z,a) = (z-l)*(z-u)*Q z := twoZeroQuotient_factor _ l u hfa hfb hdouble
  let Q₀ : ℂ → ℂ := fun _ => -(4*(c : ℂ)^2)⁻¹
  have hQ₀norm (z : ℂ) : ‖Q₀ z‖ = 1/(4*c^2) := by simp [Q₀,abs_of_pos hc]
  have hmodel : ∀ z, classicalHillFreeQuadraticModel n z = (z-E)^2*Q₀ z := by
    intro z
    simp only [classicalHillFreeQuadraticModel,E,c,ofReal_mul,ofReal_natCast,Q₀,div_eq_mul_inv]
    ring
  have hl' : ‖l-E‖ ≤ eta*R := (show ‖l-E‖ < eta*R by simpa only [mem_ball,dist_eq_norm] using hl).le
  have hu' : ‖u-E‖ ≤ eta*R := (show ‖u-E‖ < eta*R by simpa only [mem_ball,dist_eq_norm] using hu).le
  have herr : ∀ z ∈ sphere E R, ‖K (z,a)-classicalHillFreeQuadraticModel n z‖ ≤ eta*r^2 := by
    intro z hz
    apply herror (z,a)
    refine ⟨?_,ha.1⟩
    simpa only [classicalHillGapSquareDisc,E,R,c,ofReal_mul,ofReal_natCast] using (sphere_subset_closedBall hz)
  have hbound := norm_two_root_quotient_sub_le_on_disc (fun z => K (z,a))
    (classicalHillFreeQuadraticModel n) Q Q₀ l u E R (eta*R) (eta*r^2) (1/(4*c^2))
    hR (by positivity) (by nlinarith) (by positivity)
    hl' hu' hQ analyticOnNhd_const hfactor hmodel herr
    (fun z _ => (hQ₀norm z).le)
  refine ⟨l,u,hpair,?_,?_,?_,hfactor,?_⟩
  · simpa only [E,R,c,ofReal_mul,ofReal_natCast,eta] using hl
  · simpa only [E,R,c,ofReal_mul,ofReal_natCast,eta] using hu
  · simpa only [classicalHillGapSquareDisc,E,R,c,ofReal_mul,ofReal_natCast] using hQ
  · intro z hz
    have hz' : z ∈ closedBall E R := by simpa only [classicalHillGapSquareDisc,E,R,c,ofReal_mul,ofReal_natCast] using hz
    have hnrm : ‖(4 : ℂ)*(c : ℂ)^2‖ = 4*c^2 := by simp [abs_of_pos hc]
    have hid : (4 : ℂ)*(c : ℂ)^2*Q z+1 = ((4 : ℂ)*(c : ℂ)^2)*(Q z-Q₀ z) := by
      dsimp only [Q₀]
      field_simp [hcC]
      ring
    have hcc : (Real.pi : ℂ)*(n : ℕ) = (c : ℂ) := by simp only [c,ofReal_mul,ofReal_natCast]
    rw [hcc]
    change ‖(4 : ℂ)*(c : ℂ)^2*Q z+1‖ ≤ epsilon
    rw [hid,norm_mul,hnrm]
    calc
      _ ≤ (4*c^2)*(4*(eta*r^2+(1/(4*c^2))*(2*R*(eta*R)+(eta*R)^2))/R^2) :=
        mul_le_mul_of_nonneg_left (hbound z hz') (by positivity)
      _ = 24*eta+4*eta^2 := by
        dsimp only [R]
        field_simp [hc.ne',hr.ne']
        ring
      _ ≤ epsilon := by
        dsimp only [eta]
        nlinarith [mul_nonneg hepsilon.le (sub_nonneg.mpr hepsilon1)]

/-- The actual deflated square has an analytic root uniformly close to
i/(2*n*pi) on the full closed disc. The sign is prescribed by this free
model; a physical integration-circle normalization is still separate. -/
theorem exists_classicalHill_near_free_gap_units (q : Curve ℂ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi/4 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 → ∃ N : ℕ, ∃ V : Set (Curve ℂ),
        0 < N ∧ IsOpen V ∧ q ∈ V ∧
        ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × Curve ℂ → ℂ,
          AnalyticOnNhd ℂ K (classicalHillGapSquareDisc n r ×ˢ V) ∧
          (∀ t ∈ classicalHillGapSquareDisc n r ×ˢ V,
            squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*classicalHillDiscriminant t.2 t.1/2) ∧
          (∀ t ∈ (classicalHillGapSquareDisc n r ×ˢ V) ∩ classicalHillContinuationDomain,
            K t = (classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
          ∀ a ∈ V, ∃ l u : ℂ, ∃ H : ℂ → ℂ, ClassicalHillHighGapPair a n l u ∧
            l ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) ((epsilon/64)*(Real.pi*(n : ℕ)*r)) ∧
            u ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) ((epsilon/64)*(Real.pi*(n : ℕ)*r)) ∧
            AnalyticOnNhd ℂ H (classicalHillGapSquareDisc n r) ∧
            ∀ z ∈ classicalHillGapSquareDisc n r,
              H z ≠ 0 ∧ H z^2 = twoZeroQuotient (fun z => K (z,a)) l u z ∧
              K (z,a) = (z-l)*(z-u)*H z^2 ∧
              ‖H z-I/(2*((Real.pi : ℂ)*(n : ℕ)))‖ ≤ epsilon/(2*Real.pi*(n : ℕ)) := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := exists_classicalHill_normalized_gap_quotients q
  refine ⟨r,hr,hrpi,?_⟩
  intro epsilon hepsilon hepsilon1
  obtain ⟨N,V,hN,hV,hq,hKfamily⟩ := hfamily epsilon hepsilon hepsilon1.le
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro n hn
  obtain ⟨K,hK,hrel,hmatch,hpairs⟩ := hKfamily n hn
  refine ⟨K,hK,hrel,hmatch,?_⟩
  intro a ha
  obtain ⟨l,u,hpair,hl,hu,hQ,hfactor,hbound⟩ := hpairs a ha
  let Q := twoZeroQuotient (fun z => K (z,a)) l u
  let c : ℝ := Real.pi*(n : ℕ)
  let w : ℂ := I/(2*(c : ℂ))
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hw : w ≠ 0 := div_ne_zero I_ne_zero (mul_ne_zero (by norm_num) hcC)
  have hwsq : w^2 = -((4 : ℂ)*(c : ℂ)^2)⁻¹ := by
    dsimp only [w]
    rw [div_pow,I_sq,mul_pow]
    norm_num
    field_simp [hcC]
  have hratio (z : ℂ) : Q z/w^2-1 = -((4 : ℂ)*(c : ℂ)^2*Q z+1) := by
    rw [hwsq]
    simp only [div_eq_mul_inv,inv_neg,inv_inv]
    ring
  have hb : ∀ z ∈ classicalHillGapSquareDisc n r, ‖Q z/w^2-1‖ ≤ epsilon := by
    intro z hz
    rw [hratio,norm_neg]
    simpa only [c,Q,ofReal_mul,ofReal_natCast] using hbound z hz
  obtain ⟨hH,hroots⟩ := prescribedSquareRoot_analytic_and_close Q (classicalHillGapSquareDisc n r)
    w epsilon hQ hw hepsilon1 hb
  refine ⟨l,u,prescribedSquareRoot Q w,hpair,hl,hu,hH,?_⟩
  intro z hz
  obtain ⟨hne,hsq,hclose⟩ := hroots z hz
  refine ⟨hne,hsq,?_,?_⟩
  · rw [hsq]
    exact hfactor z
  · have hnormw : ‖w‖ = 1/(2*c) := by simp [w,abs_of_pos hc]
    have hh : ‖prescribedSquareRoot Q w z-w‖ ≤ epsilon/(2*c) := by
      calc
        _ ≤ ‖w‖*epsilon := hclose
        _ = epsilon/(2*c) := by rw [hnormw]; ring
    simpa only [w,c,ofReal_mul,ofReal_natCast,mul_assoc] using hh

end NLS.KdV
