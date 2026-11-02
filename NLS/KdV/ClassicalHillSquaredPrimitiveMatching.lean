import NLS.KdV.ClassicalHillHighEndpointNormalization
import NLS.KdV.ClassicalBranchPrimitive

/-! # Joint analytic squares of the actual shifted high Hill primitive

The joint endpoint limit removes the small-branch hypothesis from the
local squared-cosh inverse. On one common complex potential neighborhood,
every actual high branch point has a joint analytic squared-primitive
chart agreeing with the actual F_n^2 on its admissible neighborhood.
No simplicity or analytic choice of the individual endpoints is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

/-- Admissible energy/potential parameters in a fixed high energy region. -/
def classicalHillHighPrimitiveRegion (n : ℕ+) (V : Set (Curve ℂ)) :
    Set (ℂ × Curve ℂ) :=
  {t | t.1 ∈ classicalHillHighEnergyRegion n ∧ t.2 ∈ V ∧
    t ∈ classicalHillContinuationDomain}

/-- Any two normalized analytic squared-primitive charts for the actual
trace agree as joint germs. The overlap equality holds on a full complex
neighborhood, including at the branch locus. -/
theorem classicalHill_squared_primitive_germ_unique
    (p : ℂ × Curve ℂ) (sigma : ℂ) (K L : ℂ × Curve ℂ → ℂ)
    (hK : AnalyticAt ℂ K p) (hL : AnalyticAt ℂ L p) (hK0 : K p = 0) (hL0 : L p = 0)
    (hrelK : (fun t => squaredCosh (K t)) =ᶠ[𝓝 p]
      (fun t => sigma*classicalHillDiscriminant t.2 t.1/2))
    (hrelL : (fun t => squaredCosh (L t)) =ᶠ[𝓝 p]
      (fun t => sigma*classicalHillDiscriminant t.2 t.1/2)) :
    K =ᶠ[𝓝 p] L :=
  eventuallyEq_of_squaredCosh_eq K L p hK.continuousAt hL.continuousAt hK0 hL0
    (hrelK.trans hrelL.symm)

/-- The full joint derivative of the normalized square is the exact
parity multiple of the actual discriminant derivative. -/
theorem classicalHill_squared_primitive_fderiv
    (p : ℂ × Curve ℂ) (sigma : ℂ) (K : ℂ × Curve ℂ → ℂ)
    (hK : AnalyticAt ℂ K p) (hK0 : K p = 0)
    (hrel : (fun t => squaredCosh (K t)) =ᶠ[𝓝 p]
      (fun t => sigma*classicalHillDiscriminant t.2 t.1/2)) :
    fderiv ℂ K p = sigma • fderiv ℂ
      (fun t : ℂ × Curve ℂ => classicalHillDiscriminant t.2 t.1) p := by
  let D : ℂ × Curve ℂ → ℂ := fun t => classicalHillDiscriminant t.2 t.1
  have hD : AnalyticAt ℂ D p := analyticOnNhd_classicalHillDiscriminant_joint p (mem_univ _)
  have hC : HasDerivAt squaredCosh (1/2 : ℂ) (K p) := by
    rw [hK0]
    exact hasDerivAt_squaredCosh_zero
  have hleft := hC.comp_hasFDerivAt p hK.differentiableAt.hasFDerivAt
  have hright : HasFDerivAt (fun t : ℂ × Curve ℂ => sigma*D t/2)
      ((sigma/2) • fderiv ℂ D p) p := by
    convert! hD.differentiableAt.hasFDerivAt.const_smul (sigma/2) using 1
    funext t
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  have he := hleft.unique (hright.congr_of_eventuallyEq hrel)
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun M : (ℂ × Curve ℂ) →L[ℂ] ℂ => M v) he
  change (1/2 : ℂ) • (fderiv ℂ K p v) = (sigma/2) • (fderiv ℂ D p v) at hv
  change fderiv ℂ K p v = sigma • (fderiv ℂ D p v)
  simp only [smul_eq_mul] at hv ⊢
  linear_combination 2*hv

/-- The normalized square has exactly the physical radicand's analytic
energy order, including multiple zeros. No nonzero energy derivative of
the chart is needed. -/
theorem classicalHill_squared_primitive_energy_order
    (p : ℂ × Curve ℂ) (sigma : ℂ) (hsigma : sigma^2 = 1)
    (K : ℂ × Curve ℂ → ℂ) (hK : AnalyticAt ℂ K p) (hK0 : K p = 0)
    (hrel : (fun t => squaredCosh (K t)) =ᶠ[𝓝 p]
      (fun t => sigma*classicalHillDiscriminant t.2 t.1/2)) :
    analyticOrderNatAt (fun z => K (z,p.2)) p.1 =
      analyticOrderNatAt (fun z => classicalHillRadicand (z,p.2)) p.1 := by
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
  have he : H ∘ g =ᶠ[𝓝 p.1] (fun z => classicalHillRadicand (z,p.2)) := by
    filter_upwards [hrelg] with z hz
    change squaredCosh (g z) = sigma*classicalHillDiscriminant p.2 z/2 at hz
    change 4*squaredCosh (g z)^2-4 = classicalHillDiscriminant p.2 z^2-4
    rw [hz,div_pow,mul_pow,hsigma]
    ring
  have hH' : AnalyticAt ℂ H (g p.1) := by rw [hg0]; exact hH
  have hc := hH'.analyticOrderAt_comp hg
  simp only [hg0,ho,one_mul,sub_zero] at hc
  exact congrArg ENat.toNat (hc.symm.trans (analyticOrderAt_congr he))

/-- The analytic squared primitive retains the exact endpoint counts
of each actual high pair, with multiplicity two at a collapsed pair. -/
theorem ClassicalHillHighGapPair.squared_primitive_multiplicity
    {q : Curve ℂ} {n : ℕ+} {l r : ℂ} (h : ClassicalHillHighGapPair q n l r)
    (lambda : ℂ) (hlambda : lambda ∈ classicalHillHighEnergyRegion n)
    (sigma : ℂ) (hsigma : sigma^2 = 1) (K : ℂ × Curve ℂ → ℂ)
    (hK : AnalyticAt ℂ K (lambda,q)) (hK0 : K (lambda,q) = 0)
    (hrel : (fun t => squaredCosh (K t)) =ᶠ[𝓝 (lambda,q)]
      (fun t => sigma*classicalHillDiscriminant t.2 t.1/2)) :
    analyticOrderNatAt (fun z => K (z,q)) lambda = ({l,r} : Multiset ℂ).count lambda := by
  rw [classicalHill_squared_primitive_energy_order (lambda,q) sigma hsigma K hK hK0 hrel]
  exact h.multiplicity lambda hlambda

private theorem exists_squared_shifted_primitive_matching
    (p : ℂ × Curve ℂ) (n : ℕ) (S : Set (ℂ × Curve ℂ))
    (hbranch : classicalHillDiscriminant p.2 p.1 = 2*(-1 : ℂ)^n)
    (hdom : S ⊆ classicalHillContinuationDomain)
    (hstrip : ∀ t ∈ S,
      |(classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi).im| < Real.pi/2) :
    ∃ T : Set (ℂ × Curve ℂ), IsOpen T ∧ p ∈ T ∧
      ∃ K : ℂ × Curve ℂ → ℂ, AnalyticOnNhd ℂ K T ∧ K p = 0 ∧
        (∀ t ∈ T, squaredCosh (K t) = (-1 : ℂ)^n*classicalHillDiscriminant t.2 t.1/2) ∧
        ∀ t ∈ T ∩ S, K t = (classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2 := by
  have hsign : ((-1 : ℂ)^n)^2 = 1 := by rw [pow_two,← mul_pow]; simp
  obtain ⟨W,hW,hpW,U,hU,h0U,K,hK,hK0,hrel,hmatch⟩ :=
    exists_classicalHill_local_squared_primitive p ((-1 : ℂ)^n) hsign hbranch
  have hfn : Tendsto (fun t : ℂ × Curve ℂ => classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi)
      (𝓝[S] p) (𝓝 0) := by
    apply tendsto_classicalHillShiftedPrimitive_joint_at_branch p n id
      (tendsto_id.mono_left nhdsWithin_le_nhds) _ _ hbranch
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact hdom ht
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact hstrip t ht
  have hsq : Tendsto (fun t : ℂ × Curve ℂ =>
      (classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) (𝓝[S] p) (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0)] using hfn.pow 2
  have hevent : ∀ᶠ t in 𝓝[S] p,
      K t = (classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2 := by
    filter_upwards [hsq.eventually (hU.mem_nhds h0U),
      mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hpW),self_mem_nhdsWithin] with t htU htW htS
    apply hmatch t htW _ htU
    rw [cosh_add_hill_index]
    have h := (classicalHillContinuedPrimitive_trace t (hdom htS)).1
    linear_combination (-1 : ℂ)^n*h
  obtain ⟨epsilon,hepsilon,heq⟩ := Metric.mem_nhdsWithin_iff.mp hevent
  refine ⟨W ∩ ball p epsilon,hW.inter isOpen_ball,⟨hpW,mem_ball_self hepsilon⟩,
    K,hK.mono inter_subset_left,hK0,fun t ht => (hrel t ht.1).2,?_⟩
  intro t ht
  exact heq ⟨ht.1.2,ht.2⟩

/-- One complex neighborhood and cutoff precede all high indices and
branch points. Each actual high zero has a joint analytic chart for the
square of its actual shifted primitive, agreeing on an actual open patch
of admissible parameters. Double and higher spectral orders are allowed. -/
theorem exists_classicalHill_high_squared_primitive_matching (q : Curve ℂ) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ a ∈ V,
        ∀ lambda ∈ classicalHillHighEnergyRegion n, classicalHillRadicand (lambda,a) = 0 →
          ∃ T : Set (ℂ × Curve ℂ), IsOpen T ∧ (lambda,a) ∈ T ∧
            ∃ K : ℂ × Curve ℂ → ℂ, AnalyticOnNhd ℂ K T ∧ K (lambda,a) = 0 ∧
              (∀ t ∈ T, squaredCosh (K t) =
                (-1 : ℂ)^(n : ℕ)*classicalHillDiscriminant t.2 t.1/2) ∧
              ∀ t ∈ T ∩ classicalHillHighPrimitiveRegion n V,
                K t = (classicalHillContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2 := by
  obtain ⟨N,V,hN,hV,hq,hphase⟩ := exists_classicalHill_source_high_trace_phase q
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro n hn a ha lambda hlam hzero
  have hbranch : classicalHillDiscriminant a lambda = 2*(-1 : ℂ)^(n : ℕ) := by
    obtain ⟨z,hz,hzsq⟩ := hlam
    rw [← hzsq] at hzero ⊢
    exact classicalHillTrace_level_of_zero_and_phase a n z hzero (by
      simpa only [ofReal_one,one_smul] using hphase a ha 1 (by constructor <;> norm_num)
        n hn z (ball_subset_closedBall hz))
  apply exists_squared_shifted_primitive_matching (lambda,a) n
    (classicalHillHighPrimitiveRegion n V) hbranch (fun _ ht => ht.2.2)
  intro t ht
  obtain ⟨z,hz,hzsq⟩ := ht.1
  change z^2 = t.1 at hzsq
  have hdom : (z^2,t.2) ∈ classicalHillContinuationDomain := by
    rw [hzsq]
    exact ht.2.2
  have h := classicalHillShiftedPrimitive_im_strip_of_trace_phase t.2 n (by omega) z
    (ball_subset_closedBall hz) hdom
    (fun s hs => hphase t.2 ht.2.1 s hs n hn z (ball_subset_closedBall hz))
  simpa only [hzsq] using h

end NLS.KdV
