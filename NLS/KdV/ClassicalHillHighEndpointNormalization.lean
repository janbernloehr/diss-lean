import NLS.KdV.ClassicalHillHighPrimitiveStrip

/-! # Indexed limits at actual high Hill branch points

The continued root tends to zero when its squared radicand does. The
shifted multiplier then tends to one. The proved imaginary strip recovers
the actual shifted primitive by the principal logarithm near that limit,
fixing the endpoint value without an unspecified multiple of 2*pi*i.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

private theorem index_sign_mul_self (n : ℕ) : (-1 : ℂ)^n*(-1 : ℂ)^n = 1 := by
  rw [← mul_pow]
  simp

theorem exp_add_hill_index (z : ℂ) (n : ℕ) :
    exp (z+I*(n : ℂ)*Real.pi) = (-1 : ℂ)^n*exp z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : z+I*((n+1 : ℕ) : ℂ)*Real.pi =
        (z+I*(n : ℂ)*Real.pi)+(Real.pi : ℂ)*I := by push_cast; ring
    rw [he,exp_add_pi_mul_I,ih,pow_succ]
    ring

/-- The actual zero and the proved parity half-plane determine the
endpoint trace level; it is not supplied as spectral label data. -/
theorem classicalHillTrace_level_of_zero_and_phase
    (q : Curve ℂ) (n : ℕ) (z : ℂ) (hzero : classicalHillRadicand (z^2,q) = 0)
    (hphase : 0 < ((-1 : ℂ)^n*classicalHillDiscriminant q (z^2)).re) :
    classicalHillDiscriminant q (z^2) = 2*(-1 : ℂ)^n := by
  have hD : classicalHillDiscriminant q (z^2)^2 = 4 := sub_eq_zero.mp hzero
  have hs : ((-1 : ℂ)^n*classicalHillDiscriminant q (z^2))^2 = (2 : ℂ)^2 := by
    rw [mul_pow,hD]
    have hn : ((-1 : ℂ)^n)^2 = 1 := by simpa only [pow_two] using index_sign_mul_self n
    rw [hn]
    norm_num
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with he | he
  · have hh := congrArg (fun w : ℂ => (-1 : ℂ)^n*w) he
    rw [← mul_assoc,index_sign_mul_self,one_mul] at hh
    simpa only [mul_comm] using hh
  · rw [he] at hphase
    norm_num at hphase

/-- Along any admissible approach with the canonical imaginary strip,
the shifted primitive tends to zero at the actual parity branch point.
The statement imposes no simplicity or noncollapsed-gap hypothesis. -/
theorem tendsto_classicalHillShiftedPrimitive_at_branch
    {A : Type*} {l : Filter A} (q : Curve ℂ) (n : ℕ) (b : ℂ) (w : A → ℂ)
    (hw : Tendsto w l (𝓝 b))
    (hdom : ∀ᶠ i in l, (w i^2,q) ∈ classicalHillContinuationDomain)
    (hstrip : ∀ᶠ i in l,
      |(classicalHillContinuedPrimitive (w i^2,q)+I*(n : ℂ)*Real.pi).im| < Real.pi/2)
    (hbranch : classicalHillDiscriminant q (b^2) = 2*(-1 : ℂ)^n) :
    Tendsto (fun i => classicalHillContinuedPrimitive (w i^2,q)+I*(n : ℂ)*Real.pi) l (𝓝 0) := by
  have hparam : Continuous (fun z : ℂ => (z^2,q)) := by fun_prop
  have hall : Continuous (fun p : ℂ × Curve ℂ => classicalHillDiscriminant p.2 p.1) :=
    analyticOnNhd_classicalHillDiscriminant_joint.continuous
  have hcont : Continuous (fun z : ℂ => classicalHillDiscriminant q (z^2)) :=
    hall.comp (f := fun z : ℂ => (z^2,q)) hparam
  have hD := (hcont.tendsto b).comp hw
  rw [hbranch] at hD
  have hs : ((-1 : ℂ)^n)^2 = 1 := by simpa only [pow_two] using index_sign_mul_self n
  have hR : Tendsto (fun i => classicalHillRadicand (w i^2,q)) l (𝓝 0) := by
    have h := (hD.pow 2).sub_const 4
    have he : (2*(-1 : ℂ)^n)^2-4 = 0 := by rw [mul_pow,hs]; norm_num
    simpa only [classicalHillRadicand,he,Function.comp_def] using h
  have hroot : Tendsto (fun i => classicalHillContinuedRoot (w i^2,q)) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hn : Tendsto (fun i => ‖classicalHillRadicand (w i^2,q)‖) l (𝓝 0) := by
      simpa only [norm_zero] using hR.norm
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hn
    have heq : (fun i => Real.sqrt ‖classicalHillRadicand (w i^2,q)‖) =ᶠ[l]
        fun i => ‖classicalHillContinuedRoot (w i^2,q)‖ := by
      filter_upwards [hdom] with i hi
      rw [← classicalHillContinuedRoot_sq _ hi,norm_pow,Real.sqrt_sq (norm_nonneg _)]
    simpa only [Real.sqrt_zero] using ht.congr' heq
  have hE : Tendsto (fun i => exp (classicalHillContinuedPrimitive (w i^2,q)+I*(n : ℂ)*Real.pi))
      l (𝓝 1) := by
    have h := ((hD.add hroot).div_const 2).const_mul ((-1 : ℂ)^n)
    have he : (-1 : ℂ)^n*((2*(-1 : ℂ)^n+0)/2) = 1 := by
      rw [add_zero,show (2*(-1 : ℂ)^n)/2 = (-1 : ℂ)^n by ring,index_sign_mul_self]
    rw [he] at h
    apply h.congr'
    filter_upwards [hdom] with i hi
    rw [exp_add_hill_index,exp_classicalHillContinuedPrimitive _ hi]
    rfl
  have hlog := (continuousAt_clog (by simp : (1 : ℂ) ∈ slitPlane)).tendsto.comp hE
  have hlog0 : Tendsto (fun i => log (exp
      (classicalHillContinuedPrimitive (w i^2,q)+I*(n : ℂ)*Real.pi))) l (𝓝 0) := by
    simpa only [log_one,Function.comp_def] using hlog
  apply hlog0.congr'
  filter_upwards [hstrip] with i hi
  apply log_exp
  · linarith [(abs_lt.mp hi).1,Real.pi_pos]
  · linarith [(abs_lt.mp hi).2,Real.pi_pos]

/-- At every actual high branch point of every real potential in one
complex neighborhood, the normalized limit is zero from both nonreal
frequency half-planes. The cutoff precedes all potentials and endpoints. -/
theorem exists_classicalHill_high_endpoint_normalization (q : Curve ℂ) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, (∀ t, (a t).im = 0) → ∀ n : ℕ, N ≤ n →
        ∀ b ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4),
          classicalHillRadicand (b^2,a) = 0 →
            Tendsto (fun z : ℂ => classicalHillContinuedPrimitive (z^2,a)+I*(n : ℂ)*Real.pi)
              (𝓝[{z : ℂ | z.im ≠ 0}] b) (𝓝 0) := by
  obtain ⟨N,V,hN,hV,hq,hphase⟩ := exists_classicalHill_source_high_trace_phase q
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro a ha hreal n hn b hb hzero
  have hn1 : 1 ≤ n := by omega
  have hball : ∀ᶠ z in 𝓝[{z : ℂ | z.im ≠ 0}] b,
      z ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4) :=
    mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hb)
  have hdom : ∀ᶠ z in 𝓝[{z : ℂ | z.im ≠ 0}] b,
      (z^2,a) ∈ classicalHillContinuationDomain := by
    filter_upwards [self_mem_nhdsWithin,hball] with z hzi hz
    have hre := re_pos_of_high_closedBall n hn1 z (ball_subset_closedBall hz)
    have him : (z^2).im ≠ 0 := by
      intro he
      apply mul_ne_zero hre.ne' hzi
      simp only [pow_two,mul_im] at he
      linear_combination he/2
    exact mem_classicalHillContinuationDomain_of_im_ne_zero a hreal (z^2) him
  apply tendsto_classicalHillShiftedPrimitive_at_branch a n b id
    (tendsto_id.mono_left nhdsWithin_le_nhds) hdom _
    (classicalHillTrace_level_of_zero_and_phase a n b hzero (by
      simpa only [ofReal_one,one_smul] using hphase a ha 1 (by constructor <;> norm_num)
        n hn b (ball_subset_closedBall hb)))
  filter_upwards [hball,hdom] with z hz hzd
  exact classicalHillShiftedPrimitive_im_strip_of_trace_phase a n hn1 z
    (ball_subset_closedBall hz) hzd (fun s hs => hphase a ha s hs n hn z (ball_subset_closedBall hz))

private theorem energy_sqrt_square (z : ℂ) : (Complex.sqrt z)^2 = z := by
  have h := Complex.cpow_nat_inv_pow z (Nat.succ_ne_zero 1)
  norm_num at h
  simpa only [Complex.sqrt,one_div] using h

/-- The indexed endpoint value in the actual energy coordinate. Every
high radicand zero has limit -i*n*pi from both nonreal energy half-planes,
on one common complex potential neighborhood. Double zeros are included.
This does not assign the finitely many central spectral labels. -/
theorem exists_classicalHill_high_energy_endpoint_normalization (q : Curve ℂ) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, (∀ t, (a t).im = 0) → ∀ n : ℕ+, N ≤ (n : ℕ) →
        ∀ lambda ∈ classicalHillHighEnergyRegion n,
          classicalHillRadicand (lambda,a) = 0 →
            Tendsto (fun mu : ℂ => classicalHillContinuedPrimitive (mu,a))
              (𝓝[{mu : ℂ | mu.im ≠ 0}] lambda) (𝓝 (-I*(n : ℂ)*Real.pi)) := by
  obtain ⟨N,V,hN,hV,hq,hlim⟩ := exists_classicalHill_high_endpoint_normalization q
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro a ha hreal n hn lambda hlam hzero
  obtain ⟨b,hb,rfl⟩ := hlam
  have hFn := hlim a ha hreal n hn b hb hzero
  have hF : Tendsto (fun z : ℂ => classicalHillContinuedPrimitive (z^2,a))
      (𝓝[{z : ℂ | z.im ≠ 0}] b) (𝓝 (-I*(n : ℂ)*Real.pi)) := by
    have h := hFn.sub_const (I*(n : ℂ)*Real.pi)
    simpa only [add_sub_cancel_right,zero_sub,neg_mul] using h
  have hbre := re_pos_of_high_closedBall n n.property b (ball_subset_closedBall hb)
  have hroot : Complex.sqrt (b^2) = b := by
    have h := classicalHillFreePrimitive_sq_of_re_pos b hbre
    change -I*Complex.sqrt (b^2) = -I*b at h
    exact mul_left_cancel₀ (neg_ne_zero.mpr I_ne_zero) h
  have hcont : Tendsto Complex.sqrt (𝓝[{mu : ℂ | mu.im ≠ 0}] (b^2)) (𝓝 b) := by
    have hs := (Complex.differentiableAt_sqrt
      (sq_mem_slitPlane_of_high_closedBall n n.property b (ball_subset_closedBall hb))).continuousAt.tendsto
    rw [hroot] at hs
    exact hs.mono_left nhdsWithin_le_nhds
  have hsqrt : Tendsto Complex.sqrt (𝓝[{mu : ℂ | mu.im ≠ 0}] (b^2))
      (𝓝[{z : ℂ | z.im ≠ 0}] b) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hcont,?_⟩
    filter_upwards [self_mem_nhdsWithin] with mu hmu
    intro he
    apply hmu
    have hi := congrArg Complex.im (energy_sqrt_square mu)
    simpa only [pow_two,mul_im,he,mul_zero,zero_mul,zero_add] using hi.symm
  have h := hF.comp hsqrt
  simpa only [Function.comp_def,energy_sqrt_square] using h

end NLS.KdV
