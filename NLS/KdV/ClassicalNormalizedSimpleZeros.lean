import NLS.KdV.ClassicalNormalizedZeroDerivative

/-! # Simplicity of the actual simultaneous normalized numerator zeros

The exact filled identity transports the nonzero diagonal derivative of
the invertible Hilbert zero equation to the literal energy derivative of
Psi_n. The argument includes zeros at their own critical energy.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem normalizedNumerator_simple_of_regular_zeroMap
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V) (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2)
    (n k : ℕ+) (hkn : k ≠ n) (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ)
    (ht : t ∈ classicalHillCandidateDomain V)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R t.2 (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q t.2 (lp.single 2 j 1)) m)
    (hzero : classicalHillZeroMap N Q n t = 0)
    (hbij : Function.Bijective (classicalHillZeroPartial N Q n t)) :
    deriv (fun lambda => classicalHillNormalizedNumerator N R n (lambda,t.2))
      (classicalHillCandidateEnergy N k t) ≠ 0 := by
  intro hbad
  let v (c : ℂ) : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ :=
    (t.1+c • lp.single 2 (k : ℤ) 1,t.2)
  let l (c : ℂ) := classicalHillCandidateEnergy N k (v c)
  let z := classicalHillCandidateFrequency N k t
  let C : ℂ := 2*(n : ℂ)*classicalHillCriticalFrequency N k t.2/(k : ℂ)
  let d := classicalHillZeroPartial N Q n t (lp.single 2 (k : ℤ) 1) (k : ℤ)
  have hd : d ≠ 0 := D.zeroPartial_single_diagonal_ne_zero Q hQa hQ n t ht hbij (k : ℤ)
  have hbase : v 0 = t := by simp only [v,zero_smul,add_zero,Prod.eta]
  have hl0 : l 0 = classicalHillCandidateEnergy N k t := congrArg (classicalHillCandidateEnergy N k) hbase
  have hl : l = fun c : ℂ => (z+c)^2 := by
    funext c
    dsimp only [l,v,z,classicalHillCandidateEnergy,classicalHillCandidateFrequency]
    simp only [lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      lp.single_apply,Pi.single_apply,ite_true,mul_one]
    ring
  have hlam : HasDerivAt l (2*z) 0 := by
    rw [hl]
    simpa using! ((hasDerivAt_const (0 : ℂ) z).add (hasDerivAt_id (0 : ℂ))).pow 2
  have hPsi := D.normalizedNumerator_zero_of_zeroMap R Q hQa hQ n k hkn t ht hcompat hzero
  have hp0 : HasDerivAt (fun lambda => classicalHillNormalizedNumerator N R n (lambda,t.2)) 0 (l 0) := by
    rw [hl0]
    have hh := (D.normalizedNumerator_entire R hRa n t.2 ht.2 (classicalHillCandidateEnergy N k t) (mem_univ _)).differentiableAt.hasDerivAt
    rwa [hbad] at hh
  have hp : HasDerivAt (fun c : ℂ => classicalHillNormalizedNumerator N R n (l c,t.2)) 0 0 := by
    simpa only [Function.comp_def,zero_mul] using! hp0.comp 0 hlam
  have hleft : HasDerivAt (fun c : ℂ => (l c-classicalHillUniformCriticalPoint N n t.2)*
      classicalHillNormalizedNumerator N R n (l c,t.2)) 0 0 := by
    simpa only [hl0,hPsi,mul_zero,zero_mul,add_zero] using! (hlam.sub_const _).mul hp
  have hb : AnalyticAt ℂ (fun lambda : ℂ => classicalHillUniformNumerator N k (lambda,t.2)) (l 0) :=
    (D.numerator_analytic k (l 0,t.2) ⟨mem_univ _,ht.2⟩).comp
      (f := fun lambda : ℂ => (lambda,t.2)) (analyticAt_id.prod analyticAt_const)
  have hB := hb.differentiableAt.hasDerivAt.comp 0 hlam
  have hF := D.zeroMap_coordinate_curve_hasDerivAt Q hQa hQ n t ht (k : ℤ) (k : ℤ)
  have hF0 : classicalHillZeroMap N Q n (v 0) (k : ℤ) = 0 := by
    rw [hbase,hzero]
    rfl
  have hright : HasDerivAt (fun c : ℂ => C*classicalHillUniformNumerator N k (l c,t.2)*
      classicalHillZeroMap N Q n (v c) (k : ℤ))
      (C*classicalHillUniformNumerator N k (classicalHillCandidateEnergy N k t,t.2)*d) 0 := by
    have hF' : HasDerivAt (fun c : ℂ => classicalHillZeroMap N Q n (v c) (k : ℤ)) d 0 := hF
    simpa only [Function.comp_def,hl0,hF0,mul_zero,zero_add,mul_assoc] using! (hB.mul hF').const_mul C
  have hv : ContinuousAt v 0 :=
    (continuousAt_const.add (continuousAt_id.smul continuousAt_const)).prodMk continuousAt_const
  have hU : IsOpen (classicalHillCandidateDomain V) := isOpen_ball.prod D.isOpen
  have he : ∀ᶠ c : ℂ in 𝓝 0, v c ∈ classicalHillCandidateDomain V :=
    hv.eventually (hU.mem_nhds (by rw [hbase]; exact ht))
  have hidentity : (fun c : ℂ => (l c-classicalHillUniformCriticalPoint N n t.2)*
      classicalHillNormalizedNumerator N R n (l c,t.2)) =ᶠ[𝓝 0]
      (fun c : ℂ => C*classicalHillUniformNumerator N k (l c,t.2)*classicalHillZeroMap N Q n (v c) (k : ℤ)) := by
    filter_upwards [he] with c hc
    exact D.normalizedNumerator_filled_factorization R Q hQa hQ n k hkn (v c) hc hcompat
  have hz := hright.unique (hleft.congr_of_eventuallyEq hidentity.symm)
  have hC : C ≠ 0 := by
    dsimp only [C]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast n.ne_zero))
      (D.critical_frequency_ne_zero k t.2 ht.2)) (by exact_mod_cast k.ne_zero)
  exact mul_ne_zero (mul_ne_zero hC (D.candidate_numerator_ne_zero k t ht)) hd hz

/-- One subneighborhood supports all retained actual simple zeros for the
fixed omitted n. The original Hilbert branch and its free values remain. -/
theorem exists_actual_simple_normalized_zero_family
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V) (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2)
    (hQ0 : Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2))
    (hcompat : ∀ q ∈ V, ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q q (lp.single 2 j 1)) m) (n : ℕ+) :
    ∃ W : Set (NLS.LinearVolterra.Curve ℂ), ∃ s : NLS.LinearVolterra.Curve ℂ → NLS.Coeff 2,
      W ⊆ V ∧ IsOpen W ∧ 0 ∈ W ∧ s 0 = 0 ∧ AnalyticOnNhd ℂ s W ∧
      (∀ k : ℕ+, AnalyticOnNhd ℂ (fun q => classicalHillCandidateEnergy N k (s q,q)) W) ∧
      (∀ k : ℕ+, classicalHillCandidateEnergy N k (s 0,0) = freeHillEnergy k) ∧
      ∀ q ∈ W, ‖s q‖ < Real.pi/16 ∧
        (∀ j : ℤ, j ≤ 0 ∨ j = (n : ℤ) → s q j = 0) ∧
        Function.Injective (fun k : ℕ+ => classicalHillCandidateEnergy N k (s q,q)) ∧
        ∀ k : ℕ+, k ≠ n →
          classicalHillNormalizedNumerator N R n (classicalHillCandidateEnergy N k (s q,q),q) = 0 ∧
          deriv (fun lambda => classicalHillNormalizedNumerator N R n (lambda,q))
            (classicalHillCandidateEnergy N k (s q,q)) ≠ 0 := by
  obtain ⟨s,U,hUV,hU,h0U,hs0,hsa,hs⟩ := D.exists_analytic_normalized_root_displacements Q hQa hQ hQ0 n
  have ht (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ U) : (s q,q) ∈ classicalHillCandidateDomain V :=
    ⟨by simpa only [mem_ball,dist_zero_right] using (hs q hq).1,hUV hq⟩
  obtain ⟨W,hWU,hW,h0W,hregular⟩ := D.exists_regular_zero_graph Q hQa hQ hQ0 n s U hU h0U hs0 hsa ht
  refine ⟨W,s,fun _ hq => hUV (hWU hq),hW,h0W,hs0,hsa.mono hWU,?_,?_,?_⟩
  · intro k q hq
    exact (D.candidate_energy_analytic k (s q,q) (ht q (hWU hq))).comp
      (f := fun a : NLS.LinearVolterra.Curve ℂ => (s a,a)) ((hsa q (hWU hq)).prod analyticAt_id)
  · intro k
    rw [classicalHillCandidateEnergy,classicalHillCandidateFrequency,hs0,lp.coeFn_zero,
      Pi.zero_apply,add_zero,classicalHillCriticalFrequency,sq_sqrt,D.critical_free]
  intro q hq
  have hqU := hWU hq
  refine ⟨(hs q hqU).1,?_,D.candidate_energies_injective (s q,q) (ht q hqU),?_⟩
  · intro j hj
    have ha := D.zeroMap_auxiliary Q hQa hQ n (s q,q) (ht q hqU) j hj
    rw [(hs q hqU).2] at ha
    simpa only [lp.coeFn_zero,Pi.zero_apply] using ha.symm
  intro k hkn
  exact ⟨D.normalizedNumerator_zero_of_zeroMap R Q hQa hQ n k hkn (s q,q) (ht q hqU)
      (hcompat q (hUV hqU)) (hs q hqU).2,
    D.normalizedNumerator_simple_of_regular_zeroMap R Q hRa hQa hQ n k hkn (s q,q) (ht q hqU)
      (hcompat q (hUV hqU)) (hs q hqU).2 (hregular q hq)⟩

end ClassicalAllContourPeriodData

/-- One constructed normalization neighborhood precedes the omitted mode;
for each mode a subneighborhood supports its entire infinite analytic simple-zero
sequence. All original exact normalization periods are retained. -/
theorem exists_classicalHill_local_simple_normalized_zeros :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ),
      ∃ R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen V ∧ 0 ∈ V ∧ AnalyticOnNhd ℂ R V ∧
        R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        (∀ n k : ℕ+, ∀ q ∈ V,
          (2*(Real.pi : ℂ))⁻¹ * ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
            classicalHillNormalizedNumerator N R n (z^2,q)/classicalHillContinuedRoot (z^2,q)*(2*z) =
              if n = k then 1 else 0) ∧
        ∀ n : ℕ+, ∃ U : Set (NLS.LinearVolterra.Curve ℂ), ∃ s : NLS.LinearVolterra.Curve ℂ → NLS.Coeff 2,
          U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧ s 0 = 0 ∧ AnalyticOnNhd ℂ s U ∧
          (∀ k : ℕ+, AnalyticOnNhd ℂ (fun q => classicalHillCandidateEnergy N k (s q,q)) U) ∧
          (∀ k : ℕ+, classicalHillCandidateEnergy N k (s 0,0) = freeHillEnergy k) ∧
          ∀ q ∈ U, ‖s q‖ < Real.pi/16 ∧
            (∀ j : ℤ, j ≤ 0 ∨ j = (n : ℤ) → s q j = 0) ∧
            Function.Injective (fun k : ℕ+ => classicalHillCandidateEnergy N k (s q,q)) ∧
            ∀ k : ℕ+, k ≠ n →
              classicalHillNormalizedNumerator N R n (classicalHillCandidateEnergy N k (s q,q),q) = 0 ∧
              deriv (fun lambda => classicalHillNormalizedNumerator N R n (lambda,q))
                (classicalHillCandidateEnergy N k (s q,q)) ≠ 0 := by
  obtain ⟨N,V,T,R,S,Q,hN,hV,h0V,_,hRa,_,hQa,_,hR0,_,hQ0,hinv,hentry,hcompat,A,D⟩ :=
    exists_classicalHill_twoWeighted_period_inverse
  refine ⟨N,V,R,hN,hV,h0V,hRa,hR0,?_,?_⟩
  · intro n k q hq
    exact D.normalizedNumerator_period n k q hq T R (fun m j => (hentry q hq m j).1) (hinv q hq).1
  intro n
  exact D.exists_actual_simple_normalized_zero_family R Q hRa hQa (fun q hq => (hinv q hq).2.2.2.2.2) hQ0 hcompat n

end NLS.KdV
