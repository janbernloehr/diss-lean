import NLS.ZakharovShabat.NLSWKBComparison
import NLS.ComplexAnalysis.UnimodularTraceError

/-! # All-order physical Hamiltonian asymptotics of the discriminant

The actual monodromy, rather than just the approximate solution, has
trace `2*cos(i*sigma_N)` to every inverse-frequency order on the real
spectral axis. Here `sigma_N` uses the Appendix H Hamiltonians.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The true initial-value map is complex linear in its second initial component. -/
theorem classicalSolution_one_snd (Φ : Curve (ℂ × ℂ)) (z v : ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSolution Φ z (1,v) t = classicalSolution Φ z (1,0) t+v • classicalSolution Φ z (0,1) t := by
  symm
  apply classicalSolution_unique Φ z (1,v)
    (fun x => classicalSolution Φ z (1,0) x+v • classicalSolution Φ z (0,1) x)
    ((continuous_classicalSolution Φ z (1,0)).add ((continuous_classicalSolution Φ z (0,1)).const_smul v)).continuousOn
    (by simp) _ t.property
  intro x _
  have hd := (hasDerivAt_classicalSolution Φ z (1,0) x).add
    ((hasDerivAt_classicalSolution Φ z (0,1) x).const_smul v)
  convert! hd using 1
  simp only [map_add,map_smul]

/-- The finite phase polynomial in the physical Hamiltonians. -/
def nlsHamiltonianPhase (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  -I*z+∑ k ∈ Finset.range N, I*classicalNLSHamiltonian a b (k+1)/(2*z)^(k+1)

/-- Every smooth periodic complex potential has the all-order discriminant
asymptotics required to identify the Hamiltonian Laurent coefficients. -/
theorem exists_classicalDiscriminant_hamiltonian_error_bound (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ |r| →
      ‖classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) r -
        2*cos (I*nlsHamiltonianPhase a b N r)‖ ≤ C/(2*|r|)^N := by
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  obtain ⟨D,hD,herr⟩ := exists_nlsWKBVector_endpoint_error_bound a b ha hb hpa hpb N
  obtain ⟨B,hB,hcarrier⟩ := exists_nlsWKBCarrier_real_bounds a b ha hb N
  let M := Real.exp ‖Φ‖
  refine ⟨(B+2*M)*D*B,by dsimp [M]; positivity,?_⟩
  intro r hr
  let m := exp (nlsHamiltonianPhase a b N r)
  let v := -I*nlsRiccatiApproximation a b N (2*I*(r : ℂ))⁻¹ 0
  have hm : m = nlsWKBCarrier a b N r 1 := (nlsWKBCarrier_one a b ha hb N r).symm
  have hmb := (hcarrier 1 ⟨zero_le_one,le_rfl⟩ r hr)
  rw [← hm] at hmb
  have hcol : ‖classicalSolution Φ r (0,1) 1‖ ≤ M := by
    have h := norm_classicalSolution_le_exp_im Φ r (0,1) ⟨1,⟨zero_le_one,le_rfl⟩⟩
    simpa only [Prod.norm_def,norm_zero,norm_one,max_eq_right zero_le_one,
      one_mul,ofReal_im,abs_zero,zero_add,mul_one] using h
  have he := herr r hr
  have hv : nlsWKBVector a b N r 0 = (1,v) := by simp [nlsWKBVector,v]
  change ‖classicalSolution Φ r (nlsWKBVector a b N r 0) 1-m • nlsWKBVector a b N r 0‖ ≤ _ at he
  rw [hv,classicalSolution_one_snd Φ r v ⟨1,⟨zero_le_one,le_rfl⟩⟩] at he
  have hdet := det_classicalMonodromy Φ r
  simp only [classicalMonodromy,classicalFundamentalMatrix,Matrix.det_fin_two_of] at hdet
  have ht := norm_unimodular_trace_error_le
    (classicalSolution Φ r (1,0) 1).1 (classicalSolution Φ r (0,1) 1).1
    (classicalSolution Φ r (1,0) 1).2 (classicalSolution Φ r (0,1) 1).2 m v
    hdet (exp_ne_zero _) M B (D/(2*|r|)^N) (Real.exp_pos _).le hB.le (by positivity)
    ((norm_fst_le _).trans hcol) ((norm_snd_le _).trans hcol) hmb.1 hmb.2 (by
      simpa only [Prod.norm_def,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,
        smul_eq_mul,mul_one,one_mul,mul_comm] using he)
  have hphase : 2*cos (I*nlsHamiltonianPhase a b N r) = m+m⁻¹ := by
    rw [mul_comm I,cos_mul_I,two_cosh,exp_neg]
  rw [hphase]
  simp only [classicalDiscriminant,classicalMonodromy,classicalFundamentalMatrix,Matrix.trace_fin_two,Matrix.of_apply]
  change ‖(classicalSolution Φ r (1,0) 1).1+(classicalSolution Φ r (0,1) 1).2-(m+m⁻¹)‖ ≤ _
  exact ht.trans_eq (by ring)

end NLS.ZakharovShabat
