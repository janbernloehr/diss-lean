import NLS.ZakharovShabat.SourceHamiltonianOriginalNonextension
import NLS.ZakharovShabat.SourceHilbertActionReductionFiniteGap

/-!
# Corrections to the Section 18 Hamiltonian formulas

Single nonnegative actions are realized by actual real finite-gap H¹ sources.
They certify the missing weighted subtraction on p. 84 and identify the full
physical energy on each action axis. Its second derivative is +2, whereas
−2 is the diagonal Hessian of the corrected Hamiltonian H*.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4 : ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

/-- Actual H¹ realization, retaining the original actions, physical mass, and weighted sum. -/
theorem exists_realSobolev_single_action (m : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    ∃ a : realTypeSobolevSourceLocus,
      (∀ n, sourceComplexAction (by simp) (by norm_num) n (sobolevSourceInclusion a.val) =
        if n = m then (t : ℂ) else 0) ∧
      periodOneSobolevMass a.val = (t : ℂ) ∧
      sourceSobolevWeightedActionSum a.val = (2*(Real.pi : ℂ)*m)^2*t := by
  let b : RealCoeff 1 := lp.single 1 m t
  have hb (n : ℤ) : 0 ≤ b n := by
    by_cases hn : n = m <;> simp [b,lp.single_apply,hn,ht]
  obtain ⟨φ,hφ⟩ := exists_hilbertSource_of_nonnegative_actions b hb
  have ha (n : ℤ) : sourceComplexAction (by simp) (by norm_num) n φ.val =
      if n = m then (t : ℂ) else 0 := by
    rw [hφ n]
    by_cases hn : n = m <;> simp [b,lp.single_apply,hn]
  have hr (n : ℤ) : sourceRealAction (by simp) (by norm_num) φ.val φ.property n =
      if n = m then (t : ℂ) else 0 := by
    exact (sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n φ.val φ.property).symm.trans (ha n)
  have hclosed (n : ℤ) (hn : n ≠ m) : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 := by
    have he := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero
      (by simp) (by norm_num) φ.val φ.property n).2.2.mp (by simp [hr n,hn])
    simpa only [sourcePeriodicGapDisplacement_apply] using he
  have hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num) := by
    apply (Set.finite_singleton m).subset
    intro n hn
    by_contra hnm
    exact hn (hclosed n hnm)
  let a := sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf
  have hi : sobolevSourceInclusion a = φ.val := sobolevSourceInclusion_sourceFiniteGapSobolevPair φ hf
  have har : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a)) := by rw [hi]; exact φ.property
  refine ⟨⟨a,har⟩,?_,?_,?_⟩
  · intro n
    rw [hi]
    exact ha n
  · rw [periodOneSobolevMass_sourceFiniteGapSobolevPair]
    rw [sourceFiniteGapNLSHamiltonian_one_eq_sum φ hf {m} (by simpa using hclosed)]
    simp [hr]
  · rw [sourceSobolevWeightedActionSum_eq_tsum a har]
    simp only [sourceSobolevWeightedAction,hi,ha]
    simp

variable {W₀ W V : Set (CoeffPair 4)} {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {T : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}

/-- The omitted term is nonzero on a constructed actual source with action I₁=1. -/
theorem SourceOriginalHamiltonianData.printed_subtraction_counterexample
    (Q : SourceOriginalHamiltonianData D T F H) :
    ∃ a : realTypeSobolevSourceLocus,
      sourceSobolevWeightedActionSum a.val = 4*(Real.pi : ℂ)^2 ∧
      H (sourceActionSequence (q := 2) (by simp) (by norm_num) s (sobolevSourceFL4 a.val)) ≠
        periodOneSobolevHamiltonian a.val - 2*(periodOneSobolevMass a.val)^2 := by
  obtain ⟨a,_,_,hw⟩ := exists_realSobolev_single_action 1 1 (by norm_num)
  have hw' : sourceSobolevWeightedActionSum a.val = 4*(Real.pi : ℂ)^2 := by rw [hw]; norm_num; ring
  refine ⟨a,hw',?_⟩
  rw [Q.physical a,sourceSobolevPhysicalCorrection,hw']
  intro he
  have hz : 4*(Real.pi : ℂ)^2 = 0 := sub_eq_self.mp he
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact (mul_ne_zero (by norm_num) (pow_ne_zero _ hp)) hz

/-- Restoring the mass term changes the frequency derivative to 4−2δₙₘ. -/
theorem SourceOriginalHamiltonianData.restored_frequency_derivative
    (Q : SourceOriginalHamiltonianData D T F H) (m n : ℤ) :
    HasDerivAt (fun z : ℂ => F (z • lp.single 2 m 1) n + 4*z + (2*(n:ℂ)*Real.pi)^2)
      (4 - if n = m then 2 else 0) 0 := by
  let e : Coeff 2 := lp.single 2 m 1
  let L := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n
  have hline : HasDerivAt (fun z : ℂ => z • e) e 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const e
  have hF : HasFDerivAt F (fderiv ℂ F 0) ((0 : ℂ) • e) := by
    simpa using (Q.frequency.analytic 0 Q.frequency.zero_mem).differentiableAt.hasFDerivAt
  have hd := L.hasFDerivAt.comp_hasDerivAt 0 (hF.comp_hasDerivAt 0 hline)
  have hd' := (hd.add ((hasDerivAt_id (0 : ℂ)).const_mul 4)).add_const ((2*(n:ℂ)*Real.pi)^2)
  convert! hd' using 1
  · rw [Q.frequency.derivative_zero (by norm_num)]
    change (4 - if n = m then 2 else 0) = (-2 : ℂ)*(lp.single 2 m 1 : Coeff 2) n + 4*1
    by_cases hn : n = m <;> norm_num [lp.single_apply,hn]

/-- The full physical energy restricted to one action axis. -/
def sourceSingleActionFullHamiltonian (H : Coeff 2 → ℂ) (m : ℤ) (z : ℂ) : ℂ :=
  H (z • lp.single 2 m 1) + 2*z^2 + (2*(m:ℂ)*Real.pi)^2*z

/-- Every nonnegative point of the action axis recovers the full physical H¹ energy. -/
theorem SourceOriginalHamiltonianData.single_action_physical_energy
    (Q : SourceOriginalHamiltonianData D T F H) (m : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    ∃ a : realTypeSobolevSourceLocus,
      sourceActionSequence (q := 2) (by simp) (by norm_num) s (sobolevSourceFL4 a.val) =
        (t : ℂ) • lp.single 2 m 1 ∧
      sourceSingleActionFullHamiltonian H m t = periodOneSobolevHamiltonian a.val := by
  obtain ⟨a,ha,hm,hw⟩ := exists_realSobolev_single_action m t ht
  have he : sourceActionSequence (q := 2) (by simp) (by norm_num) s (sobolevSourceFL4 a.val) =
      (t : ℂ) • lp.single 2 m 1 := by
    ext n
    have he0 := D.complex.actionSequence_apply (q := 2) (sobolevSourceFL4 a.val)
      (D.complex.real_subset (realSobolevSourceFL4 a).property) n
    have hc := sourceComplexAction_real_exponent (by simp) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)
      (by norm_num) (by norm_num) (by norm_num : (2 : ℝ≥0∞) ≤ 4) n
      (⟨sobolevSourceInclusion a.val,a.property⟩ : realTypeSourceLocus 2)
    change sourceComplexAction (by simp) (by norm_num) n (sobolevSourceInclusion a.val) =
      sourceComplexAction (by simp) (by norm_num) n (sobolevSourceFL4 a.val) at hc
    calc
      _ = sourceComplexAction (by simp) (by norm_num) n (sobolevSourceFL4 a.val) := he0
      _ = if n = m then (t : ℂ) else 0 := hc.symm.trans (ha n)
      _ = _ := by
        change (if n = m then (t : ℂ) else 0) = (t : ℂ)*(lp.single 2 m 1 : Coeff 2) n
        by_cases hn : n = m <;> simp [lp.single_apply,hn]
  refine ⟨a,he,?_⟩
  have hp := Q.physical a
  rw [he,sourceSobolevPhysicalCorrection,hm,hw] at hp
  rw [sourceSingleActionFullHamiltonian,hp]
  ring

/-- The restored frequency differentiates the full energy along the action axis. -/
theorem SourceOriginalHamiltonianData.single_action_energy_hasDerivAt
    (Q : SourceOriginalHamiltonianData D T F H) (m : ℤ) (z : ℂ)
    (hz : z • lp.single 2 m 1 ∈ T) :
    HasDerivAt (sourceSingleActionFullHamiltonian H m)
      (F (z • lp.single 2 m 1) m + 4*z + (2*(m:ℂ)*Real.pi)^2) z := by
  have hline : HasDerivAt (fun w : ℂ => w • (lp.single 2 m 1 : Coeff 2)) (lp.single 2 m 1) z := by
    simpa using (hasDerivAt_id z).smul_const (lp.single 2 m 1 : Coeff 2)
  have hd := (Q.analytic _ hz).differentiableAt.hasFDerivAt.comp_hasDerivAt z hline
  have he : fderiv ℂ H (z • lp.single 2 m 1) (lp.single 2 m 1) = F (z • lp.single 2 m 1) m := by
    rw [← Coeff.scalarGradient_apply,← Q.gradient_eq hz]
  rw [he] at hd
  have hsq := ((hasDerivAt_id z).pow 2).const_mul 2
  have hlin := (hasDerivAt_id z).const_mul ((2*(m:ℂ)*Real.pi)^2)
  convert! (hd.add hsq).add hlin using 1
  simp only [id_eq]
  ring

/-- The actual full energy has diagonal Hessian +2 at zero, refuting the printed −2. -/
theorem SourceOriginalHamiltonianData.full_hessian_diagonal
    (Q : SourceOriginalHamiltonianData D T F H) (m : ℤ) :
    deriv (deriv (sourceSingleActionFullHamiltonian H m)) 0 = 2 := by
  have he : deriv (sourceSingleActionFullHamiltonian H m) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => F (z • lp.single 2 m 1) m + 4*z + (2*(m:ℂ)*Real.pi)^2) := by
    have ht : Tendsto (fun z : ℂ => z • (lp.single 2 m 1 : Coeff 2)) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun z : ℂ => z • (lp.single 2 m 1 : Coeff 2)) := by fun_prop
      simpa using hc.tendsto (0 : ℂ)
    filter_upwards [ht (Q.frequency.isOpen.mem_nhds Q.frequency.zero_mem)] with z hz
    exact (Q.single_action_energy_hasDerivAt m z hz).deriv
  have hd := (Q.restored_frequency_derivative m m).congr_of_eventuallyEq he
  convert! hd.deriv using 1
  norm_num

theorem SourceOriginalHamiltonianData.full_hessian_ne_printed
    (Q : SourceOriginalHamiltonianData D T F H) (m : ℤ) :
    deriv (deriv (sourceSingleActionFullHamiltonian H m)) 0 ≠ -2 := by
  rw [Q.full_hessian_diagonal m]
  norm_num

end NLS.ZakharovShabat
