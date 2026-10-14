import NLS.SequenceSpaces.QuarterPowerWitness
import NLS.ZakharovShabat.SourceBirkhoffInverseChart
import NLS.ZakharovShabat.SourceBirkhoffImageInverse
import NLS.ZakharovShabat.SourceBirkhoffCoordinateBound

/-!
# Actual small real potentials with squared gaps outside ℓ²

A real ℓ⁸ sequence with nonsummable fourth powers can be scaled into
the target of the actual inverse Birkhoff chart. The exact action-radius
identity and uniformly bounded normalized-action roots then force the
squared spectral gaps of the inverse potential to fail ℓ² membership.
The source can be chosen in every prescribed open neighborhood of zero.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceGapWitnessEight : Fact (1 ≤ (8 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Failure of stronger squared-gap summability occurs for genuine real
sources arbitrarily near the free potential in the original ℓ⁸ topology. -/
theorem exists_near_zero_real_source_squaredGap_not_memℓp_two
    (U : Set (CoeffPair 8)) (hU : IsOpen U) (hzero : (0 : CoeffPair 8) ∈ U) :
    ∃ ψ : CoeffPair 8, ψ ∈ U ∧ IsRealType (CoeffPair.toMax 8 ψ) ∧
      ¬ Memℓp (fun n : ℤ => (sourcePeriodicGapDisplacement (p := 8)
        (by norm_num) (by norm_num) ψ n)^2) 2 := by
  let hp : (8 : ℝ≥0∞) ≠ ⊤ := by norm_num
  let hp1 : (1 : ℝ≥0∞) < 8 := by norm_num
  obtain ⟨Vr,hVr,hzeroR,A,hA,hroot⟩ :=
    exists_local_uniform_sourceNormalizedActionRoot_bound hp hp1 0 (by simp)
  obtain ⟨Vf,hVf,hzeroF,_,hfactor⟩ :=
    exists_local_sourceNormalizedActionRoot_allIndices_analytic hp hp1 0 (by simp)
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  obtain ⟨C⟩ := D.exists_inverseChart 0 (U ∩ (Vr ∩ Vf))
    (hU.inter (hVr.inter hVf)) ⟨hzero,hzeroR,hzeroF⟩
  let F : ℝ → Coeff 8 × Coeff 8 := fun t =>
    (RealCoeff.complexCLM 8 (t • quarterPowerCoeff),0)
  have hF : Continuous F := by fun_prop
  have hzeroT : F 0 ∈ C.target := by
    simpa only [F,zero_smul,map_zero,D.birkhoff_map_zero,ZeroMemClass.coe_zero] using! C.center_mem
  obtain ⟨δ,hδ,hδT⟩ := Metric.isOpen_iff.mp (C.target_open.preimage hF) 0 hzeroT
  let t := δ/2
  have ht : 0 < t := by dsimp [t]; positivity
  have htT : F t ∈ C.target := hδT (by
    change dist t (0 : ℝ) < δ
    rw [dist_zero_right,Real.norm_of_nonneg ht.le]
    dsimp [t]
    linarith)
  let ψ := C.inverse (F t)
  have hψ := C.image_subset htT
  refine ⟨ψ,hψ.2.1,?_,?_⟩
  · exact C.real_preserving (t • quarterPowerCoeff,0) (by simpa [F] using htT)
  · intro hgap
    apply not_memℓp_smul_quarterPowerWitness_sq t ht.ne'
    have hdom := hgap.const_smul ((A^2/2 : ℝ) : ℂ)
    apply hdom.mono'
    intro n
    have ha := C.action_eq (F t) htT n
    have hf := hfactor ψ hψ.2.2.2 n
    have hr := hroot ψ hψ.2.2.1 n
    have he : ((t * quarterPowerWitness n : ℝ) : ℂ)^2 =
        (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
          (sourceNormalizedActionRoot hp hp1 n ψ)^2 / 2 := by
      simp only [F,RealCoeff.complexCLM_apply,lp.coeFn_smul,Pi.smul_apply,
        smul_eq_mul,quarterPowerCoeff_apply,lp.coeFn_zero,Pi.zero_apply,zero_pow,
        ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,add_zero] at ha
      rw [hf.1,hf.2] at *
      linear_combination 2 * ha.symm
    rw [he,norm_div,norm_mul]
    simp only [Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ A^2/2),norm_pow]
    norm_num only [Complex.norm_ofNat]
    have hs : ‖sourceNormalizedActionRoot hp hp1 n ψ‖^2 ≤ A^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hr 2
    nlinarith [sq_nonneg ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖]

end NLS.ZakharovShabat
