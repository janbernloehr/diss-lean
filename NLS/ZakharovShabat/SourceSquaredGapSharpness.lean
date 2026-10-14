import NLS.SequenceSpaces.StrictSquaredExponentWitness
import NLS.ZakharovShabat.SourceBirkhoffInverseChart
import NLS.ZakharovShabat.SourceBirkhoffImageInverse
import NLS.ZakharovShabat.SourceBirkhoffCoordinateBound
import NLS.ZakharovShabat.SourceSquaredGapRowLowerBound

/-!
# Sharp summability of actual squared gaps

Every exponent strictly below p/2 fails for some actual real potential
in every prescribed open neighborhood of zero. Real inverse Birkhoff
charts transfer explicit sequence-space witnesses to actual spectral data.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p r : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Squared gaps of actual real sources can fail every stronger positive
finite exponent, arbitrarily close to zero in the original topology. -/
theorem exists_near_zero_real_source_squaredGap_not_memℓp
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hr : 0 < r.toReal) (hrp : r < p/2)
    (U : Set (CoeffPair p)) (hU : IsOpen U) (hzero : (0 : CoeffPair p) ∈ U) :
    ∃ ψ : CoeffPair p, ψ ∈ U ∧ IsRealType (CoeffPair.toMax p ψ) ∧
      ¬ Memℓp (fun n : ℤ => (sourcePeriodicGapDisplacement hp hp1 ψ n)^2) r := by
  have hrf : r ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hr).2.ne
  have hrealp : 2*r.toReal < p.toReal := by
    have hh := (ENNReal.toReal_lt_toReal hrf (ENNReal.div_ne_top hp (by norm_num))).mpr hrp
    rw [ENNReal.toReal_div,ENNReal.toReal_ofNat] at hh
    linarith
  obtain ⟨Vr,hVr,hzeroR,A,hA,hroot⟩ :=
    exists_local_uniform_sourceNormalizedActionRoot_bound hp hp1 0 (by simp)
  obtain ⟨Vf,hVf,hzeroF,_,hfactor⟩ :=
    exists_local_sourceNormalizedActionRoot_allIndices_analytic hp hp1 0 (by simp)
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  obtain ⟨C⟩ := D.exists_inverseChart 0 (U ∩ (Vr ∩ Vf))
    (hU.inter (hVr.inter hVf)) ⟨hzero,hzeroR,hzeroF⟩
  let F : ℝ → Coeff p × Coeff p := fun t =>
    (RealCoeff.complexCLM p (t • squaredExponentCoeff hr hrealp),0)
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
  · exact C.real_preserving (t • squaredExponentCoeff hr hrealp,0) (by simpa [F] using htT)
  · intro hgap
    apply not_memℓp_smul_squaredExponentWitness_sq hr t ht.ne'
    have hdom := hgap.const_smul ((A^2/2 : ℝ) : ℂ)
    apply hdom.mono'
    intro n
    have ha := C.action_eq (F t) htT n
    have hf := hfactor ψ hψ.2.2.2 n
    have hr := hroot ψ hψ.2.2.1 n
    have he : ((t * squaredExponentWitness r.toReal n : ℝ) : ℂ)^2 =
        (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
          (sourceNormalizedActionRoot hp hp1 n ψ)^2 / 2 := by
      simp only [F,RealCoeff.complexCLM_apply,lp.coeFn_smul,Pi.smul_apply,
        smul_eq_mul,squaredExponentCoeff_apply,lp.coeFn_zero,Pi.zero_apply,zero_pow,
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
