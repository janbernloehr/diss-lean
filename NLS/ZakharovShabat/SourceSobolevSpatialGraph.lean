import NLS.ZakharovShabat.SourceSobolevMomentumDifferential

/-! # Bounded recovery of H¹ from a source and its spatial derivative

The explicit Fourier multiplier recovers H¹ coefficients from an L² pair
and its period-one derivative. The recovery operator is bounded and linear.
A cotangent integration-by-parts identity supplies precisely this graph
condition for the original reflected Hamiltonian vector.
-/
noncomputable section
open Set Filter Topology Complex
open NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The period-one derivative of a left-component mode has its signed Fourier symbol. -/
theorem sourceSobolevSpatialDerivative_mode_left (k : ℤ) :
    sourceSobolevSpatialDerivative (scalarMode k 1,0) =
      (I*2*(Real.pi : ℂ)*k) • CoeffPair.inlCLM (lp.single 2 k 1) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext m
  · change (2 : ℂ)*(I*(Real.pi : ℂ)*m*(scalarMode k 1).val m) =
      (I*2*(Real.pi : ℂ)*k)*(lp.single 2 k 1 : Coeff 2) m
    simp only [scalarMode_apply,lp.single_apply,Pi.single_apply]
    split_ifs with hm
    · subst m; ring
    · simp
  · change periodOneDerivative (0 : ScalarDomain 2) m = _
    simp

/-- The period-one derivative of a right-component mode has the same signed symbol. -/
theorem sourceSobolevSpatialDerivative_mode_right (k : ℤ) :
    sourceSobolevSpatialDerivative (0,scalarMode k 1) =
      (I*2*(Real.pi : ℂ)*k) • CoeffPair.inrCLM (lp.single 2 k 1) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext m
  · change periodOneDerivative (0 : ScalarDomain 2) m = _
    simp
  · change (2 : ℂ)*(I*(Real.pi : ℂ)*m*(scalarMode k 1).val m) =
      (I*2*(Real.pi : ℂ)*k)*(lp.single 2 k 1 : Coeff 2) m
    simp only [scalarMode_apply,lp.single_apply,Pi.single_apply]
    split_ifs with hm
    · subst m; ring
    · simp

/-- An integration-by-parts identity controls the differentiated coefficients of the reflected Hamiltonian vector. -/
theorem hamiltonian_spatial_coefficients (L K : CoeffPair 2 →L[ℂ] ℂ)
    (h : ∀ v : ScalarDomain 2 × ScalarDomain 2,
      L (sourceSobolevSpatialDerivative v) = -K (sobolevSourceInclusion v)) (m : ℤ) :
    I*2*(Real.pi : ℂ)*m*(sourceHamiltonianDirection le_rfl L).fst m =
      (sourceHamiltonianDirection le_rfl K).fst m ∧
    I*2*(Real.pi : ℂ)*m*(sourceHamiltonianDirection le_rfl L).snd m =
      (sourceHamiltonianDirection le_rfl K).snd m := by
  have hl := h (scalarMode (-m) 1,0)
  have hr := h (0,scalarMode (-m) 1)
  rw [sourceSobolevSpatialDerivative_mode_left,map_smul,smul_eq_mul] at hl
  rw [sourceSobolevSpatialDerivative_mode_right,map_smul,smul_eq_mul] at hr
  have hil : sobolevSourceInclusion (scalarMode (-m) 1,0) = CoeffPair.inlCLM (lp.single 2 (-m) 1) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext k <;> simp [lp.single_apply,Pi.single_apply]
  have hir : sobolevSourceInclusion (0,scalarMode (-m) 1) = CoeffPair.inrCLM (lp.single 2 (-m) 1) := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext k <;> simp [lp.single_apply,Pi.single_apply]
  rw [hil,Int.cast_neg] at hl
  rw [hir,Int.cast_neg] at hr
  constructor
  · change I*2*(Real.pi : ℂ)*m*(-I*(CoeffPair.cotangentCoefficients le_rfl L).2 (-m)) =
      -I*(CoeffPair.cotangentCoefficients le_rfl K).2 (-m)
    rw [CoeffPair.cotangentCoefficients_snd,CoeffPair.cotangentCoefficients_snd]
    linear_combination I*hr
  · change I*2*(Real.pi : ℂ)*m*(I*(CoeffPair.cotangentCoefficients le_rfl L).1 (-m)) =
      I*(CoeffPair.cotangentCoefficients le_rfl K).1 (-m)
    rw [CoeffPair.cotangentCoefficients_fst,CoeffPair.cotangentCoefficients_fst]
    linear_combination -I*hl

/-- Raw and differentiated L² coefficients construct an H¹ lift with its exact spatial derivative. -/
theorem exists_hamiltonian_sobolev_of_spatial_identity (L K : CoeffPair 2 →L[ℂ] ℂ)
    (h : ∀ v : ScalarDomain 2 × ScalarDomain 2,
      L (sourceSobolevSpatialDerivative v) = -K (sobolevSourceInclusion v)) :
    ∃ v : ScalarDomain 2 × ScalarDomain 2,
      sobolevSourceInclusion v = sourceHamiltonianDirection le_rfl L ∧
      sourceSobolevSpatialDerivative v = sourceHamiltonianDirection le_rfl K := by
  let X := sourceHamiltonianDirection le_rfl L
  let Y := sourceHamiltonianDirection le_rfl K
  have hm := hamiltonian_spatial_coefficients L K h
  have hx : Memℓp (fun m : ℤ => I*(Real.pi : ℂ)*m*X.fst m) 2 := by
    convert! (lp.memℓp Y.fst).const_mul (1/2 : ℂ) using 1
    funext m
    change I*(Real.pi : ℂ)*m*X.fst m = (1/2 : ℂ)*Y.fst m
    rw [← (hm m).1]
    ring
  have hy : Memℓp (fun m : ℤ => I*(Real.pi : ℂ)*m*X.snd m) 2 := by
    convert! (lp.memℓp Y.snd).const_mul (1/2 : ℂ) using 1
    funext m
    change I*(Real.pi : ℂ)*m*X.snd m = (1/2 : ℂ)*Y.snd m
    rw [← (hm m).2]
    ring
  let v : ScalarDomain 2 × ScalarDomain 2 :=
    (⟨X.fst,memlp_sobolev_weight_of_derivative (lp.memℓp X.fst) hx⟩,
     ⟨X.snd,memlp_sobolev_weight_of_derivative (lp.memℓp X.snd) hy⟩)
  refine ⟨v,?_,?_⟩
  · apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext m
    · change (sobolevSourceInclusion v).fst m = X.fst m
      simp only [sobolevSourceInclusion_fst,v]
    · change (sobolevSourceInclusion v).snd m = X.snd m
      simp only [sobolevSourceInclusion_snd,v]
  · apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext m
    · change (2 : ℂ)*(I*(Real.pi : ℂ)*m*X.fst m) = Y.fst m
      convert (hm m).1 using 1
      ring
    · change (2 : ℂ)*(I*(Real.pi : ℂ)*m*X.snd m) = Y.snd m
      convert (hm m).2 using 1
      ring
/-- The bounded sign multiplier converts a period-one derivative into the homogeneous H¹ weight. -/
def spatialGraphSymbol : Coeff ⊤ :=
  ⟨fun n => if 0 ≤ n then -I/(2*(Real.pi : ℂ)) else I/(2*(Real.pi : ℂ)), by
    apply memℓp_infty
    refine ⟨‖I/(2*(Real.pi : ℂ))‖,?_⟩
    rintro _ ⟨n,rfl⟩
    dsimp only
    split_ifs <;> simp⟩

/-- Bounded linear recovery of H¹ coefficients from a scalar L² derivative graph. -/
def spatialGraphRecovery : (Coeff 2 × Coeff 2) →L[ℂ] ScalarDomain 2 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℂ _ _)+
      (Coeff.multiplierCLM spatialGraphSymbol).comp (ContinuousLinearMap.snd ℂ _ _))

/-- On the actual derivative graph, recovery preserves every raw Fourier coefficient. -/
theorem spatialGraphRecovery_coeff (a b : Coeff 2)
    (h : ∀ n : ℤ, b n = 2*I*(Real.pi : ℂ)*n*a n) (n : ℤ) :
    (spatialGraphRecovery (a,b)).val n = a n := by
  change (a n+spatialGraphSymbol n*b n)/(Weight.sobolev 1 n : ℂ) = a n
  rw [div_eq_iff (Weight.complex_ne_zero _ _),h n]
  change a n+(if 0 ≤ n then -I/(2*(Real.pi : ℂ)) else I/(2*(Real.pi : ℂ)))*
      (2*I*(Real.pi : ℂ)*n*a n) = a n*(Weight.sobolev 1 n : ℂ)
  simp only [Weight.sobolev_apply,Real.rpow_one,Complex.ofReal_add,Complex.ofReal_one]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases hn : 0 ≤ n
  · rw [if_pos hn,abs_of_nonneg (by exact_mod_cast hn : (0 : ℝ) ≤ n)]
    push_cast
    field_simp
    simp only [I_sq]
    ring
  · rw [if_neg hn,abs_of_neg (by exact_mod_cast lt_of_not_ge hn : (n : ℝ) < 0)]
    push_cast
    field_simp
    simp only [I_sq]
    ring


/-- The same bounded recovery in both components of the original source space. -/
def sourceSpatialGraphRecovery : (CoeffPair 2 × CoeffPair 2) →L[ℂ]
    (ScalarDomain 2 × ScalarDomain 2) :=
  let fst := (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2)).comp
    (CoeffPair.toMax 2).toContinuousLinearMap
  let snd := (ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2)).comp
    (CoeffPair.toMax 2).toContinuousLinearMap
  let P := ContinuousLinearMap.fst ℂ (CoeffPair 2) (CoeffPair 2)
  let Q := ContinuousLinearMap.snd ℂ (CoeffPair 2) (CoeffPair 2)
  (spatialGraphRecovery.comp ((fst.comp P).prod (fst.comp Q))).prod
    (spatialGraphRecovery.comp ((snd.comp P).prod (snd.comp Q)))

/-- Bounded graph recovery is a left inverse of the actual scalar derivative graph. -/
theorem spatialGraphRecovery_leftInverse (a : ScalarDomain 2) :
    spatialGraphRecovery (scalarInclusion a,periodOneDerivative a) = a := by
  apply Subtype.ext
  funext n
  exact (spatialGraphRecovery_coeff _ _ (fun k => by simp only
    [periodOneDerivative_apply,scalarInclusion_apply]) n).trans (scalarInclusion_apply a n)

/-- The full original source derivative graph recovers its H¹ source exactly. -/
theorem sourceSpatialGraphRecovery_leftInverse (a : ScalarDomain 2 × ScalarDomain 2) :
    sourceSpatialGraphRecovery (sobolevSourceInclusion a,sourceSobolevSpatialDerivative a) = a := by
  apply Prod.ext
  · exact spatialGraphRecovery_leftInverse a.1
  · exact spatialGraphRecovery_leftInverse a.2

/-- One fixed operator norm controls the H¹ norm by the L² source and its spatial derivative. -/
theorem norm_sobolev_source_le_graph (a : ScalarDomain 2 × ScalarDomain 2) :
    ‖a‖ ≤ ‖sourceSpatialGraphRecovery‖ * max ‖sobolevSourceInclusion a‖ ‖sourceSobolevSpatialDerivative a‖ := by
  have h := sourceSpatialGraphRecovery.le_opNorm (sobolevSourceInclusion a,sourceSobolevSpatialDerivative a)
  rwa [sourceSpatialGraphRecovery_leftInverse] at h
end NLS.ZakharovShabat
