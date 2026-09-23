import NLS.ZakharovShabat.ClassicalSeparatedCharacteristics
import NLS.ZakharovShabat.ClassicalChainTaylor
import NLS.ZakharovShabat.ClassicalFiniteChains
import NLS.ComplexAnalysis.AnalyticScalarJetOrder

/-!
# Scalar Taylor jets of the classical separated characteristic

The normalized initial vector spans the one-dimensional separated initial
condition. Evaluating its classical solution chain at the opposite endpoint
and taking the scalar endpoint defect gives an actual convergent Taylor
series. Its finite scalar convolution kernels detect the analytic order of
the separated characteristic.
-/

noncomputable section
open Set Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The separated endpoint condition as a continuous scalar functional. -/
def separatedEndpointDefectCLM (b : BoundaryCondition) : (ℂ × ℂ) →L[ℂ] ℂ :=
  ({ toFun := fun v => v.1 - extensionSign b * v.2
     map_add' := by intro u v; dsimp; ring
     map_smul' := by intro c v; dsimp; ring } : (ℂ × ℂ) →ₗ[ℂ] ℂ).toContinuousLinearMap

/-- The scalar defect for the normalized classical solution. -/
def classicalSeparatedEndpointDefect (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (z : ℂ) : ℂ :=
  separatedEndpointDefectCLM b (classicalSolution Φ z (1,extensionSign b) 1)

/-- The endpoint defect differs from the source-normalized characteristic by `-2i`. -/
theorem classicalSeparatedEndpointDefect_eq (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalSeparatedEndpointDefect b Φ z = -(2*I)*classicalSeparatedCharacteristic b Φ z := by
  have hd : (2*I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) I_ne_zero
  unfold classicalSeparatedEndpointDefect
  change (classicalSolution Φ z (1,extensionSign b) 1).1 -
    extensionSign b * (classicalSolution Φ z (1,extensionSign b) 1).2 = _
  rw [classicalSolution_eq_columns Φ z (1,extensionSign b) ⟨1,by constructor <;> norm_num⟩]
  simp only [classicalSeparatedCharacteristic,classicalMonodromy,classicalFundamentalMatrix,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,one_mul,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  cases b <;> simp only [extensionSign,one_mul,neg_one_mul] <;> field_simp [hd] <;> ring

/-- The convergent scalar endpoint series is obtained by evaluating the whole-curve chain series. -/
def classicalSeparatedEndpointSeries (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (z : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  ((separatedEndpointDefectCLM b).comp
    (ContinuousMap.evalCLM ℂ (⟨1,by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1))).compFormalMultilinearSeries
      (classicalChainSeries Φ z (1,extensionSign b))

/-- Its coefficients are the signed original forced-chain endpoint defects. -/
theorem classicalSeparatedEndpointSeries_apply (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℕ) (w : Fin n → ℂ) :
    classicalSeparatedEndpointSeries b Φ z n w =
      (∏ i, w i) * (-1 : ℂ)^n *
        separatedEndpointDefectCLM b
          (classicalChainCurve Φ z n (1,extensionSign b) ⟨1,by constructor <;> norm_num⟩) := by
  change separatedEndpointDefectCLM b
      ((ContinuousMap.evalCLM ℂ (⟨1,by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1))
        (classicalChainSeries Φ z (1,extensionSign b) n w)) = _
  rw [classicalChainSeries_apply]
  simp only [map_smul,ContinuousMap.evalCLM_apply,smul_eq_mul]
  ring

/-- The scalar series converges to the actual separated endpoint defect. -/
theorem hasFPowerSeriesOnBall_classicalSeparatedEndpointDefect (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    HasFPowerSeriesOnBall (classicalSeparatedEndpointDefect b Φ)
      (classicalSeparatedEndpointSeries b Φ z) z (classicalChainRadius Φ z) := by
  have h := ((separatedEndpointDefectCLM b).comp
    (ContinuousMap.evalCLM ℂ (⟨1,by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1))).comp_hasFPowerSeriesOnBall
      (hasFPowerSeriesOnBall_classicalSolutionCurve Φ z (1,extensionSign b))
  convert h using 1
  · funext w
    simp only [classicalSeparatedEndpointDefect,Function.comp_def,ContinuousLinearMap.comp_apply,
      ContinuousMap.evalCLM_apply,classicalSolutionCurve_apply]
  · rfl

/-- The formal endpoint series has exactly the analytic order of the source characteristic. -/
theorem order_classicalSeparatedEndpointSeries (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)).order =
      analyticOrderAt (classicalSeparatedCharacteristic b Φ) z := by
  rw [order_scalarFormalTaylor
    (hasFPowerSeriesOnBall_classicalSeparatedEndpointDefect b Φ z).hasFPowerSeriesAt]
  have hc : (-(2*I) : ℂ) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (by norm_num) I_ne_zero)
  have hconst : analyticOrderAt (fun _ : ℂ => -(2*I)) z = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hc)
  have han : AnalyticAt ℂ (classicalSeparatedCharacteristic b Φ) z :=
    (analyticOnNhd_classicalSeparatedCharacteristic_joint b (z,Φ) (mem_univ _)).comp
      (f := fun w : ℂ => (w,Φ)) (analyticAt_id.prod analyticAt_const)
  rw [show classicalSeparatedEndpointDefect b Φ =
      (fun _ : ℂ => -(2*I)) * classicalSeparatedCharacteristic b Φ from
        funext (fun w => by simp [classicalSeparatedEndpointDefect_eq]),
    analyticOrderAt_mul analyticAt_const han,
    hconst,zero_add]

/-- Scalar Taylor nullity is the truncated analytic order of the classical separated characteristic. -/
theorem finrank_classicalSeparatedTaylorKernel (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (m N : ℕ)
    (hm : analyticOrderAt (classicalSeparatedCharacteristic b Φ) z = m) :
    Module.finrank ℂ (LinearMap.ker
      (scalarTaylorJetMap (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) N)) =
        min N m :=
  finrank_ker_scalarTaylorJetMap _ m
    ((order_classicalSeparatedEndpointSeries b Φ z).trans hm) N

/-- A scalar initial jet, alternated for the original `z-L` chain recursion. -/
def separatedSignedInitialJet (b : BoundaryCondition) (N : ℕ) (w : Fin N → ℂ)
    (j : ℕ) : ℂ × ℂ :=
  (-1 : ℂ)^j • ((if h : j < N then w ⟨j,h⟩ else 0) • (1,extensionSign b))

private theorem classicalChainCurve_smul_initial (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (n : ℕ) (c : ℂ) (v : ℂ × ℂ) :
    classicalChainCurve Φ z n (c • v) = c • classicalChainCurve Φ z n v := by
  have hconst : ContinuousMap.const (Icc (0 : ℝ) 1) (c • v) =
      c • ContinuousMap.const (Icc (0 : ℝ) 1) v := by ext t <;> simp
  simp only [classicalChainCurve,classicalSolutionCurve_eq_inverse,hconst,map_smul]

/-- Finite scalar Taylor convolution is the signed endpoint defect of the corresponding original chain. -/
theorem scalarTaylorJetMap_classicalSeparated_eq_chainEndpoint
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (N : ℕ) (w : Fin N → ℂ) (k : Fin N) :
    scalarTaylorJetMap (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) N w k =
      (-1 : ℂ)^k.val * separatedEndpointDefectCLM b
        (classicalJetCurve Φ z (separatedSignedInitialJet b N w) k.val
          ⟨1,by constructor <;> norm_num⟩) := by
  rw [scalarTaylorJetMap_apply_eq_sum,classicalJetCurve_eq_sum]
  simp only [ContinuousMap.sum_apply,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k.val := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hlt : k.val-j < N := (Nat.sub_le _ _).trans_lt k.isLt
  rw [coeff_scalarFormalTaylor,classicalSeparatedEndpointSeries_apply]
  simp only [Finset.prod_const_one,one_mul,separatedSignedInitialJet,dif_pos hlt,
    classicalChainCurve_smul_initial,map_smul,ContinuousMap.smul_apply,smul_eq_mul]
  have hsign : (-1 : ℂ)^j * (-1 : ℂ)^(k.val-j) = (-1 : ℂ)^k.val := by
    rw [← pow_add,Nat.add_sub_of_le hjk]
  have heven : (-1 : ℂ)^((k.val-j)*2) = 1 := by
    rw [mul_comm,pow_mul]
    norm_num
  rw [← hsign]
  ring_nf
  simp [heven]

/-- Every prescribed chain initial value satisfies the separated condition at the left endpoint. -/
theorem separatedSignedInitialJet_left_condition (b : BoundaryCondition)
    (N : ℕ) (w : Fin N → ℂ) (j : ℕ) :
    separatedEndpointDefectCLM b (separatedSignedInitialJet b N w j) = 0 := by
  unfold separatedSignedInitialJet
  simp only [map_smul]
  have h : separatedEndpointDefectCLM b (1,extensionSign b) = 0 := by
    change (1 : ℂ) - extensionSign b * extensionSign b = 0
    rw [extensionSign_sq]
    ring
  simp [h]

/-- The finite scalar Taylor kernel is exactly the system of separated endpoint conditions
for the forced chain with prescribed scalar initial values. -/
theorem mem_ker_classicalSeparatedTaylorJetMap_iff (b : BoundaryCondition)
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (N : ℕ) (w : Fin N → ℂ) :
    w ∈ LinearMap.ker
      (scalarTaylorJetMap (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) N) ↔
        ∀ k : Fin N,
          separatedEndpointDefectCLM b
            (classicalJetCurve Φ z (separatedSignedInitialJet b N w) k.val
              ⟨1,by constructor <;> norm_num⟩) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h k
    have hk := congrFun h k
    rw [scalarTaylorJetMap_classicalSeparated_eq_chainEndpoint] at hk
    exact (mul_eq_zero.mp hk).resolve_left (pow_ne_zero _ (by norm_num))
  · intro h
    funext k
    change scalarTaylorJetMap
      (scalarFormalTaylor (classicalSeparatedEndpointSeries b Φ z)) N w k = 0
    rw [scalarTaylorJetMap_classicalSeparated_eq_chainEndpoint,h k,mul_zero]

end NLS.ZakharovShabat
