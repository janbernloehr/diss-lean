import NLS.ZakharovShabat.ClassicalFiniteChains

/-!
# Boundary Taylor-jet equations for finite chains

The coefficients here are those of the actual convergent monodromy boundary
series. Alternating the initial data converts the original `z-L` recursion
into the ordinary convolution equations for these Taylor coefficients.
-/

noncomputable section
open Set Complex Matrix NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The usual two-by-two matrix action, using pair initial coordinates. -/
def classicalMatrixAction (M : Matrix (Fin 2) (Fin 2) ℂ) : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun v := (M 0 0*v.1+M 0 1*v.2,M 1 0*v.1+M 1 1*v.2)
  map_add' := by intro u v; apply Prod.ext <;> dsimp <;> ring
  map_smul' := by intro c v; apply Prod.ext <;> dsimp <;> ring

/-- Pair coordinates give exactly the standard matrix-vector product. -/
theorem classicalMatrixAction_eq_mulVec (M : Matrix (Fin 2) (Fin 2) ℂ) (v : ℂ × ℂ) :
    ![(classicalMatrixAction M v).1,(classicalMatrixAction M v).2] = M *ᵥ ![v.1,v.2] := by
  ext i
  fin_cases i <;> simp [classicalMatrixAction,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail]

theorem classicalMatrixAction_smul (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) (v : ℂ × ℂ) :
    classicalMatrixAction (c • M) v = c • classicalMatrixAction M v := by
  apply Prod.ext <;> simp [classicalMatrixAction,Matrix.smul_apply] <;> ring

theorem classicalMatrixAction_sub (M N : Matrix (Fin 2) (Fin 2) ℂ) (v : ℂ × ℂ) :
    classicalMatrixAction (M-N) v = classicalMatrixAction M v-classicalMatrixAction N v := by
  apply Prod.ext <;> simp [classicalMatrixAction] <;> ring

@[simp] theorem classicalMatrixAction_one (v : ℂ × ℂ) : classicalMatrixAction 1 v = v := by
  apply Prod.ext <;> simp [classicalMatrixAction]

/-- The normalized chain matrix acts by the corresponding whole chain curve. -/
theorem classicalMatrixAction_chainMatrix (Φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℕ)
    (t : Icc (0 : ℝ) 1) (v : ℂ × ℂ) :
    classicalMatrixAction (classicalChainMatrix Φ z n t) v = classicalChainCurve Φ z n v t := by
  rw [classicalChainCurve_eq_columns Φ z n v]
  change (((classicalChainCurve Φ z n (1,0) t).1*v.1+(classicalChainCurve Φ z n (0,1) t).1*v.2),
    ((classicalChainCurve Φ z n (1,0) t).2*v.1+(classicalChainCurve Φ z n (0,1) t).2*v.2)) =
      v.1 • classicalChainCurve Φ z n (1,0) t + v.2 • classicalChainCurve Φ z n (0,1) t
  apply Prod.ext <;> dsimp <;> ring

/-- The ordinary finite convolution of boundary Taylor coefficients with an initial jet. -/
def classicalBoundaryJet (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) (w : ℕ → ℂ × ℂ) (n : ℕ) : ℂ × ℂ :=
  ∑ j ∈ Finset.range (n+1), classicalMatrixAction (classicalBoundarySeries Φ z σ j (fun _ => 1)) (w (n-j))

/-- Alternating the initial coefficients accounts for the sign of the original pencil `z-L`. -/
def signedInitialJet (v : ℕ → ℂ × ℂ) (n : ℕ) : ℂ × ℂ := (-1 : ℂ)^n • v n

/-- Changing from chain initial values to Taylor initial coefficients is an involution. -/
@[simp] theorem signedInitialJet_involutive (v : ℕ → ℂ × ℂ) : signedInitialJet (signedInitialJet v) = v := by
  funext n
  simp only [signedInitialJet,smul_smul,← mul_pow,neg_one_mul,neg_neg,one_pow,one_smul]

private theorem sign_product (n j : ℕ) (hj : j ≤ n) : (-1 : ℂ)^j * (-1 : ℂ)^(n-j) = (-1 : ℂ)^n := by
  rw [← pow_add,Nat.add_sub_of_le hj]

/-- The actual boundary Taylor convolution equals the signed endpoint defect of the original classical chain. -/
theorem classicalBoundaryJet_signed (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) (v : ℕ → ℂ × ℂ) (n : ℕ) :
    classicalBoundaryJet Φ z σ (signedInitialJet v) n = (-1 : ℂ)^n •
      (classicalJetCurve Φ z v n ⟨1,by constructor <;> norm_num⟩-σ • v n) := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hzero : classicalMatrixAction (classicalBoundarySeries Φ z σ 0 (fun _ => 1))
      (signedInitialJet v n) = (-1 : ℂ)^n • (classicalChainCurve Φ z 0 (v n) t-σ • v n) := by
    rw [classicalBoundarySeries_zero,signedInitialJet,map_smul,classicalMatrixAction_sub,classicalMatrixAction_smul,classicalMatrixAction_one]
    have hm : classicalMonodromy Φ z = classicalChainMatrix Φ z 0 t := (classicalChainMatrix_zero Φ z t).symm
    rw [hm,classicalMatrixAction_chainMatrix]
  have hpos (j : ℕ) (hj : j+1 ≤ n) :
      classicalMatrixAction (classicalBoundarySeries Φ z σ (j+1) (fun _ => 1))
        (signedInitialJet v (n-(j+1))) = (-1 : ℂ)^n • classicalChainCurve Φ z (j+1) (v (n-(j+1))) t := by
    rw [classicalBoundarySeries_succ]
    simp only [Finset.prod_const_one,signedInitialJet,classicalMatrixAction_smul,map_smul,
      smul_smul,classicalMatrixAction_chainMatrix]
    rw [one_mul,mul_comm,sign_product n (j+1) hj]
  unfold classicalBoundaryJet
  rw [Finset.sum_range_succ',Nat.sub_zero,hzero]
  rw [classicalJetCurve_eq_sum]
  change _ = (-1 : ℂ)^n • ((∑ j ∈ Finset.range (n+1), classicalChainCurve Φ z j (v (n-j))) t-σ • v n)
  rw [ContinuousMap.sum_apply,Finset.sum_range_succ',Nat.sub_zero]
  rw [show (∑ j ∈ Finset.range n, classicalMatrixAction (classicalBoundarySeries Φ z σ (j+1) (fun _ => 1))
      (signedInitialJet v (n-(j+1)))) =
      ∑ j ∈ Finset.range n, (-1 : ℂ)^n • classicalChainCurve Φ z (j+1) (v (n-(j+1))) t from
    Finset.sum_congr rfl (fun j hj => hpos j (by simpa using Finset.mem_range.mp hj))]
  rw [← Finset.smul_sum]
  module

/-- Vanishing of each Taylor-jet equation is exactly the corresponding chain endpoint condition. -/
theorem classicalBoundaryJet_signed_eq_zero_iff (Φ : Curve (ℂ × ℂ)) (z σ : ℂ)
    (v : ℕ → ℂ × ℂ) (n : ℕ) : classicalBoundaryJet Φ z σ (signedInitialJet v) n = 0 ↔
      classicalJetCurve Φ z v n ⟨1,by constructor <;> norm_num⟩ = σ • v n := by
  rw [classicalBoundaryJet_signed,smul_eq_zero]
  simp [sub_eq_zero]

end NLS.ZakharovShabat
