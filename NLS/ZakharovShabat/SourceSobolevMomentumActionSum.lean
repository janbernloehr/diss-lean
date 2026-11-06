import NLS.ZakharovShabat.SourceSobolevBirkhoffTranslation
import NLS.ZakharovShabat.SourceHilbertActionRotation

/-! # The physical translation field as a convergent sum of action fields

The bounded Birkhoff inverse derivative transports the unconditional
Hilbert coordinate expansion of the actual spatial derivative. This
proves convergence of the full signed action-field sum in the original
source L² norm, without an assumed momentum normal form.
-/
noncomputable section
open Set Filter Topology NLS.Poisson
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V X U Wa : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The signed 2πn-weighted actual Hamiltonian fields sum in the original L² source norm. -/
theorem hasSum_actionHamiltonian_spatialDerivative
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (F : SourceFullAbelianDifferentialData (by simp) (by norm_num) X U)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa u)
    (a : realTypeSobolevSourceLocus) :
    HasSum (fun n : ℤ => (2*(Real.pi : ℂ)*n) •
      sourceHamiltonianVector le_rfl (sourceComplexAction (by simp) (by norm_num) n)
        (sobolevSourceInclusion a.val)) (sourceSobolevSpatialDerivative a.val) := by
  let φ : realTypeSourceSubmodule 2 := ⟨sobolevSourceInclusion a.val,a.property⟩
  let v := sourceSobolevSpatialDerivative a.val
  let T := sourceBirkhoffJacobian (by simp) (by norm_num) s φ.val
  let Q : CoeffPair 2 ≃L[ℂ] (Coeff 2 × Coeff 2) :=
    ContinuousLinearEquiv.ofBijective T
      (LinearMap.ker_eq_bot.mpr (D.jacobian_bijective_all_exponents φ).1)
      (LinearMap.range_eq_top.mpr (D.jacobian_bijective_all_exponents φ).2)
  let w := T v
  have hmode (n : ℤ) :
      (lp.single 2 n (w.1 n),lp.single 2 n (w.2 n)) =
      T ((2*(Real.pi : ℂ)*n) •
        sourceHamiltonianVector le_rfl (sourceComplexAction (by simp) (by norm_num) n) φ.val) := by
    have hv := D.jacobian_spatialDerivative_coordinates E F A a n
    change w.1 n = -(sourceBirkhoffMap (by simp) (by norm_num) s φ.val).2 n*(2*(Real.pi : ℂ)*n) ∧
      w.2 n = (sourceBirkhoffMap (by simp) (by norm_num) s φ.val).1 n*(2*(Real.pi : ℂ)*n) at hv
    have hrow (j : ℤ) := D.jacobian_coordinates φ.val (D.real_subset φ.property)
      (sourceHamiltonianVector le_rfl (sourceComplexAction (by simp) (by norm_num) n) φ.val) j
    have hd (j : ℤ) := D.fderiv_coordinates j φ.val (D.real_subset φ.property)
    have hr (j : ℤ) := D.map_coordinates_actionHamiltonian le_rfl n j φ
    rw [map_smul]
    apply Prod.ext <;> ext j
    · change (lp.single (E := fun _ : ℤ => ℂ) 2 n (w.1 n)) j = (2*(Real.pi : ℂ)*n)*
        ((T (sourceHamiltonianVector le_rfl (sourceComplexAction (by simp) (by norm_num) n) φ.val)).1 j)
      rw [(hrow j).1,← (hd j).1,(hr j).1]
      change (lp.single (E := fun _ : ℤ => ℂ) 2 n (w.1 n)) j =
        (2*(Real.pi : ℂ)*n)*(-(sourceBirkhoffMap (by simp) (by norm_num) s φ.val).2 n*
          (if j = n then 1 else 0))
      rw [hv.1]
      by_cases hj : j = n
      · subst j
        simp only [lp.single_apply,Pi.single_eq_same,ite_true,mul_one]
        ring
      · simp [lp.single_apply,hj]
    · change (lp.single (E := fun _ : ℤ => ℂ) 2 n (w.2 n)) j = (2*(Real.pi : ℂ)*n)*
        ((T (sourceHamiltonianVector le_rfl (sourceComplexAction (by simp) (by norm_num) n) φ.val)).2 j)
      rw [(hrow j).2,← (hd j).2,(hr j).2]
      change (lp.single (E := fun _ : ℤ => ℂ) 2 n (w.2 n)) j =
        (2*(Real.pi : ℂ)*n)*((sourceBirkhoffMap (by simp) (by norm_num) s φ.val).1 n*
          (if j = n then 1 else 0))
      rw [hv.2]
      by_cases hj : j = n
      · subst j
        simp only [lp.single_apply,Pi.single_eq_same,ite_true,mul_one]
        ring
      · simp [lp.single_apply,hj]
  have hw : HasSum (fun n : ℤ => (lp.single 2 n (w.1 n),lp.single 2 n (w.2 n))) w :=
    (lp.hasSum_single (by simp) w.1).prodMk (lp.hasSum_single (by simp) w.2)
  have hsum := Q.symm.toContinuousLinearMap.hasSum hw
  have hinv (n : ℤ) : Q.symm (lp.single 2 n (w.1 n),lp.single 2 n (w.2 n)) =
      (2*(Real.pi : ℂ)*n) •
        sourceHamiltonianVector le_rfl (sourceComplexAction (by simp) (by norm_num) n) φ.val := by
    rw [hmode n]
    exact Q.symm_apply_apply _
  have hwv : Q.symm w = v := Q.symm_apply_apply v
  change HasSum (fun n : ℤ => Q.symm (lp.single 2 n (w.1 n),lp.single 2 n (w.2 n))) (Q.symm w) at hsum
  simpa only [hinv,hwv] using hsum

/-- Every source cotangent may be evaluated on this norm-convergent action expansion. -/
theorem hasSum_actionHamiltonian_spatial_cotangent
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (F : SourceFullAbelianDifferentialData (by simp) (by norm_num) X U)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa u)
    (a : realTypeSobolevSourceLocus) (L : CoeffPair 2 →L[ℂ] ℂ) :
    HasSum (fun n : ℤ => (2*(Real.pi : ℂ)*n)*sourceBivector le_rfl L
      (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
        (sobolevSourceInclusion a.val))) (L (sourceSobolevSpatialDerivative a.val)) := by
  have h := L.hasSum (D.hasSum_actionHamiltonian_spatialDerivative E F A a)
  simpa only [map_smul,smul_eq_mul,sourceHamiltonianVector,apply_sourceHamiltonianDirection] using h

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
