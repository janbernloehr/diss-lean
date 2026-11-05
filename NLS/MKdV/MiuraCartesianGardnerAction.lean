import NLS.MKdV.MiuraCartesianActionFlow
import NLS.Poisson.L2CartesianGardner

/-! # Actual Cartesian-action Gardner brackets through every closed gap

The actual original H¹ Gardner trajectory and the proved Cartesian
rotation have the same L² derivative. Their chain rule identifies the
literal Frechet derivative applied to the actual Gardner action field.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraH1SobolevEquiv_L2 (a : ScalarDomain 2) :
    hierarchySobolevJetL2 1 0 (by omega) (miuraH1SobolevEquiv a) = scalarInclusion a := by
  ext j
  simp only [hierarchySobolevJetL2_apply,pow_zero,one_mul,miuraH1SobolevEquiv_apply,scalarInclusion_apply]

theorem miuraH1ActionFlow_L2_native (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    hierarchySobolevJetL2 1 0 (by omega)
      (miuraActionFlow 1 (miuraH1SobolevEquiv a) (miuraH1SobolevReal a ha) n t) =
      scalarInclusion (miuraH1ActionFlow a ha n t) := by
  ext j
  simp only [hierarchySobolevJetL2_apply,pow_zero,one_mul,scalarInclusion_apply,
    miuraH1ActionFlow,miuraH1SobolevEquiv_symm_apply]

theorem miuraL2CartesianCoordinates_miuraH1ActionFlow (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (t : ℝ) :
    miuraL2CartesianCoordinates m (scalarInclusion (miuraH1ActionFlow a ha n t)) =
      if m = n then cartesianPlaneRotation t (miuraL2CartesianCoordinates m (scalarInclusion a))
      else miuraL2CartesianCoordinates m (scalarInclusion a) := by
  have he := miuraL2CartesianCoordinates_miuraActionFlow 1 (miuraH1SobolevEquiv a)
    (miuraH1SobolevReal a ha) m n hm hn t
  rwa [miuraH1SobolevEquiv_L2,miuraH1ActionFlow_L2_native] at he

theorem hasDerivAt_miuraH1ActionFlow_Cartesian (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (t : ℝ) :
    HasDerivAt (fun r => miuraL2CartesianCoordinates m (scalarInclusion (miuraH1ActionFlow a ha n r)))
      (if m = n then
        ((miuraL2CartesianCoordinates m (scalarInclusion (miuraH1ActionFlow a ha n t))).2,
         -(miuraL2CartesianCoordinates m (scalarInclusion (miuraH1ActionFlow a ha n t))).1)
       else 0) t := by
  have he : (fun r => miuraL2CartesianCoordinates m (scalarInclusion (miuraH1ActionFlow a ha n r))) =
      (fun r => if m = n then cartesianPlaneRotation r (miuraL2CartesianCoordinates m (scalarInclusion a))
        else miuraL2CartesianCoordinates m (scalarInclusion a)) :=
    funext (miuraL2CartesianCoordinates_miuraH1ActionFlow a ha m n hm hn)
  rw [he,miuraL2CartesianCoordinates_miuraH1ActionFlow a ha m n hm hn t]
  by_cases hmn : m = n
  · simp only [if_pos hmn]
    exact hasDerivAt_cartesianPlaneRotation _ t
  · simp only [if_neg hmn]
    exact hasDerivAt_const t _

/-- The vector form of {X_m,J_n}=delta_mn Y_m and
{Y_m,J_n}=-delta_mn X_m, using the actual original scalar derivatives. -/
theorem fderiv_miuraCartesian_apply_Gardner_action (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (fderiv ℂ (miuraL2CartesianCoordinates m) (scalarInclusion a))
      (l2GardnerDirection (miuraL2Action n) (scalarInclusion a)) =
      if m = n then ((miuraL2CartesianCoordinates m (scalarInclusion a)).2,
        -(miuraL2CartesianCoordinates m (scalarInclusion a)).1) else 0 := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  have hg := hasDerivAt_miuraH1ActionFlow_Gardner a ha n hn 0
  rw [miuraH1ActionFlow_zero] at hg
  have hf : HasFDerivAt (miuraL2CartesianCoordinates m)
      ((fderiv ℂ (miuraL2CartesianCoordinates m) (scalarInclusion a)).restrictScalars ℝ)
      (scalarInclusion (miuraH1ActionFlow a ha n 0)) := by
    rw [miuraH1ActionFlow_zero]
    exact (analyticAt_miuraL2CartesianCoordinates (scalarInclusion a) har m hm).differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hd := hf.comp_hasDerivAt 0 hg
  have he := hasDerivAt_miuraH1ActionFlow_Cartesian a ha m n hm hn 0
  rw [miuraH1ActionFlow_zero] at he
  exact hd.unique he

/-- Literal scalar Gardner brackets of the two actual Cartesian
coordinate functions, with all gap-collapse cases included. -/
theorem miuraCartesianActionGardner_brackets (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (l2GardnerBracket (fun b => (miuraL2CartesianCoordinates m b).1) (miuraL2Action n) (scalarInclusion a),
     l2GardnerBracket (fun b => (miuraL2CartesianCoordinates m b).2) (miuraL2Action n) (scalarInclusion a)) =
      if m = n then ((miuraL2CartesianCoordinates m (scalarInclusion a)).2,
        -(miuraL2CartesianCoordinates m (scalarInclusion a)).1) else 0 := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  rw [l2GardnerBracket_pair _ _ _ (analyticAt_miuraL2CartesianCoordinates (scalarInclusion a) har m hm).differentiableAt]
  exact fderiv_miuraCartesian_apply_Gardner_action a ha m n hm hn

end NLS.MKdV
