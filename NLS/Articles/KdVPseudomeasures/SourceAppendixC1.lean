import NLS.KdV.HillDirichletSignedForms

/-! Lemma C.1 with the entire H-minus-one potential and native
zero-trace H1 domains, for both periodic and antiperiodic extensions. -/
noncomputable section
open Set NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
namespace NLS.Articles.KdVPseudomeasures

def originalDirichletPotentialOperator (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    UnitDirichletH1 →L[ℂ] UnitDirichletHminus :=
  singularDirichletRestriction.comp ((hminusOneMultiplication q).comp unitDirichletOriginalH1)

theorem sourceLemmaC_1 (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (r : ℤ) (g h : UnitDirichletH1) :
    singularHillPairing (hminusOneMultiplication q (unitDirichletSignedH1 r g))
      (unitDirichletSignedH1 r h) = originalDirichletPotentialOperator q g h := by
  change singularHillPairing (hminusOneMultiplication q (unitDirichletSignedH1 r g))
    (unitDirichletSignedH1 r h) = singularHillPairing
      (hminusOneMultiplication q (unitDirichletOriginalH1 g)) (unitDirichletOriginalH1 h)
  simp only [singularHillPairing,hminusOneMultiplication_apply,hminusOneProduct_duality]
  rw [hillH1_product_signed_test_eq r (unitDirichletSignedH1 r g) g h
    (unitDirichletSignedH1_translate_one r g) (fun x hx => (unitDirichletSignedH1_on_unit r g x hx).symm)]

end NLS.Articles.KdVPseudomeasures
