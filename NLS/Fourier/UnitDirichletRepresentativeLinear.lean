import NLS.Fourier.UnitIntervalDirichlet

/-! # Linearity of the full native interval representative -/
noncomputable section
namespace NLS.Fourier

theorem unitDirichletRepresentative_add (f g : UnitDirichletH1) (x : ℝ) :
    unitDirichletRepresentative (f+g) x =
      unitDirichletRepresentative f x+unitDirichletRepresentative g x := by
  change periodOneSobolevSynthesis (f.val+g.val) (x : AddCircle (2:ℝ)) = _
  rw [map_add]
  rfl

theorem unitDirichletRepresentative_smul (c : ℂ) (f : UnitDirichletH1) (x : ℝ) :
    unitDirichletRepresentative (c • f) x = c*unitDirichletRepresentative f x := by
  change periodOneSobolevSynthesis (c • f.val) (x : AddCircle (2:ℝ)) = _
  rw [map_smul]
  rfl

theorem unitDirichletRepresentative_zero_vector (x : ℝ) :
    unitDirichletRepresentative 0 x = 0 := by
  change periodOneSobolevSynthesis 0 (x : AddCircle (2:ℝ)) = 0
  rw [map_zero]
  rfl

end NLS.Fourier
