import NLS.ComplexAnalysis.CircleArcCurveIntegral

/-!
# A circle through the corners of a stadium

For a horizontal half-width `d` and vertical offset `ρ`, the four
vectors `±d ± ρi` have one norm. Their complex arguments therefore
parameterize four points on one circle, giving exact endpoints for
circle arcs paired with the stadium sides.
-/

noncomputable section
open Complex
namespace NLS.ComplexAnalysis

/-- Radius of the circle through the four corners of a stadium. -/
def stadiumCornerRadius (d ρ : ℝ) : ℝ :=
  ‖(d:ℂ)+(ρ:ℂ)*I‖

/-- The four corner directions have the same norm. -/
theorem stadiumCorner_norms (d ρ : ℝ) :
    ‖(d:ℂ)+(ρ:ℂ)*I‖ = stadiumCornerRadius d ρ ∧
    ‖(-d:ℂ)+(ρ:ℂ)*I‖ = stadiumCornerRadius d ρ ∧
    ‖(d:ℂ)-(ρ:ℂ)*I‖ = stadiumCornerRadius d ρ ∧
    ‖(-d:ℂ)-(ρ:ℂ)*I‖ = stadiumCornerRadius d ρ := by
  constructor
  · rfl
  constructor
  · simp [stadiumCornerRadius, Complex.norm_def, Complex.normSq_apply]
  constructor
  · simp [stadiumCornerRadius, Complex.norm_def, Complex.normSq_apply]
  · simp [stadiumCornerRadius, Complex.norm_def, Complex.normSq_apply]

/-- Circle points at the arguments of the four corner vectors equal
the four stadium corners exactly. -/
theorem stadiumCorner_circleMap (c : ℂ) (d ρ : ℝ) :
    circleMap c (stadiumCornerRadius d ρ)
      (arg ((-d:ℂ)+(ρ:ℂ)*I)) = c+(-d:ℂ)+(ρ:ℂ)*I ∧
    circleMap c (stadiumCornerRadius d ρ)
      (arg ((d:ℂ)+(ρ:ℂ)*I)) = c+(d:ℂ)+(ρ:ℂ)*I ∧
    circleMap c (stadiumCornerRadius d ρ)
      (arg ((d:ℂ)-(ρ:ℂ)*I)) = c+(d:ℂ)-(ρ:ℂ)*I ∧
    circleMap c (stadiumCornerRadius d ρ)
      (arg ((-d:ℂ)-(ρ:ℂ)*I)) = c+(-d:ℂ)-(ρ:ℂ)*I := by
  obtain ⟨_,hUL,hLR,hLL⟩ := stadiumCorner_norms d ρ
  constructor
  · rw [← hUL, circleMap_norm_arg]
    ring
  constructor
  · rw [← stadiumCorner_norms d ρ |>.1, circleMap_norm_arg]
    ring
  constructor
  · rw [← hLR, circleMap_norm_arg]
    ring
  · rw [← hLL, circleMap_norm_arg]
    ring

/-- Angular parameters of the four stadium corners, beginning in the
upper left and proceeding clockwise. -/
def stadiumUpperLeftAngle (d ρ : ℝ) : ℝ :=
  arg ((-d:ℂ)+(ρ:ℂ)*I)

def stadiumUpperRightAngle (d ρ : ℝ) : ℝ :=
  arg ((d:ℂ)+(ρ:ℂ)*I)

def stadiumLowerRightAngle (d ρ : ℝ) : ℝ :=
  arg ((d:ℂ)-(ρ:ℂ)*I)

def stadiumLowerLeftAngle (d ρ : ℝ) : ℝ :=
  arg ((-d:ℂ)-(ρ:ℂ)*I)

/-- The first clockwise circle arc joins the two upper stadium
corners. -/
def stadiumCircleUpperArc (c : ℂ) (d ρ : ℝ) :
    Path (c-(d:ℂ)+(ρ:ℂ)*I) (c+(d:ℂ)+(ρ:ℂ)*I) :=
  (circleAngleArcPath c (stadiumCornerRadius d ρ)
    (stadiumUpperLeftAngle d ρ) (stadiumUpperRightAngle d ρ)).cast
      (by
        simpa [stadiumUpperLeftAngle, sub_eq_add_neg] using
          (stadiumCorner_circleMap c d ρ).1.symm)
      (by
        simpa [stadiumUpperRightAngle] using
          (stadiumCorner_circleMap c d ρ).2.1.symm)

/-- The second clockwise circle arc joins the two right stadium
corners. -/
def stadiumCircleRightArc (c : ℂ) (d ρ : ℝ) :
    Path (c+(d:ℂ)+(ρ:ℂ)*I) (c+(d:ℂ)-(ρ:ℂ)*I) :=
  (circleAngleArcPath c (stadiumCornerRadius d ρ)
    (stadiumUpperRightAngle d ρ) (stadiumLowerRightAngle d ρ)).cast
      (by
        simpa [stadiumUpperRightAngle] using
          (stadiumCorner_circleMap c d ρ).2.1.symm)
      (by
        simpa [stadiumLowerRightAngle] using
          (stadiumCorner_circleMap c d ρ).2.2.1.symm)

/-- The third clockwise circle arc joins the two lower stadium
corners. -/
def stadiumCircleLowerArc (c : ℂ) (d ρ : ℝ) :
    Path (c+(d:ℂ)-(ρ:ℂ)*I) (c-(d:ℂ)-(ρ:ℂ)*I) :=
  (circleAngleArcPath c (stadiumCornerRadius d ρ)
    (stadiumLowerRightAngle d ρ) (stadiumLowerLeftAngle d ρ)).cast
      (by
        simpa [stadiumLowerRightAngle] using
          (stadiumCorner_circleMap c d ρ).2.2.1.symm)
      (by
        simpa [stadiumLowerLeftAngle, sub_eq_add_neg] using
          (stadiumCorner_circleMap c d ρ).2.2.2.symm)

/-- The final clockwise circle arc returns to the upper-left corner
after exactly one full turn. -/
def stadiumCircleLeftArc (c : ℂ) (d ρ : ℝ) :
    Path (c-(d:ℂ)-(ρ:ℂ)*I) (c-(d:ℂ)+(ρ:ℂ)*I) :=
  (circleAngleArcPath c (stadiumCornerRadius d ρ)
    (stadiumLowerLeftAngle d ρ)
    (stadiumUpperLeftAngle d ρ-2*Real.pi)).cast
      (by
        simpa [stadiumLowerLeftAngle, sub_eq_add_neg] using
          (stadiumCorner_circleMap c d ρ).2.2.2.symm)
      (by
        have hperiod := (periodic_circleMap c (stadiumCornerRadius d ρ))
          (stadiumUpperLeftAngle d ρ-2*Real.pi)
        have hangle :
            (stadiumUpperLeftAngle d ρ-2*Real.pi)+2*Real.pi =
              stadiumUpperLeftAngle d ρ := by ring
        rw [hangle] at hperiod
        rw [← hperiod]
        simpa [stadiumUpperLeftAngle, sub_eq_add_neg] using
          (stadiumCorner_circleMap c d ρ).1.symm)

/-- The four arcs through the stadium corners have the signed circle
integral when concatenated in clockwise order. -/
theorem stadiumCircleArc_integrals_eq_neg_circleIntegral
    (f : ℂ → ℂ) (c : ℂ) (d ρ : ℝ)
    (hf : ∀ θ : ℝ,
      ContinuousAt f (circleMap c (stadiumCornerRadius d ρ) θ)) :
    ((((∫ᶜ z in stadiumCircleUpperArc c d ρ, holomorphicOneForm f z) +
       (∫ᶜ z in stadiumCircleRightArc c d ρ, holomorphicOneForm f z)) +
       (∫ᶜ z in stadiumCircleLowerArc c d ρ, holomorphicOneForm f z)) +
       (∫ᶜ z in stadiumCircleLeftArc c d ρ, holomorphicOneForm f z)) =
      -(∮ z in C(c, stadiumCornerRadius d ρ), f z) := by
  simpa only [stadiumCircleUpperArc, stadiumCircleRightArc,
    stadiumCircleLowerArc, stadiumCircleLeftArc, curveIntegral_cast] using
    four_circleAngleArc_curveIntegral_eq_neg_circleIntegral f c
      (stadiumCornerRadius d ρ)
      (stadiumUpperLeftAngle d ρ) (stadiumUpperRightAngle d ρ)
      (stadiumLowerRightAngle d ρ) (stadiumLowerLeftAngle d ρ) hf

/-- Each of the four named circle arcs is twice smooth on the unit
interval, as needed for a piecewise contour homotopy. -/
theorem stadiumCircleArcs_contDiffOn (c : ℂ) (d ρ : ℝ) :
    ContDiffOn ℝ 2 (stadiumCircleUpperArc c d ρ).extend
      (Set.Icc (0:ℝ) 1) ∧
    ContDiffOn ℝ 2 (stadiumCircleRightArc c d ρ).extend
      (Set.Icc (0:ℝ) 1) ∧
    ContDiffOn ℝ 2 (stadiumCircleLowerArc c d ρ).extend
      (Set.Icc (0:ℝ) 1) ∧
    ContDiffOn ℝ 2 (stadiumCircleLeftArc c d ρ).extend
      (Set.Icc (0:ℝ) 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ContDiffOn ℝ 2
      (circleAngleArcPath c (stadiumCornerRadius d ρ)
        (stadiumUpperLeftAngle d ρ) (stadiumUpperRightAngle d ρ)).extend
      (Set.Icc (0:ℝ) 1)
    exact circleAngleArcPath_contDiffOn _ _ _ _
  · change ContDiffOn ℝ 2
      (circleAngleArcPath c (stadiumCornerRadius d ρ)
        (stadiumUpperRightAngle d ρ) (stadiumLowerRightAngle d ρ)).extend
      (Set.Icc (0:ℝ) 1)
    exact circleAngleArcPath_contDiffOn _ _ _ _
  · change ContDiffOn ℝ 2
      (circleAngleArcPath c (stadiumCornerRadius d ρ)
        (stadiumLowerRightAngle d ρ) (stadiumLowerLeftAngle d ρ)).extend
      (Set.Icc (0:ℝ) 1)
    exact circleAngleArcPath_contDiffOn _ _ _ _
  · change ContDiffOn ℝ 2
      (circleAngleArcPath c (stadiumCornerRadius d ρ)
        (stadiumLowerLeftAngle d ρ)
        (stadiumUpperLeftAngle d ρ-2*Real.pi)).extend
      (Set.Icc (0:ℝ) 1)
    exact circleAngleArcPath_contDiffOn _ _ _ _

end NLS.ComplexAnalysis
