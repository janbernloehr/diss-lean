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
open scoped ComplexConjugate
namespace NLS.ComplexAnalysis

/-- Radius of the circle through the four corners of a stadium. -/
def stadiumCornerRadius (d ρ : ℝ) : ℝ :=
  ‖(d:ℂ)+(ρ:ℂ)*I‖

/-- The circle through the corners extends past each real endpoint by a
positive distance no greater than the stadium radius. -/
theorem stadiumCornerRadius_sub_halfWidth {d ρ : ℝ}
    (hd : 0 < d) (hρ : 0 < ρ) :
    0 < stadiumCornerRadius d ρ - d ∧
      stadiumCornerRadius d ρ - d ≤ ρ := by
  have hsq : (stadiumCornerRadius d ρ) ^ 2 = d ^ 2 + ρ ^ 2 := by
    simp only [stadiumCornerRadius, Complex.norm_def, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    norm_num only [mul_zero, zero_mul, mul_one, zero_add, add_zero, sub_zero]
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hR : 0 ≤ stadiumCornerRadius d ρ := norm_nonneg _
  constructor
  · nlinarith [sq_pos_of_pos hρ]
  · nlinarith [mul_pos hd hρ]

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

/-- The upper-right corner has an angle strictly inside the first quadrant. -/
theorem stadiumUpperRightAngle_mem_firstQuadrant {d ρ : ℝ}
    (hd : 0 < d) (hρ : 0 < ρ) :
    0 < stadiumUpperRightAngle d ρ ∧
      stadiumUpperRightAngle d ρ < Real.pi / 2 := by
  have him : 0 < (((d:ℂ)+(ρ:ℂ)*I).im) := by simp [hρ]
  have hre : 0 < (((d:ℂ)+(ρ:ℂ)*I).re) := by simp [hd]
  have hnonneg : 0 ≤ stadiumUpperRightAngle d ρ :=
    arg_nonneg_iff.mpr him.le
  have hne : stadiumUpperRightAngle d ρ ≠ 0 := by
    intro heq
    have hzero := (arg_eq_zero_iff.mp heq).2
    exact (ne_of_gt him) hzero
  constructor
  · exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  · exact arg_lt_pi_div_two_iff.mpr (Or.inl hre)

/-- Reflection across the real axis negates the right-hand corner angle. -/
theorem stadiumLowerRightAngle_eq_neg {d ρ : ℝ}
    (hd : 0 < d) (hρ : 0 < ρ) :
    stadiumLowerRightAngle d ρ = -stadiumUpperRightAngle d ρ := by
  have hconj : ((d:ℂ)-(ρ:ℂ)*I) =
      conj ((d:ℂ)+(ρ:ℂ)*I) := by
    apply Complex.ext <;> simp
  rw [stadiumLowerRightAngle, hconj, arg_conj]
  have hlt := (stadiumUpperRightAngle_mem_firstQuadrant hd hρ).2
  have hne : stadiumUpperRightAngle d ρ ≠ Real.pi := by
    intro heq
    have hpi := Real.pi_pos
    linarith
  have hne' : arg ((d:ℂ)+(ρ:ℂ)*I) ≠ Real.pi := hne
  rw [if_neg hne']
  rfl

/-- The left-hand angles are the right-hand angles shifted by a half-turn. -/
theorem stadiumLeftAngles_eq {d ρ : ℝ} (hρ : 0 < ρ) :
    stadiumLowerLeftAngle d ρ = stadiumUpperRightAngle d ρ - Real.pi ∧
    stadiumLowerRightAngle d ρ = stadiumUpperLeftAngle d ρ - Real.pi := by
  have hURim : 0 < (((d:ℂ)+(ρ:ℂ)*I).im) := by simp [hρ]
  have hULim : 0 < (((-d:ℂ)+(ρ:ℂ)*I).im) := by simp [hρ]
  constructor
  · have hneg : ((-d:ℂ)-(ρ:ℂ)*I) = -((d:ℂ)+(ρ:ℂ)*I) := by ring
    simpa only [stadiumLowerLeftAngle, stadiumUpperRightAngle, hneg] using
      (arg_neg_eq_arg_sub_pi_of_im_pos hURim)
  · have hneg : ((d:ℂ)-(ρ:ℂ)*I) = -((-d:ℂ)+(ρ:ℂ)*I) := by ring
    simpa only [stadiumLowerRightAngle, stadiumUpperLeftAngle, hneg] using
      (arg_neg_eq_arg_sub_pi_of_im_pos hULim)

/-- In clockwise order the four angles are `π-α, α, -α, α-π`,
where `0 < α < π/2`. -/
theorem stadiumCornerAngles_clockwise {d ρ : ℝ}
    (hd : 0 < d) (hρ : 0 < ρ) :
    stadiumUpperLeftAngle d ρ = Real.pi - stadiumUpperRightAngle d ρ ∧
    stadiumLowerRightAngle d ρ = -stadiumUpperRightAngle d ρ ∧
    stadiumLowerLeftAngle d ρ = stadiumUpperRightAngle d ρ - Real.pi := by
  have hright := stadiumLowerRightAngle_eq_neg hd hρ
  obtain ⟨hleft, hother⟩ := stadiumLeftAngles_eq (d := d) hρ
  constructor
  · linarith
  exact ⟨hright, hleft⟩

/-- The four circular pieces have strictly decreasing endpoint angles,
and the last piece completes exactly one clockwise turn. -/
theorem stadiumCornerAngles_strictOrder {d ρ : ℝ}
    (hd : 0 < d) (hρ : 0 < ρ) :
    stadiumUpperRightAngle d ρ < stadiumUpperLeftAngle d ρ ∧
    stadiumLowerRightAngle d ρ < stadiumUpperRightAngle d ρ ∧
    stadiumLowerLeftAngle d ρ < stadiumLowerRightAngle d ρ ∧
    stadiumUpperLeftAngle d ρ - 2 * Real.pi <
      stadiumLowerLeftAngle d ρ := by
  obtain ⟨hαpos, hαlt⟩ := stadiumUpperRightAngle_mem_firstQuadrant hd hρ
  obtain ⟨hUL, hLR, hLL⟩ := stadiumCornerAngles_clockwise hd hρ
  constructor
  · rw [hUL]
    linarith
  constructor
  · rw [hLR]
    linarith
  constructor
  · rw [hLR, hLL]
    linarith
  · rw [hUL, hLL]
    linarith

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

/-- The upper circular piece remains strictly in the upper half-plane. -/
theorem stadiumCircleUpperArc_im_pos
    (c : ℂ) {d ρ : ℝ} (hc : c.im = 0)
    (hd : 0 < d) (hρ : 0 < ρ)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    0 < ((stadiumCircleUpperArc c d ρ).extend t).im := by
  have hR : 0 < stadiumCornerRadius d ρ := by
    have h := (stadiumCornerRadius_sub_halfWidth hd hρ).1
    linarith
  obtain ⟨hαpos, hαlt⟩ := stadiumUpperRightAngle_mem_firstQuadrant hd hρ
  obtain ⟨hUL, _, _⟩ := stadiumCornerAngles_clockwise hd hρ
  have hleft : stadiumUpperLeftAngle d ρ ∈ Set.Ioo (0:ℝ) Real.pi := by
    rw [hUL]
    constructor <;> linarith [Real.pi_pos]
  have hright : stadiumUpperRightAngle d ρ ∈ Set.Ioo (0:ℝ) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  change 0 < ((circleAngleArcPath c (stadiumCornerRadius d ρ)
    (stadiumUpperLeftAngle d ρ) (stadiumUpperRightAngle d ρ)).extend t).im
  exact circleAngleArcPath_im_pos c _ _ _ hc hR hleft hright t ht

/-- The lower circular piece remains strictly in the lower half-plane. -/
theorem stadiumCircleLowerArc_im_neg
    (c : ℂ) {d ρ : ℝ} (hc : c.im = 0)
    (hd : 0 < d) (hρ : 0 < ρ)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ((stadiumCircleLowerArc c d ρ).extend t).im < 0 := by
  have hR : 0 < stadiumCornerRadius d ρ := by
    have h := (stadiumCornerRadius_sub_halfWidth hd hρ).1
    linarith
  obtain ⟨hαpos, hαlt⟩ := stadiumUpperRightAngle_mem_firstQuadrant hd hρ
  obtain ⟨_, hLR, hLL⟩ := stadiumCornerAngles_clockwise hd hρ
  have hright : stadiumLowerRightAngle d ρ ∈
      Set.Ioo (-Real.pi) (0:ℝ) := by
    rw [hLR]
    constructor <;> linarith [Real.pi_pos]
  have hleft : stadiumLowerLeftAngle d ρ ∈
      Set.Ioo (-Real.pi) (0:ℝ) := by
    rw [hLL]
    constructor <;> linarith [Real.pi_pos]
  change ((circleAngleArcPath c (stadiumCornerRadius d ρ)
    (stadiumLowerRightAngle d ρ) (stadiumLowerLeftAngle d ρ)).extend t).im < 0
  exact circleAngleArcPath_im_neg c _ _ _ hc hR hright hleft t ht

/-- The right circular piece crosses the real axis only at its midpoint. -/
theorem stadiumCircleRightArc_im_sign
    (c : ℂ) {d ρ : ℝ} (hc : c.im = 0)
    (hd : 0 < d) (hρ : 0 < ρ)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (t < 1/2 → 0 < ((stadiumCircleRightArc c d ρ).extend t).im) ∧
    (t = 1/2 → ((stadiumCircleRightArc c d ρ).extend t).im = 0) ∧
    (1/2 < t → ((stadiumCircleRightArc c d ρ).extend t).im < 0) := by
  have hR : 0 < stadiumCornerRadius d ρ := by
    have h := (stadiumCornerRadius_sub_halfWidth hd hρ).1
    linarith
  obtain ⟨hαpos, hαlt⟩ := stadiumUpperRightAngle_mem_firstQuadrant hd hρ
  have hLR := stadiumLowerRightAngle_eq_neg hd hρ
  have him : ((stadiumCircleRightArc c d ρ).extend t).im =
      stadiumCornerRadius d ρ *
        Real.sin (stadiumUpperRightAngle d ρ * (1-2*t)) := by
    change ((circleAngleArcPath c (stadiumCornerRadius d ρ)
      (stadiumUpperRightAngle d ρ)
      (stadiumLowerRightAngle d ρ)).extend t).im = _
    rw [circleAngleArcPath_im c _ _ _ hc t ht, hLR]
    congr 1
    ring_nf
  rw [him]
  refine ⟨?_, ?_, ?_⟩
  · intro hhalf
    have hfacpos : 0 < 1-2*t := by linarith
    have hfac_le : 1-2*t ≤ 1 := by linarith [ht.1]
    have hθpos := mul_pos hαpos hfacpos
    have hθle := mul_le_mul_of_nonneg_left hfac_le hαpos.le
    have hθ : stadiumUpperRightAngle d ρ * (1-2*t) ∈
        Set.Ioo (0:ℝ) Real.pi := by
      constructor <;> nlinarith [Real.pi_pos]
    exact mul_pos hR (Real.sin_pos_of_mem_Ioo hθ)
  · intro hhalf
    subst t
    norm_num
  · intro hhalf
    have hfacneg : 1-2*t < 0 := by linarith
    have hfac_ge : -1 ≤ 1-2*t := by linarith [ht.2]
    have hθneg := mul_neg_of_pos_of_neg hαpos hfacneg
    have hθge := mul_le_mul_of_nonneg_left hfac_ge hαpos.le
    have hθ : -Real.pi < stadiumUpperRightAngle d ρ * (1-2*t) := by
      nlinarith [Real.pi_pos]
    exact mul_neg_of_pos_of_neg hR
      (Real.sin_neg_of_neg_of_neg_pi_lt hθneg hθ)

/-- The left arc is the half-turn of the right arc, so their imaginary
coordinates have opposite signs at matching parameters. -/
theorem stadiumCircleLeftArc_im_eq_neg_rightArc_im
    (c : ℂ) {d ρ : ℝ} (hc : c.im = 0)
    (hd : 0 < d) (hρ : 0 < ρ)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ((stadiumCircleLeftArc c d ρ).extend t).im =
      -((stadiumCircleRightArc c d ρ).extend t).im := by
  obtain ⟨hUL, hLR, hLL⟩ := stadiumCornerAngles_clockwise hd hρ
  change ((circleAngleArcPath c (stadiumCornerRadius d ρ)
    (stadiumLowerLeftAngle d ρ)
    (stadiumUpperLeftAngle d ρ-2*Real.pi)).extend t).im =
    -((circleAngleArcPath c (stadiumCornerRadius d ρ)
      (stadiumUpperRightAngle d ρ)
      (stadiumLowerRightAngle d ρ)).extend t).im
  rw [circleAngleArcPath_im c _ _ _ hc t ht,
    circleAngleArcPath_im c _ _ _ hc t ht]
  have hangle : stadiumLowerLeftAngle d ρ +
      (stadiumUpperLeftAngle d ρ - 2 * Real.pi -
        stadiumLowerLeftAngle d ρ) * t =
      (stadiumUpperRightAngle d ρ +
        (stadiumLowerRightAngle d ρ -
          stadiumUpperRightAngle d ρ) * t) - Real.pi := by
    rw [hUL, hLR, hLL]
    ring
  rw [hangle, Real.sin_sub_pi]
  ring

/-- The left circular piece crosses the real axis only at its midpoint,
with the opposite signs from the right piece. -/
theorem stadiumCircleLeftArc_im_sign
    (c : ℂ) {d ρ : ℝ} (hc : c.im = 0)
    (hd : 0 < d) (hρ : 0 < ρ)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (t < 1/2 → ((stadiumCircleLeftArc c d ρ).extend t).im < 0) ∧
    (t = 1/2 → ((stadiumCircleLeftArc c d ρ).extend t).im = 0) ∧
    (1/2 < t → 0 < ((stadiumCircleLeftArc c d ρ).extend t).im) := by
  have hmirror := stadiumCircleLeftArc_im_eq_neg_rightArc_im c hc hd hρ t ht
  obtain ⟨hpos, hzero, hneg⟩ := stadiumCircleRightArc_im_sign c hc hd hρ t ht
  rw [hmirror]
  exact ⟨fun h => neg_lt_zero.mpr (hpos h), fun h => by rw [hzero h, neg_zero],
    fun h => neg_pos.mpr (hneg h)⟩

/-- The right arc's only real-axis crossing is the outermost point of
the corner circle on the right. -/
theorem stadiumCircleRightArc_midpoint
    (c : ℂ) {d ρ : ℝ} (hd : 0 < d) (hρ : 0 < ρ) :
    (stadiumCircleRightArc c d ρ).extend (1/2:ℝ) =
      c + (stadiumCornerRadius d ρ : ℂ) := by
  have ht : (1/2:ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
  have hLR := stadiumLowerRightAngle_eq_neg hd hρ
  change (circleAngleArcPath c (stadiumCornerRadius d ρ)
    (stadiumUpperRightAngle d ρ)
    (stadiumLowerRightAngle d ρ)).extend (1/2:ℝ) = _
  rw [(circleAngleArcPath c (stadiumCornerRadius d ρ)
    (stadiumUpperRightAngle d ρ)
    (stadiumLowerRightAngle d ρ)).extend_apply ht]
  change circleMap c (stadiumCornerRadius d ρ)
    (stadiumUpperRightAngle d ρ +
      (stadiumLowerRightAngle d ρ - stadiumUpperRightAngle d ρ) * (1/2:ℝ)) = _
  have hangle : stadiumUpperRightAngle d ρ +
      (stadiumLowerRightAngle d ρ - stadiumUpperRightAngle d ρ) * (1/2:ℝ) = 0 := by
    rw [hLR]
    ring
  rw [hangle]
  simp [circleMap]

/-- The left arc's only real-axis crossing is the outermost point of
the corner circle on the left. -/
theorem stadiumCircleLeftArc_midpoint
    (c : ℂ) {d ρ : ℝ} (hd : 0 < d) (hρ : 0 < ρ) :
    (stadiumCircleLeftArc c d ρ).extend (1/2:ℝ) =
      c - (stadiumCornerRadius d ρ : ℂ) := by
  have ht : (1/2:ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
  obtain ⟨hUL, _, hLL⟩ := stadiumCornerAngles_clockwise hd hρ
  change (circleAngleArcPath c (stadiumCornerRadius d ρ)
    (stadiumLowerLeftAngle d ρ)
    (stadiumUpperLeftAngle d ρ-2*Real.pi)).extend (1/2:ℝ) = _
  rw [(circleAngleArcPath c (stadiumCornerRadius d ρ)
    (stadiumLowerLeftAngle d ρ)
    (stadiumUpperLeftAngle d ρ-2*Real.pi)).extend_apply ht]
  change circleMap c (stadiumCornerRadius d ρ)
    (stadiumLowerLeftAngle d ρ +
      (stadiumUpperLeftAngle d ρ - 2*Real.pi -
        stadiumLowerLeftAngle d ρ) * (1/2:ℝ)) = _
  have hangle : stadiumLowerLeftAngle d ρ +
      (stadiumUpperLeftAngle d ρ - 2*Real.pi -
        stadiumLowerLeftAngle d ρ) * (1/2:ℝ) = -Real.pi := by
    rw [hUL, hLL]
    ring
  rw [hangle]
  simp [circleMap, Complex.exp_neg_pi_mul_I, sub_eq_add_neg]

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
