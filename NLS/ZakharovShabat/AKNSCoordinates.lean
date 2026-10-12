import NLS.ZakharovShabat.PhysicalOperator

/-! # The normalized AKNS change of coordinates

The vector change of basis is unitary for the component-sum Hilbert norm.
The potential map is `(q + i p, q - i p)`, without the vector normalization.
These are different maps, as already specified on printed page 19.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- The scalar in the unitary vector change of basis. -/
def aknsScale : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem aknsScale_sq : aknsScale ^ 2 = 1 / 2 := by
  unfold aknsScale
  rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem aknsScale_ne_zero : aknsScale ≠ 0 := by
  intro h
  have := aknsScale_sq
  rw [h] at this
  norm_num at this

/-- Normalized vector coordinates: the matrix T in the dissertation. -/
def aknsToZS (u : ℂ × ℂ) : ℂ × ℂ :=
  (aknsScale * (u.1 + Complex.I * u.2), aknsScale * (u.1 - Complex.I * u.2))

/-- The inverse (adjoint) vector change of basis. -/
def zsToAKNS (u : ℂ × ℂ) : ℂ × ℂ :=
  (aknsScale * (u.1 + u.2), aknsScale * (-Complex.I * u.1 + Complex.I * u.2))

@[simp] theorem zsToAKNS_aknsToZS (u : ℂ × ℂ) : zsToAKNS (aknsToZS u) = u := by
  ext <;> dsimp [zsToAKNS, aknsToZS] <;>
    ring_nf <;> simp [Complex.I_sq, aknsScale_sq] <;> ring

@[simp] theorem aknsToZS_zsToAKNS (u : ℂ × ℂ) : aknsToZS (zsToAKNS u) = u := by
  ext <;> dsimp [zsToAKNS, aknsToZS] <;>
    ring_nf <;> simp [Complex.I_sq, aknsScale_sq] <;> ring

/-- The linear coordinate equivalence; Hilbert norm preservation is stated separately. -/
def aknsCoordinateEquiv : (ℂ × ℂ) ≃ₗ[ℂ] (ℂ × ℂ) where
  toFun := aknsToZS
  invFun := zsToAKNS
  left_inv := zsToAKNS_aknsToZS
  right_inv := aknsToZS_zsToAKNS
  map_add' u v := by ext <;> simp [aknsToZS] <;> ring
  map_smul' c u := by ext <;> simp [aknsToZS] <;> ring

/-- The original physical component-sum norm is preserved, for complex coordinates. -/
theorem aknsToZS_norm_sq (u : ℂ × ℂ) :
    ‖(aknsToZS u).1‖ ^ 2 + ‖(aknsToZS u).2‖ ^ 2 = ‖u.1‖ ^ 2 + ‖u.2‖ ^ 2 := by
  simp only [Complex.sq_norm, aknsToZS, Complex.normSq_mul]
  have hs : Complex.normSq aknsScale = 1 / 2 := by
    simp only [aknsScale, Complex.normSq_ofReal, ← sq]
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hs]
  simp [Complex.normSq, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]
  ring

/-- Potential coordinates have no factor 1/sqrt(2). -/
def aknsPotential (q p : ℂ) : ℂ × ℂ := (q + Complex.I * p, q - Complex.I * p)

/-- The AKNS differential expression, specified by a value and its derivative. -/
def aknsAction (q p : ℂ) (u v : ℂ × ℂ) : ℂ × ℂ :=
  (-v.2 + q * u.1 + p * u.2, v.1 + p * u.1 - q * u.2)

/-- The Zakharov--Shabat differential expression on a value and its derivative. -/
def zsAction (φ u v : ℂ × ℂ) : ℂ × ℂ :=
  (Complex.I * v.1 + φ.1 * u.2, -Complex.I * v.2 + φ.2 * u.1)

/-- Exact conjugation of both derivative and potential terms. -/
theorem aknsAction_intertwining (q p : ℂ) (u v : ℂ × ℂ) :
    zsAction (aknsPotential q p) (aknsToZS u) (aknsToZS v) =
      aknsToZS (aknsAction q p u v) := by
  ext <;> dsimp [zsAction, aknsPotential, aknsToZS, aknsAction] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

/-- Dirichlet boundary values correspond to a vanishing second AKNS component. -/
theorem aknsToZS_dirichlet_iff (u : ℂ × ℂ) :
    (aknsToZS u).1 = (aknsToZS u).2 ↔ u.2 = 0 := by
  simp only [aknsToZS, mul_right_inj' aknsScale_ne_zero]
  constructor
  · intro h
    have : Complex.I * u.2 = 0 := by linear_combination h / 2
    exact (mul_eq_zero.mp this).resolve_left Complex.I_ne_zero
  · intro h; simp [h]

/-- Neumann boundary values correspond to a vanishing first AKNS component. -/
theorem aknsToZS_neumann_iff (u : ℂ × ℂ) :
    (aknsToZS u).1 = -(aknsToZS u).2 ↔ u.1 = 0 := by
  constructor
  · intro h
    have : aknsScale * u.1 = 0 := by
      dsimp [aknsToZS] at h
      linear_combination h / 2
    exact (mul_eq_zero.mp this).resolve_left aknsScale_ne_zero
  · intro h; simp [aknsToZS, h]

/-- The potential map differs from the vector map by the missing normalization. -/
theorem aknsPotential_eq_sqrt_two_smul (q p : ℂ) :
    aknsPotential q p = (Real.sqrt 2 : ℂ) • aknsToZS (q,p) := by
  have hs : (Real.sqrt 2 : ℂ) * aknsScale = 1 := by
    simp [aknsScale, Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
  ext <;> simp [aknsPotential, aknsToZS, smul_eq_mul, ← mul_assoc, hs]

/-- The normalized vector map cannot also be the potential map, already at (q,p)=(1,0). -/
theorem aknsPotential_ne_vectorMap : aknsPotential 1 0 ≠ aknsToZS (1,0) := by
  intro h
  have hs : aknsScale = 1 := by
    simpa [aknsPotential, aknsToZS] using (congrArg Prod.fst h).symm
  have hsq := aknsScale_sq
  rw [hs] at hsq
  norm_num at hsq

/-- Equation (1.7), including both component signs. -/
theorem aknsAction_eigen_iff (q p z : ℂ) (u v : ℂ × ℂ) :
    aknsAction q p u v = z • u ↔
      -v.2 = z * u.1 - q * u.1 - p * u.2 ∧
      v.1 = z * u.2 - p * u.1 + q * u.2 := by
  simp only [aknsAction, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor
  · linear_combination h₁
  · linear_combination h₂
  · linear_combination h₁
  · linear_combination h₂

/-- Using T also on potentials makes the printed conjugation false for constant data. -/
theorem aknsAction_printed_normalization_false :
    zsAction (aknsToZS (1,0)) (aknsToZS (1,0)) (aknsToZS (0,0)) ≠
      aknsToZS (aknsAction 1 0 (1,0) (0,0)) := by
  intro h
  have hs : aknsScale * aknsScale = aknsScale := by
    simpa [zsAction, aknsToZS, aknsAction] using congrArg Prod.fst h
  have hs1 : aknsScale = 1 := mul_left_cancel₀ aknsScale_ne_zero (hs.trans (mul_one _).symm)
  have hsq := aknsScale_sq
  rw [hs1] at hsq
  norm_num at hsq

end NLS.ZakharovShabat
