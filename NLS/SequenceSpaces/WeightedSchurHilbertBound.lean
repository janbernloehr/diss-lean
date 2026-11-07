import NLS.SequenceSpaces.FiniteWeightedSchur
import NLS.SequenceSpaces.HilbertMatrixTranspose
import NLS.SequenceSpaces.OperatorBasisExt
import NLS.SequenceSpaces.FullDuality

/-! A symmetric Hilbert matrix with bounded weighted ell1 columns has
a uniform Hilbert operator bound, for arbitrary positive weights. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.Coeff

theorem dualPairing_operator_truncate_self
    (T : Coeff 2 →L[ℂ] Coeff 2) (s : Finset ℤ) (x : Coeff 2) :
    dualPairing (T (truncate s x)) (truncate s x)=
      ∑ j∈s, ∑ i∈s, x j*(T (lp.single 2 j 1)) i*x i := by
  classical
  have hs (j : ℤ) : (lp.single 2 j (x j) : Coeff 2)=x j • lp.single 2 j 1 := by
    ext i
    simp [lp.single_apply,Pi.single_apply]
  have hsingle (y : Coeff 2) (i : ℤ) (c : ℂ) :
      dualPairing y (lp.single 2 i c)=y i*c := by
    simp [dualPairing_apply,lp.single_apply,Pi.single_apply]
  have heval (i : ℤ) : T (truncate s x) i=∑ j∈s, x j*(T (lp.single 2 j 1)) i := by
    simp only [truncate,map_sum,lp.coeFn_sum,Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j,map_smul]
    rfl
  calc
    _=∑ i∈s, (T (truncate s x)) i*x i := by
      rw [show truncate s x=∑ i∈s, lp.single 2 i (x i) from rfl,map_sum]
      simp_rw [hsingle]
    _=∑ i∈s, ∑ j∈s, x j*(T (lp.single 2 j 1)) i*x i := by
      simp_rw [heval,Finset.sum_mul]
    _=_ := Finset.sum_comm

theorem quadratic_bound_of_symmetric_weighted_columns
    (T : Coeff 2 →L[ℂ] Coeff 2) (w : ℤ → ℝ) (hw : ∀ j, 0<w j)
    (M : ℝ) (hM : 0≤M)
    (hsym : ∀ i j, T (lp.single 2 j 1) i=T (lp.single 2 i 1) j)
    (hcol : ∀ (s : Finset ℤ) (j : ℤ), (∑ i∈s, ‖T (lp.single 2 j 1) i‖*w i)≤M*w j)
    (x : Coeff 2) : ‖dualPairing (T x) x‖≤M*‖x‖^2 := by
  classical
  have hb (s : Finset ℤ) : ‖dualPairing (T (truncate s x)) (truncate s x)‖≤M*‖x‖^2 := by
    have hq := finite_symmetric_weighted_quadratic_bound_finset s
      (fun i j => ‖T (lp.single 2 j 1) i‖) w (fun i => ‖x i‖) M
      (fun _ _ => norm_nonneg _) (fun i j => congrArg norm (hsym i j)) hw
      (fun j _ => hcol s j)
    rw [dualPairing_operator_truncate_self]
    calc
      _≤∑ j∈s, ∑ i∈s, ‖x j*(T (lp.single 2 j 1)) i*x i‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
      _=∑ i∈s, ∑ j∈s, ‖T (lp.single 2 j 1) i‖*‖x i‖*‖x j‖ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [norm_mul]
        ring
      _≤M*∑ i∈s, ‖x i‖^2 := hq
      _≤M*‖x‖^2 := mul_le_mul_of_nonneg_left (by
        simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
          lp.sum_rpow_le_norm_rpow (by norm_num : 0<(2 : ℝ≥0∞).toReal) x s) hM
  have ht : Tendsto (fun s : Finset ℤ => ‖dualPairing (T (truncate s x)) (truncate s x)‖)
      atTop (𝓝 ‖dualPairing (T x) x‖) := by
    have hc : Continuous (fun z : Coeff 2 => dualPairing (T z)) :=
      (dualPairing (p := 2) (q := 2)).continuous.comp T.continuous
    have he : Continuous (fun z : Coeff 2 => dualPairing (T z) z) := hc.clm_apply continuous_id
    exact (he.norm.tendsto x).comp (tendsto_truncate (by norm_num) x)
  exact le_of_tendsto ht (Filter.Eventually.of_forall hb)

theorem norm_le_two_mul_of_symmetric_quadratic_bound
    (T : Coeff 2 →L[ℂ] Coeff 2) (M : ℝ) (hM : 0≤M)
    (hsym : ∀ i j, T (lp.single 2 j 1) i=T (lp.single 2 i 1) j)
    (hq : ∀ x : Coeff 2, ‖dualPairing (T x) x‖≤M*‖x‖^2) : ‖T‖≤2*M := by
  have htr : hilbertMatrixTranspose T=T := by
    apply continuousLinearMap_eq_of_single (by norm_num)
    intro j
    ext i
    rw [hilbertMatrixTranspose_single,hsym]
  have hB (x y : Coeff 2) : dualPairing (T x) y=dualPairing (T y) x := by
    rw [←htr,dualPairing_hilbertMatrixTranspose,dualPairing_hilbert_comm,htr]
  have hunit (x y : Coeff 2) (hx : ‖x‖=1) (hy : ‖y‖=1) :
      ‖dualPairing (T x) y‖≤2*M := by
    have he : (4 : ℂ)*dualPairing (T x) y=
        dualPairing (T (x+y)) (x+y)-dualPairing (T (x-y)) (x-y) := by
      simp only [map_add,map_sub,add_apply,sub_apply]
      rw [hB y x]
      ring
    have hplus : ‖x+y‖≤2 := by simpa only [hx,hy,one_add_one_eq_two] using norm_add_le x y
    have hminus : ‖x-y‖≤2 := by simpa only [hx,hy,one_add_one_eq_two] using norm_sub_le x y
    have hpn : M*‖x+y‖^2≤4*M := by
      have hh : ‖x+y‖^2≤4 := by nlinarith [norm_nonneg (x+y)]
      nlinarith [mul_le_mul_of_nonneg_left hh hM]
    have hmn : M*‖x-y‖^2≤4*M := by
      have hh : ‖x-y‖^2≤4 := by nlinarith [norm_nonneg (x-y)]
      nlinarith [mul_le_mul_of_nonneg_left hh hM]
    have hh : 4*‖dualPairing (T x) y‖≤8*M := by
      calc
        _=‖(4 : ℂ)*dualPairing (T x) y‖ := by rw [norm_mul];norm_num
        _≤‖dualPairing (T (x+y)) (x+y)‖+‖dualPairing (T (x-y)) (x-y)‖ := by
          rw [he]
          exact norm_sub_le _ _
        _≤M*‖x+y‖^2+M*‖x-y‖^2 := add_le_add (hq _) (hq _)
        _≤8*M := by linarith
    linarith
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro x hx
  rw [←norm_dualPairing_eq (p := 2) (q := 2) (by norm_num) (T x)]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro y hy
  exact hunit x y hx hy

theorem norm_le_two_mul_of_symmetric_weighted_columns
    (T : Coeff 2 →L[ℂ] Coeff 2) (w : ℤ → ℝ) (hw : ∀ j, 0<w j)
    (M : ℝ) (hM : 0≤M)
    (hsym : ∀ i j, T (lp.single 2 j 1) i=T (lp.single 2 i 1) j)
    (hcol : ∀ (s : Finset ℤ) (j : ℤ), (∑ i∈s, ‖T (lp.single 2 j 1) i‖*w i)≤M*w j) :
    ‖T‖≤2*M :=
  norm_le_two_mul_of_symmetric_quadratic_bound T M hM hsym
    (quadratic_bound_of_symmetric_weighted_columns T w hw M hM hsym hcol)

end NLS.Coeff
