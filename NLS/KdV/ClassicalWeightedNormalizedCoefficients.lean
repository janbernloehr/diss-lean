import NLS.KdV.ClassicalWeightedPeriodInverse
import NLS.KdV.ClassicalNormalizedDifferentials

/-! # One-weight l2 control of actual normalized numerator coefficients

The compatible weighted inverse realizes the literal weighted error in
every positive inverse column. It is Banach analytic and uniformly small
near zero after division by the selected column index.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.KdV

def classicalHillWeightedInverseError
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) : NLS.Coeff 2 :=
  (n : ℂ) • (Q q (lp.single 2 (n : ℤ) 1)-lp.single 2 (n : ℤ) 1)

theorem classicalHillWeightedInverseError_apply
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : NLS.LinearVolterra.Curve ℂ)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m*(R q (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j*(Q q (lp.single 2 j 1)) m)
    (n : ℕ+) (m : ℤ) :
    classicalHillWeightedInverseError Q n q m =
      NLS.Coeff.positiveIndexWeight m*
        ((R q (lp.single 2 (n : ℤ) 1)) m-(lp.single 2 (n : ℤ) (1 : ℂ) : NLS.Coeff 2) m) := by
  have hn : (0 : ℤ) < n := by exact_mod_cast n.pos
  have he := hcompat m (n : ℤ)
  have hwn : NLS.Coeff.positiveIndexWeight (n : ℤ) = (n : ℂ) := by
    simp only [NLS.Coeff.positiveIndexWeight,if_pos hn,Int.cast_natCast]
  rw [hwn] at he
  change (n : ℂ)*((Q q (lp.single 2 (n : ℤ) 1)) m-
    (lp.single 2 (n : ℤ) (1 : ℂ) : NLS.Coeff 2) m) = _
  rw [mul_sub,mul_sub,← he]
  by_cases hmn : m = (n : ℤ)
  · subst m
    simp only [NLS.Coeff.positiveIndexWeight,if_pos hn,Int.cast_natCast]
  · simp only [lp.single_apply,Pi.single_apply,if_neg hmn,mul_zero,sub_zero]

theorem classicalHillWeightedInverseError_memlp
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : NLS.LinearVolterra.Curve ℂ)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m*(R q (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j*(Q q (lp.single 2 j 1)) m) (n : ℕ+) :
    Memℓp (fun m : ℤ => NLS.Coeff.positiveIndexWeight m*
      ((R q (lp.single 2 (n : ℤ) 1)) m-(lp.single 2 (n : ℤ) (1 : ℂ) : NLS.Coeff 2) m)) 2 := by
  have he : (fun m : ℤ => NLS.Coeff.positiveIndexWeight m*
      ((R q (lp.single 2 (n : ℤ) 1)) m-(lp.single 2 (n : ℤ) (1 : ℂ) : NLS.Coeff 2) m)) =
      (fun m => classicalHillWeightedInverseError Q n q m) :=
    funext (fun m => (classicalHillWeightedInverseError_apply R Q q hcompat n m).symm)
  rw [he]
  exact lp.memℓp (classicalHillWeightedInverseError Q n q)

theorem classicalHillWeightedInverseError_analytic
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (V : Set (NLS.LinearVolterra.Curve ℂ)) (hQa : AnalyticOnNhd ℂ Q V) (n : ℕ+) :
    AnalyticOnNhd ℂ (classicalHillWeightedInverseError Q n) V := by
  intro q hq
  have hc : AnalyticAt ℂ (fun x : NLS.LinearVolterra.Curve ℂ => Q x (lp.single 2 (n : ℤ) 1)) q := by
    simpa only [Function.comp_def] using!
      ((ContinuousLinearMap.apply ℂ (NLS.Coeff 2) (lp.single 2 (n : ℤ) 1)).analyticAt (Q q)).comp
        (f := Q) (hQa q hq)
  exact (analyticAt_const (v := (n : ℂ))).smul
    (hc.sub (analyticAt_const (v := (lp.single 2 (n : ℤ) 1 : NLS.Coeff 2))))

theorem classicalHillWeightedInverseError_free
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQ0 : Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) (n : ℕ+) :
    classicalHillWeightedInverseError Q n 0 = 0 := by
  simp only [classicalHillWeightedInverseError,hQ0,ContinuousLinearMap.id_apply,sub_self,smul_zero]

theorem norm_classicalHillWeightedInverseError_le
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) :
    ‖classicalHillWeightedInverseError Q n q‖ ≤
      (n : ℝ)*‖Q q-ContinuousLinearMap.id ℂ (NLS.Coeff 2)‖ := by
  have he : classicalHillWeightedInverseError Q n q =
      (n : ℂ) • ((Q q-ContinuousLinearMap.id ℂ (NLS.Coeff 2)) (lp.single 2 (n : ℤ) 1)) := rfl
  rw [he,norm_smul,Complex.norm_natCast]
  have hen : ‖(lp.single 2 (n : ℤ) (1 : ℂ) : NLS.Coeff 2)‖ = 1 := by
    rw [lp.norm_single (by norm_num),norm_one]
  simpa only [hen,mul_one] using
    mul_le_mul_of_nonneg_left ((Q q-ContinuousLinearMap.id ℂ (NLS.Coeff 2)).le_opNorm
      (lp.single 2 (n : ℤ) 1)) (by positivity : (0 : ℝ) ≤ n)

/-- A single neighborhood controls every weighted column error, with its
exact n scaling. No mode-dependent neighborhood is selected. -/
theorem exists_uniform_small_classicalHillWeightedInverseError
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (V : Set (NLS.LinearVolterra.Curve ℂ)) (hV : IsOpen V) (h0V : 0 ∈ V)
    (hQa : AnalyticOnNhd ℂ Q V) (hQ0 : Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set (NLS.LinearVolterra.Curve ℂ), U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧
      ∀ q ∈ U, ∀ n : ℕ+, ‖classicalHillWeightedInverseError Q n q‖ ≤ ε*(n : ℝ) := by
  have hc := ((hQa 0 h0V).sub (analyticAt_const (v := ContinuousLinearMap.id ℂ (NLS.Coeff 2)))).continuousAt.norm
  have hs : ∀ᶠ q in 𝓝 (0 : NLS.LinearVolterra.Curve ℂ),
      ‖Q q-ContinuousLinearMap.id ℂ (NLS.Coeff 2)‖ < ε :=
    hc.eventually (gt_mem_nhds (by
      change ‖Q 0-ContinuousLinearMap.id ℂ (NLS.Coeff 2)‖ < ε
      simpa only [hQ0,sub_self,norm_zero] using hε))
  obtain ⟨B,hBsub,hB,h0B⟩ := _root_.mem_nhds_iff.mp hs
  refine ⟨V ∩ B,inter_subset_left,hV.inter hB,⟨h0V,h0B⟩,?_⟩
  intro q hq n
  exact (norm_classicalHillWeightedInverseError_le Q n q).trans
    (by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (hBsub hq.2).le (by positivity : (0 : ℝ) ≤ n))

/-- The same actual normalized entire family has jointly compatible
one-weight l2 coefficient errors on a single constructed neighborhood. -/
theorem exists_classicalHill_weighted_normalized_differentials :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ),
      ∃ R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen V ∧ 0 ∈ V ∧ AnalyticOnNhd ℂ R V ∧ AnalyticOnNhd ℂ Q V ∧
        R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        (∀ n : ℕ+, AnalyticOnNhd ℂ (classicalHillWeightedInverseError Q n) V) ∧
        (∀ q ∈ V, ∀ n : ℕ+, ∀ m : ℤ,
          classicalHillWeightedInverseError Q n q m =
            NLS.Coeff.positiveIndexWeight m*
              ((R q (lp.single 2 (n : ℤ) 1)) m-
                (lp.single 2 (n : ℤ) (1 : ℂ) : NLS.Coeff 2) m)) ∧
        (∀ n : ℕ+, AnalyticOnNhd ℂ (classicalHillNormalizedNumerator N R n) (univ ×ˢ V)) ∧
        (∀ n k : ℕ+, ∀ q ∈ V,
          (2*(Real.pi : ℂ))⁻¹ * ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
            classicalHillNormalizedNumerator N R n (z^2,q)/classicalHillContinuedRoot (z^2,q)*(2*z) =
              if n = k then 1 else 0) ∧
        ∃ A : ℝ, ClassicalAllContourPeriodData N V A := by
  obtain ⟨N,V,T,R,S,Q,hN,hV,h0V,_,hRa,_,hQa,_,hR0,_,hQ0,hinv,hentry,hcompat,A,D⟩ :=
    exists_classicalHill_weighted_period_inverse
  refine ⟨N,V,R,Q,hN,hV,h0V,hRa,hQa,hR0,hQ0,
    fun n => classicalHillWeightedInverseError_analytic Q V hQa n,?_,
    D.normalizedNumerator_analytic R hRa,?_,A,D⟩
  · intro q hq n m
    exact classicalHillWeightedInverseError_apply R Q q (hcompat q hq) n m
  intro n k q hq
  exact D.normalizedNumerator_period n k q hq T R (fun m j => (hentry q hq m j).1) (hinv q hq).1

end NLS.KdV
