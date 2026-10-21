import NLS.ZakharovShabat.SourceBirkhoffHmFourierAnalytic
import NLS.ZakharovShabat.SourceBirkhoffFourierSobolevBall

/-! # The canonical stronger Birkhoff Fourier remainder

Coefficient uniqueness packages the analytic and uniformly bounded one-derivative Fourier remainder for the same Birkhoff family at every positive integer order.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The canonical rectangular Fourier remainder in the space gaining one
derivative. The theorems below identify every coordinate near the real locus. -/
def higherSobolevBirkhoffFourierRemainder (m : ℕ)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (b : SobolevSource m) :
    WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 ×
      WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 :=
  (WeightedCoeff.ofFunctionOrZero _ 2 (fun n =>
    (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m b)).1 n -
      (sourceBirkhoffFourier (higherSobolevSourceInclusion m b)).1 n),
   WeightedCoeff.ofFunctionOrZero _ 2 (fun n =>
    (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m b)).2 n -
      (sourceBirkhoffFourier (higherSobolevSourceInclusion m b)).2 n))

/-- Coefficient uniqueness identifies the canonical stronger-target map
with any realization of the actual rectangular Fourier error. -/
theorem higherSobolevBirkhoffFourierRemainder_eq_of_coordinates
    (m : ℕ) (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (b : SobolevSource m)
    (E : WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 ×
      WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2)
    (hE : ∀ n,
      E.1.val n = (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m b)).1 n -
        (sourceBirkhoffFourier (higherSobolevSourceInclusion m b)).1 n ∧
      E.2.val n = (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m b)).2 n -
        (sourceBirkhoffFourier (higherSobolevSourceInclusion m b)).2 n) :
    higherSobolevBirkhoffFourierRemainder m s b = E := by
  apply Prod.ext
  · exact WeightedCoeff.ofFunctionOrZero_eq_of_coordinates _ _ E.1 (fun n => (hE n).1)
  · exact WeightedCoeff.ofFunctionOrZero_eq_of_coordinates _ _ E.2 (fun n => (hE n).2)

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- The canonical remainder is analytic into h^(m+1) on a complex
neighborhood of every real original Hm source, with its literal coordinates. -/
theorem exists_local_higherSobolevBirkhoffFourierRemainder_analytic
    (m : ℕ) (hm : 1 ≤ m) (a : realTypeHigherSobolevSourceLocus m) :
    ∃ V : Set (SobolevSource m), IsOpen V ∧ a.val ∈ V ∧
      AnalyticOnNhd ℂ (higherSobolevBirkhoffFourierRemainder m s) V ∧
      ∀ b ∈ V, ∀ n,
        (higherSobolevBirkhoffFourierRemainder m s b).1.val n =
          (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m b)).1 n -
            (sourceBirkhoffFourier (higherSobolevSourceInclusion m b)).1 n ∧
        (higherSobolevBirkhoffFourierRemainder m s b).2.val n =
          (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m b)).2 n -
            (sourceBirkhoffFourier (higherSobolevSourceInclusion m b)).2 n := by
  obtain ⟨V,hV,haV,E,hE,he⟩ := D.exists_local_higherSobolevBirkhoffFourier_analytic m hm a
  have hEq (b : SobolevSource m) (hb : b ∈ V) :
      higherSobolevBirkhoffFourierRemainder m s b = E b :=
    higherSobolevBirkhoffFourierRemainder_eq_of_coordinates m s b (E b) (he b hb)
  refine ⟨V,hV,haV,?_,?_⟩
  · intro b hb
    apply (hE b hb).congr
    filter_upwards [hV.mem_nhds hb] with c hc
    exact (hEq c hc).symm
  · intro b hb n
    rw [hEq b hb]
    exact he b hb n

/-- Every coefficient of the canonical stronger remainder is the literal
Birkhoff-minus-Fourier coefficient on the full real original Hm space. -/
theorem higherSobolevBirkhoffFourierRemainder_coordinates
    (m : ℕ) (hm : 1 ≤ m) (a : realTypeHigherSobolevSourceLocus m) (n : ℤ) :
    (higherSobolevBirkhoffFourierRemainder m s a.val).1.val n =
      (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m a.val)).1 n -
        (sourceBirkhoffFourier (higherSobolevSourceInclusion m a.val)).1 n ∧
    (higherSobolevBirkhoffFourierRemainder m s a.val).2.val n =
      (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m a.val)).2 n -
        (sourceBirkhoffFourier (higherSobolevSourceInclusion m a.val)).2 n := by
  obtain ⟨V,_,haV,_,h⟩ := D.exists_local_higherSobolevBirkhoffFourierRemainder_analytic m hm a
  exact h a.val haV n

/-- The same canonical stronger-target remainder is uniformly bounded on
each entire real Hm ball, for every positive integer order. -/
theorem higherSobolevBirkhoffFourierRemainder_uniform_real_ball
    (m : ℕ) (hm : 1 ≤ m) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeHigherSobolevSourceLocus m, ‖a.val‖ ≤ R →
      ‖higherSobolevBirkhoffFourierRemainder m s a.val‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := D.birkhoff_fourier_uniform_real_Hm_ball m hm R hR
  refine ⟨C,hC,?_⟩
  intro a ha
  obtain ⟨E,hE,he⟩ := h a ha
  rw [higherSobolevBirkhoffFourierRemainder_eq_of_coordinates m s a.val E he]
  exact hE

/-- The canonical stronger remainder takes bounded sets of real original
Hm sources to bounded sets of h^(m+1). -/
theorem higherSobolevBirkhoffFourierRemainder_image_isBounded
    (m : ℕ) (hm : 1 ≤ m) {S : Set (SobolevSource m)}
    (hS : Bornology.IsBounded S)
    (hreal : ∀ b ∈ S, IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion m b))) :
    Bornology.IsBounded (higherSobolevBirkhoffFourierRemainder m s '' S) := by
  obtain ⟨R,hR⟩ := hS.exists_norm_le
  obtain ⟨C,_,hC⟩ := D.higherSobolevBirkhoffFourierRemainder_uniform_real_ball
    m hm (max R 0) (le_max_right _ _)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C,?_⟩
  rintro _ ⟨b,hb,rfl⟩
  exact hC ⟨b,hreal b hb⟩ ((hR b hb).trans (le_max_left _ _))

/-- The canonical map is analytic into the stronger target at every
real original Hm point. -/
theorem higherSobolevBirkhoffFourierRemainder_analyticAt_real
    (m : ℕ) (hm : 1 ≤ m) (a : realTypeHigherSobolevSourceLocus m) :
    AnalyticAt ℂ (higherSobolevBirkhoffFourierRemainder m s) a.val := by
  obtain ⟨V,_,haV,h,_⟩ := D.exists_local_higherSobolevBirkhoffFourierRemainder_analytic m hm a
  exact h a.val haV

end SourceBirkhoffMapComplexData

/-- A single constructed Birkhoff map has a canonical Fourier remainder
that gains a derivative analytically and preserves boundedness at every
positive integer Sobolev order. -/
theorem exists_sourceBirkhoffMap_canonical_bounded_one_smoothing :
    ∃ W₀ B W : Set (CoeffPair 2), ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
      SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s ∧
      ∀ m : ℕ, 1 ≤ m →
        (∀ a : realTypeHigherSobolevSourceLocus m,
          AnalyticAt ℂ (higherSobolevBirkhoffFourierRemainder m s) a.val) ∧
        (∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
          ∀ a : realTypeHigherSobolevSourceLocus m, ‖a.val‖ ≤ R →
            ‖higherSobolevBirkhoffFourierRemainder m s a.val‖ ≤ C) := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  exact ⟨W₀,B,W,s,D,fun m hm =>
    ⟨D.higherSobolevBirkhoffFourierRemainder_analyticAt_real m hm,
     D.higherSobolevBirkhoffFourierRemainder_uniform_real_ball m hm⟩⟩

end NLS.ZakharovShabat
