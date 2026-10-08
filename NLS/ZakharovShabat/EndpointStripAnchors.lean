import NLS.ZakharovShabat.EndpointStripPropagation

/-! # Reaching any signed index from distant anchors

The positive and negative tails are treated separately. Every strip used
has absolute index at least that of the target, preserving its threshold.
-/
noncomputable section
open scoped Classical
namespace NLS.ZakharovShabat

/-- Two distant anchors and two occurrences on each intervening strip fix the target pair. -/
theorem endpoint_pair_refined_of_anchors (N A : ℕ) (n : ℤ) (ξ η : ℤ → ℂ)
    (hnA : n.natAbs ≤ A) (hAN : A ≤ N)
    (horder : Monotone (fun k : ℤ ×ₗ Fin 2 => (periodicEndpointSlot ξ η k).re))
    (hcount : ∀ m : ℤ, n.natAbs ≤ m.natAbs → m.natAbs ≤ A →
      ((centralPeriodicSlots N).filter (fun k => periodicEndpointSlot ξ η k ∈ resonantStrip m)).card = 2)
    (hrefine : ∀ m : ℤ, n.natAbs ≤ m.natAbs → m.natAbs ≤ A →
      ξ m ∈ resonantStrip m ∧ η m ∈ resonantStrip m →
      ξ m ∈ refinedResonantDisk m ∧ η m ∈ refinedResonantDisk m)
    (hpos : ξ A ∈ refinedResonantDisk A ∧ η A ∈ refinedResonantDisk A)
    (hneg : ξ (-(A:ℤ)) ∈ refinedResonantDisk (-(A:ℤ)) ∧ η (-(A:ℤ)) ∈ refinedResonantDisk (-(A:ℤ))) :
    ξ n ∈ refinedResonantDisk n ∧ η n ∈ refinedResonantDisk n := by
  by_cases hn : 0 ≤ n
  · have hdown : ∀ d : ℕ, d ≤ A-n.natAbs →
        ξ ((A:ℤ)-d) ∈ refinedResonantDisk ((A:ℤ)-d) ∧ η ((A:ℤ)-d) ∈ refinedResonantDisk ((A:ℤ)-d) := by
      intro d
      induction d with
      | zero => intro _; simpa only [Nat.cast_zero, sub_zero] using hpos
      | succ d ih =>
        intro hd
        have hi := ih (by omega)
        let m : ℤ := (A:ℤ)-(d+1:ℕ)
        have hm : n.natAbs ≤ m.natAbs := by dsimp [m]; omega
        have hmA : m.natAbs ≤ A := by dsimp [m]; omega
        have hm1 : m+1 = (A:ℤ)-d := by dsimp [m]; omega
        have hm1low : n.natAbs ≤ (m+1).natAbs := by dsimp [m]; omega
        have hm1A : (m+1).natAbs ≤ A := by dsimp [m]; omega
        have hs := endpoint_pair_strip_step_left N m ξ η (hmA.trans hAN) (hm1A.trans hAN)
          horder (hcount m hm hmA) (hcount (m+1) hm1low hm1A)
          (by simpa only [hm1] using hi.1) (by simpa only [hm1] using hi.2)
        exact hrefine m hm hmA hs
    have he : (A:ℤ)-((A-n.natAbs:ℕ):ℤ) = n := by omega
    simpa only [he] using hdown (A-n.natAbs) le_rfl
  · have hup : ∀ d : ℕ, d ≤ A-n.natAbs →
        ξ (-(A:ℤ)+d) ∈ refinedResonantDisk (-(A:ℤ)+d) ∧ η (-(A:ℤ)+d) ∈ refinedResonantDisk (-(A:ℤ)+d) := by
      intro d
      induction d with
      | zero => intro _; simpa only [Nat.cast_zero, add_zero] using hneg
      | succ d ih =>
        intro hd
        have hi := ih (by omega)
        let m : ℤ := -(A:ℤ)+d
        have hm : n.natAbs ≤ m.natAbs := by dsimp [m]; omega
        have hmA : m.natAbs ≤ A := by dsimp [m]; omega
        have hm1low : n.natAbs ≤ (m+1).natAbs := by dsimp [m]; omega
        have hm1A : (m+1).natAbs ≤ A := by dsimp [m]; omega
        have hs := endpoint_pair_strip_step_right N m ξ η (hmA.trans hAN) (hm1A.trans hAN)
          horder (hcount m hm hmA) (hcount (m+1) hm1low hm1A) hi.1 hi.2
        have h := hrefine (m+1) hm1low hm1A hs
        simpa only [m, Nat.cast_add, Nat.cast_one, add_assoc] using h
    have he : -(A:ℤ)+((A-n.natAbs:ℕ):ℤ) = n := by omega
    simpa only [he] using hup (A-n.natAbs) le_rfl

end NLS.ZakharovShabat
