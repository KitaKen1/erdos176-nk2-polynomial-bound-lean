import Erdos176Lean.Basic

/-!
# Erdős problem 176: `k = 1` appendix

For `l = 2`, the case `k = 1` has no finite value: a one-term AP has signed
sum `±1`, never absolute value at least `2`.
-/

namespace Erdos176Lean

theorem not_erdos176Good_one (N : ℕ) :
    ¬ erdos176Good 1 N := by
  intro h
  rcases h with ⟨_hNpos, hall⟩
  let f : Fin N → ℤ := fun _ => 1
  have hpm : ∀ x : Fin N, f x = -1 ∨ f x = 1 := by
    intro _x
    right
    rfl
  rcases hall f hpm with ⟨d, _hd, a, hnowrap, hge⟩
  have hsum : ordinaryAPSum f 1 a d hnowrap = 1 := by
    simp [ordinaryAPSum, f]
  rw [hsum] at hge
  norm_num at hge

end Erdos176Lean
