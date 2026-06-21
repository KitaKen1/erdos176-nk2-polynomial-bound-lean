import Mathlib

/-!
# Erdős problem 176: finite Boolean checker for small `k`

This helper is for the small-case appendix only.  It does not participate in
the main `k >= 5` proof in `Erdos176Lean/Basic.lean`.
-/

namespace Erdos176Lean
namespace SmallK

open scoped BigOperators

def boolSign (b : Bool) : ℤ :=
  if b then 1 else -1

def bitColor (N code : ℕ) (x : Fin N) : Bool :=
  ((code / (2 ^ x.val)) % 2) == 1

def apSumCode (N k a d code : ℕ) : ℤ :=
  (List.range k).foldl
    (fun s j =>
      if h : a + j * d < N then
        s + boolSign (bitColor N code ⟨a + j * d, h⟩)
      else
        s)
    0

def hasLargeAPCode (k N code : ℕ) : Bool :=
  (List.range N).any fun a =>
    (List.range N).any fun d =>
      decide (0 < d ∧ a + (k - 1) * d < N ∧ 2 ≤ |apSumCode N k a d code|)

def goodCode (k N : ℕ) : Bool :=
  (List.range (2 ^ N)).all fun code => hasLargeAPCode k N code

def allBeforeFalse (k N : ℕ) : Bool :=
  (List.range N).all fun M => decide (goodCode k M = false)

def exactAtCode (k N : ℕ) : Bool :=
  goodCode k N && allBeforeFalse k N

end SmallK
end Erdos176Lean
