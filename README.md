# Erdős Problem 176: Lean Formalization Attempt for `N(k,2)`

This repository is an attempt to Lean-formalize a proof outline for a polynomial
upper bound on the Erdős Problem 176 quantity `N(k,2)` [Reference 1].

This Lean formalization was carried out with reference to the existing
discussion in the Erdős Problem 176 forum thread [Reference 2].

You can also check the proof in your browser:
[Lean4web Live](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos176-nk2-polynomial-bound-lean%2Fmain%2Ferdos176_lean4web.lean)

(This is the Lean4web file for the main `k >= 5` theorem. The small cases
`k = 1, 2, 3, 4` are handled separately in the appendix below.)

Consequently, for the finite-valued range `k >= 2`, the original `C^k`-type
upper-bound question follows from this proof: the main theorem gives an
`O(k^3)` bound for `k >= 5`, and the remaining finite cases `k = 2, 3, 4`
can be absorbed into the constant `C`.

## Final Lean Target: Natural Language vs. Lean Formalization

### Natural Language Target

For every `k >= 5`, let `N(k,2)` be the least `N` such that every `±1`
coloring of an interval of length `N` contains an ordinary `k`-term arithmetic
progression whose signed sum has absolute value at least `2`.  The target bound
is

```text
N(k,2) <= floor(2 * (k^2 - 1) * (k - 1) * (2*k + 1) / (k - 3)) + 1.
```

### Final Lean Formalization Target 1: Compact

```lean
theorem Erdos176Lean.erdos176Number_le_report_bound
    (k : ℕ) (hk : 5 ≤ k) :
    Erdos176Lean.erdos176Number k hk
      ≤ Nat.floor
        (2 * (((k : ℝ) ^ 2 - 1) * ((k : ℝ) - 1) * (2 * (k : ℝ) + 1))
          / ((k : ℝ) - 3)) + 1
```

Comparison table:

| Natural-language statement | Lean formalization |
| --- | --- |
| `k >= 5` | `(k : ℕ) (hk : 5 ≤ k)` |
| `N(k,2)` | `Erdos176Lean.erdos176Number k hk` |
| The report threshold | `Nat.floor (2 * (((k : ℝ) ^ 2 - 1) * ((k : ℝ) - 1) * (2 * (k : ℝ) + 1)) / ((k : ℝ) - 3)) + 1` |
| `N(k,2)` is at most the report threshold. | `Erdos176Lean.erdos176Number k hk ≤ ...` |

### Final Lean Formalization Target 2: Expanded

The following theorem is the same target as the compact version above, but with
the `N(k,2)`-type minimum and AP property expanded inside the theorem statement:

```lean
theorem Erdos176Lean.erdos176Number_le_report_bound_expanded
    (k : ℕ) (hk : 5 ≤ k) :
    ∃ M : ℕ,
      (∃ hMpos : 0 < M,
        letI : NeZero M := ⟨Nat.ne_of_gt hMpos⟩
        ∀ f : Fin M → ℤ,
          (∀ x : Fin M, f x = -1 ∨ f x = 1) →
            ∃ d : ℕ, 0 < d ∧ ∃ a : Fin M,
              ∃ hnowrap : ¬ (M ≤ a.val + (k - 1) * d),
                2 ≤ |∑ j : Fin k, f
                  ⟨a.val + j.val * d, by
                    have hbound : a.val + (k - 1) * d < M := Nat.lt_of_not_ge hnowrap
                    have hjle : j.val ≤ k - 1 := Nat.le_pred_of_lt j.isLt
                    exact lt_of_le_of_lt
                      (Nat.add_le_add_left (Nat.mul_le_mul_right d hjle) a.val) hbound⟩|)
      ∧ (∀ N : ℕ,
        (∃ hNpos : 0 < N,
          letI : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
          ∀ f : Fin N → ℤ,
            (∀ x : Fin N, f x = -1 ∨ f x = 1) →
              ∃ d : ℕ, 0 < d ∧ ∃ a : Fin N,
                ∃ hnowrap : ¬ (N ≤ a.val + (k - 1) * d),
                  2 ≤ |∑ j : Fin k, f
                    ⟨a.val + j.val * d, by
                      have hbound : a.val + (k - 1) * d < N := Nat.lt_of_not_ge hnowrap
                      have hjle : j.val ≤ k - 1 := Nat.le_pred_of_lt j.isLt
                      exact lt_of_le_of_lt
                        (Nat.add_le_add_left (Nat.mul_le_mul_right d hjle) a.val) hbound⟩|) →
          M ≤ N)
      ∧ M ≤ Nat.floor
        (2 * (((k : ℝ) ^ 2 - 1) * ((k : ℝ) - 1) * (2 * (k : ℝ) + 1))
          / ((k : ℝ) - 3)) + 1
```

Comparison table:

| Natural-language statement | Lean formalization |
| --- | --- |
| `k >= 5` | `(k : ℕ) (hk : 5 ≤ k)` |
| There exists a candidate value for `N(k,2)`. | `∃ M : ℕ, ...` |
| &nbsp;&nbsp;`M` has the desired AP property. | `∃ hMpos : 0 < M, ...` followed by the coloring-to-AP statement for `Fin M` |
| &nbsp;&nbsp;&nbsp;&nbsp;Every `±1` coloring of `[0, M)` is considered. | `∀ f : Fin M → ℤ, (∀ x : Fin M, f x = -1 ∨ f x = 1) → ...` |
| &nbsp;&nbsp;&nbsp;&nbsp;There is a positive common difference. | `∃ d : ℕ, 0 < d ∧ ...` |
| &nbsp;&nbsp;&nbsp;&nbsp;There is a starting point in the interval. | `∃ a : Fin M, ...` |
| &nbsp;&nbsp;&nbsp;&nbsp;The AP does not leave the interval. | `hnowrap : ¬ (M ≤ a.val + (k - 1) * d)` |
| &nbsp;&nbsp;&nbsp;&nbsp;The ordinary `k`-term AP sum is written explicitly. | `∑ j : Fin k, f ⟨a.val + j.val * d, proof from hnowrap⟩` |
| &nbsp;&nbsp;&nbsp;&nbsp;The AP sum has absolute value at least `2`. | `2 ≤ |∑ j : Fin k, f ⟨a.val + j.val * d, proof from hnowrap⟩|` |
| &nbsp;&nbsp;`M` is least among all `N` with the same AP property. | `∀ N : ℕ, (expanded AP property for N) → M ≤ N` |
| &nbsp;&nbsp;The least value is bounded by the report threshold. | `M ≤ Nat.floor (2 * (((k : ℝ) ^ 2 - 1) * ((k : ℝ) - 1) * (2 * (k : ℝ) + 1)) / ((k : ℝ) - 3)) + 1` |

## Check on the Web

You can check the proof in your browser:
[Lean4web Live](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos176-nk2-polynomial-bound-lean%2Fmain%2Ferdos176_lean4web.lean)

The standalone web-checkable file is:

```text
erdos176_lean4web.lean
```

It imports only Mathlib:

```lean
import Mathlib
```

You can paste or load this file in the Lean web editor:

```text
https://live.lean-lang.org/
```

The file ends with:

```lean
#check Erdos176Lean.erdos176Number_le_report_bound
#print axioms Erdos176Lean.erdos176Number_le_report_bound
#check Erdos176Lean.erdos176Number_le_report_bound_expanded
#print axioms Erdos176Lean.erdos176Number_le_report_bound_expanded
#check Erdos176Lean.exists_ordinaryAPSum_abs_ge_two_of_htmlBoundNat_le
#print axioms Erdos176Lean.exists_ordinaryAPSum_abs_ge_two_of_htmlBoundNat_le
```

On Lean4web, a successful check should show no errors and no messages other than
the expected `#check` / `#print axioms` output.  The axiom output is the standard
Lean/Mathlib foundation set:

```text
[propext, Classical.choice, Quot.sound]
```

## Main Lean File

The current Lean development is in:

```text
Erdos176Lean/Basic.lean
```

Current important theorem names include:

```lean
Erdos176Lean.casselsGeomLowerClaim_true
Erdos176Lean.average_cyclicAPSum_lower_dTwoK
Erdos176Lean.average_cyclicAPSum_upper_dTwoK
Erdos176Lean.upper_lt_lower_of_threshold_real
Erdos176Lean.average_bounds_incompatible_real
Erdos176Lean.exists_ordinaryAPSum_abs_ge_two_of_htmlBoundNat_le
Erdos176Lean.erdos176Number_le_report_bound
```

## How to Check

Build with Lake:

```bash
lake build
```

Current local check:

```text
Build completed successfully (8560 jobs).
```

Search for unfinished or nonstandard proof placeholders:

```bash
rg -n "\\bsorry\\b|\\badmit\\b|\\baxiom\\b|unsafe" . --glob "*.lean" --glob "!**/.lake/**"
```

Current local result:

```text
no matches
```

## AI Usage

This computation and comment were prepared with assistance from Codex 5.5 using
xhigh reasoning, and ChatGPT 5.5 Pro.

## References

- [1] Erdős Problem 176: <https://www.erdosproblems.com/176>
- [2] Erdős Problems forum thread for Problem 176:
  <https://www.erdosproblems.com/forum/thread/176>

## Appendix: Small Values of `k`

The final Lean theorem above is deliberately stated for `k >= 5`.  This is not
a hidden assumption inside the theorem: it is part of the theorem statement.
The displayed bound contains the denominator `k - 3`, and the averaging
comparison used in the proof is designed for the range beyond the small cases.

### k=1

There is no finite `N(1,2)` for this AP-sum property: a one-term AP has sum
`±1`, so its absolute value is never at least `2`.  In particular, this is not
`N(1,2) = 2`; the usual finite-minimum statement does not apply to `k = 1`.

Lean file:

```text
Erdos176Lean/K1.lean
```

Lean4web:
[Click here](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos176-nk2-polynomial-bound-lean%2Fmain%2Ferdos176_k1_lean4web.lean)

### k=2

The finite Boolean formulation gives `N(2,2) = 3`.

Lean file:

```text
Erdos176Lean/K2.lean
```

Lean4web:
[Click here](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos176-nk2-polynomial-bound-lean%2Fmain%2Ferdos176_k2_lean4web.lean)

### k=3

The finite Boolean formulation gives `N(3,2) = 9`, matching the classical
`W(2,3) = 9` case.

Lean file:

```text
Erdos176Lean/K3.lean
```

Lean4web:
[Click here](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos176-nk2-polynomial-bound-lean%2Fmain%2Ferdos176_k3_lean4web.lean)

### k =4

The finite Boolean formulation gives `N(4,2) = 13`.

Lean file:

```text
Erdos176Lean/K4.lean
```

Lean4web:
[Click here](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos176-nk2-polynomial-bound-lean%2Fmain%2Ferdos176_k4_lean4web.lean)

## Appendix: Relation to the `C^k` Question

The original Problem 176 question asks whether there is an absolute constant
`C` such that `N(k,2) <= C^k`.  In the present AP-sum formulation, this is a
finite-valued question for `k >= 2`; the case `k = 1` has no finite `N(1,2)`.

The main Lean theorem proves something stronger for the infinite range
`k >= 5`: it gives the explicit polynomial bound

```text
N(k,2) <= floor(2 * (k^2 - 1) * (k - 1) * (2*k + 1) / (k - 3)) + 1.
```

The right-hand side is `O(k^3)`.  Concretely, it is enough to choose constants
`A > 0` and `k0` such that, for all `k >= k0`,

```text
N(k,2) <= A * k^3.
```

Then choose `C > 1` large enough that, for all `k >= k0`,

```text
A * k^3 <= C^k.
```

This is possible because exponential growth eventually dominates polynomial
growth:

```text
lim_{k -> infinity} (A * k^3) / C^k = 0.
```

Combining the two inequalities gives

```text
N(k,2) <= A * k^3 <= C^k
```

for all sufficiently large `k`.

The only remaining finite cases below the theorem's hypothesis are
`k = 2, 3, 4`.  A finite list of cases does not obstruct a `C^k` bound: after
checking those cases separately, one can enlarge `C` once so that the inequality
also covers them.  The case `k = 1` is different, since `N(1,2)` is not finite
in this formulation.  This is why the small-case appendix and the main
`k >= 5` theorem together address the finite-valued `C^k`-type question.
