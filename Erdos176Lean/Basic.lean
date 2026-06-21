import Mathlib

set_option linter.style.header false

/-!
# Erdős problem 176: Lean checks for the reported proof attempt

Forum provenance:
This Lean formalization was carried out with reference to the existing
discussion in the Erdős Problem 176 forum thread:
https://www.erdosproblems.com/forum/thread/176

AI usage:
This Lean development and accompanying explanations were prepared with
assistance from Codex 5.5 using xhigh reasoning, and ChatGPT 5.5 Pro.

The local `176.html` proof attempt reduces the claimed polynomial bound to two
average estimates for cyclic arithmetic progressions.  This file starts by
checking the algebraic part of that reduction.

The theorem `upper_lt_lower_of_threshold` says that the numerical threshold in
the report is exactly strong enough: once

`2 * ((k^2 - 1) * (k - 1) * (2*k + 1)) / (k - 3) < N`,

the proposed wrap-error upper bound is strictly below the Fejér lower bound
specialized at `D = 2*k`.
-/

namespace Erdos176Lean

open scoped BigOperators

section CyclicAP

variable {N : ℕ} [NeZero N]

/-- The cyclic index `a + j*d` modulo `N`. -/
def cyclicIndex (a : Fin N) (j d : ℕ) : Fin N :=
  ⟨(a.val + j * d) % N, Nat.mod_lt _ (Nat.pos_of_neZero N)⟩

/-- The sum of a cyclic `k`-term arithmetic progression. -/
def cyclicAPSum (f : Fin N → ℤ) (k : ℕ) (a : Fin N) (d : ℕ) : ℤ :=
  ∑ j ∈ Finset.range k, f (cyclicIndex a j d)

/-- The cyclic progression has wrapped around the end of `[0,N)`. -/
def wraps (k : ℕ) (a : Fin N) (d : ℕ) : Prop :=
  N ≤ a.val + (k - 1) * d

/-- The ordinary, non-wrapping AP sum, available only with a non-wrap proof. -/
def ordinaryAPSum
    (f : Fin N → ℤ) (k : ℕ) (a : Fin N) (d : ℕ)
    (hnowrap : ¬ wraps (N := N) k a d) : ℤ :=
  ∑ j : Fin k, f
    ⟨a.val + j.val * d, by
      have hbound : a.val + (k - 1) * d < N := Nat.lt_of_not_ge hnowrap
      have hjle : j.val ≤ k - 1 := Nat.le_pred_of_lt j.isLt
      exact lt_of_le_of_lt
        (Nat.add_le_add_left (Nat.mul_le_mul_right d hjle) a.val) hbound⟩

theorem cyclicAPSum_eq_ordinaryAPSum
    (f : Fin N → ℤ) (k : ℕ) (a : Fin N) (d : ℕ)
    (hnowrap : ¬ wraps (N := N) k a d) :
    cyclicAPSum f k a d = ordinaryAPSum f k a d hnowrap := by
  unfold cyclicAPSum ordinaryAPSum
  rw [← Fin.sum_univ_eq_sum_range (fun j => f (cyclicIndex a j d)) k]
  refine Finset.sum_congr rfl ?_
  intro j hj
  apply congrArg f
  apply Fin.ext
  have hbound : a.val + (k - 1) * d < N := Nat.lt_of_not_ge hnowrap
  have hjle : j.val ≤ k - 1 := Nat.le_pred_of_lt j.isLt
  have hlt : a.val + j.val * d < N :=
    lt_of_le_of_lt
      (Nat.add_le_add_left (Nat.mul_le_mul_right d hjle) a.val) hbound
  simp [cyclicIndex, Nat.mod_eq_of_lt hlt]

theorem abs_cyclicAPSum_le
    (f : Fin N → ℤ)
    (hpm : ∀ x, f x = -1 ∨ f x = 1)
    (k : ℕ) (a : Fin N) (d : ℕ) :
    |cyclicAPSum f k a d| ≤ (k : ℤ) := by
  unfold cyclicAPSum
  calc
    |∑ j ∈ Finset.range k, f (cyclicIndex a j d)|
        ≤ ∑ j ∈ Finset.range k, |f (cyclicIndex a j d)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range k, (1 : ℤ) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          rcases hpm (cyclicIndex a j d) with h | h <;> simp [h]
    _ = (k : ℤ) := by simp

theorem cyclicAPSum_sq_le
    (f : Fin N → ℤ)
    (hpm : ∀ x, f x = -1 ∨ f x = 1)
    (k : ℕ) (a : Fin N) (d : ℕ) :
    (cyclicAPSum f k a d) ^ 2 ≤ (k : ℤ) ^ 2 := by
  rw [sq_le_sq]
  simpa [abs_of_nonneg (Int.natCast_nonneg k)]
    using abs_cyclicAPSum_le (N := N) f hpm k a d

theorem sq_le_one_of_abs_lt_two (z : ℤ) (h : |z| < 2) :
    z ^ 2 ≤ 1 := by
  have hz : |z| ≤ (1 : ℤ) := by omega
  have hsq : z ^ 2 ≤ (1 : ℤ) ^ 2 := by
    rw [sq_le_sq]
    simpa using hz
  simpa using hsq

/--
For a fixed excess length `m`, at most `m` starting points `a : Fin N` satisfy
`N ≤ a + m`.  This is the finite counting ingredient behind the report's
wrap estimate.
-/
theorem card_wrapStarts_le (N m : ℕ) [NeZero N] :
    ((Finset.univ : Finset (Fin N)).filter fun a => N ≤ a.val + m).card ≤ m := by
  by_cases hm : m = 0
  · subst hm
    simp [Nat.not_le_of_gt]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    let wrapToFin : {a : Fin N // N ≤ a.val + m} → Fin m := fun a =>
      ⟨a.val.val + m - N, by
        have hlt : a.val.val < N := a.val.isLt
        have hwrap : N ≤ a.val.val + m := a.property
        omega⟩
    have hinj : Function.Injective wrapToFin := by
      intro a b hab
      apply Subtype.ext
      apply Fin.ext
      have hwrapa : N ≤ a.val.val + m := a.property
      have hwrapb : N ≤ b.val.val + m := b.property
      have hvals : a.val.val + m - N = b.val.val + m - N :=
        congrArg Fin.val hab
      omega
    have hcard := Fintype.card_le_of_injective wrapToFin hinj
    simpa [Fintype.card_subtype] using hcard

theorem fixedD_second_moment_upper
    (f : Fin N → ℤ)
    (hpm : ∀ x, f x = -1 ∨ f x = 1)
    {k d : ℕ}
    (hk : 1 ≤ k)
    (hsmall : ∀ a : Fin N, ¬ wraps (N := N) k a d →
      |cyclicAPSum f k a d| < 2) :
    (∑ a : Fin N, (cyclicAPSum f k a d) ^ 2)
      ≤ (N : ℤ) + (((k : ℤ) ^ 2 - 1) * (((k - 1) * d : ℕ) : ℤ)) := by
  classical
  let K : ℤ := (k : ℤ) ^ 2 - 1
  let p : Fin N → Prop := fun a => wraps (N := N) k a d
  have hKnonneg : 0 ≤ K := by
    have hkz : (1 : ℤ) ≤ k := by exact_mod_cast hk
    dsimp [K]
    nlinarith
  have hpoint :
      ∀ a : Fin N,
        (cyclicAPSum f k a d) ^ 2 ≤ 1 + if p a then K else 0 := by
    intro a
    by_cases hp : p a
    · have hsq := cyclicAPSum_sq_le (N := N) f hpm k a d
      have hK : (1 : ℤ) + K = (k : ℤ) ^ 2 := by
        dsimp [K]
        ring
      simpa [hp, hK] using hsq
    · have hs := sq_le_one_of_abs_lt_two
        (cyclicAPSum f k a d) (hsmall a (by simpa [p] using hp))
      simpa [hp] using hs
  calc
    (∑ a : Fin N, (cyclicAPSum f k a d) ^ 2)
        ≤ ∑ a : Fin N, (1 + if p a then K else 0) :=
          Finset.sum_le_sum (by
            intro a ha
            exact hpoint a)
    _ = (N : ℤ) + K * (((Finset.univ : Finset (Fin N)).filter p).card : ℤ) := by
          rw [Finset.sum_add_distrib]
          have hconst : (∑ _a : Fin N, (1 : ℤ)) = (N : ℤ) := by
            simp [Finset.card_univ, Fintype.card_fin]
          have hif :
              (∑ a : Fin N, (if p a then K else 0))
                = K * (((Finset.univ : Finset (Fin N)).filter p).card : ℤ) := by
            rw [Finset.sum_ite]
            simp [Finset.sum_const, mul_comm]
          rw [hconst, hif]
    _ ≤ (N : ℤ) + K * (((k - 1) * d : ℕ) : ℤ) := by
          have hcardNat :
              ((Finset.univ : Finset (Fin N)).filter p).card ≤ (k - 1) * d := by
            simpa [p, wraps] using card_wrapStarts_le N ((k - 1) * d)
          have hcard :
              (((Finset.univ : Finset (Fin N)).filter p).card : ℤ)
                ≤ (((k - 1) * d : ℕ) : ℤ) := by
            exact_mod_cast hcardNat
          nlinarith
    _ = (N : ℤ) + (((k : ℤ) ^ 2 - 1) * (((k - 1) * d : ℕ) : ℤ)) := by
          rfl

theorem sum_range_succ_nat (D : ℕ) :
    (∑ i ∈ Finset.range D, (i + 1)) = D * (D + 1) / 2 := by
  have h := (Finset.sum_range_succ' (fun i : ℕ => i) D).symm
  calc
    (∑ i ∈ Finset.range D, (i + 1))
        = ∑ i ∈ Finset.range (D + 1), i := by simpa using h
    _ = D * (D + 1) / 2 := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          using Finset.sum_range_id (D + 1)

theorem sum_range_succ_int (D : ℕ) :
    (∑ i ∈ Finset.range D, (((i + 1 : ℕ) : ℤ)))
      = ((D * (D + 1) / 2 : ℕ) : ℤ) := by
  exact_mod_cast sum_range_succ_nat D

theorem second_moment_upper_range
    (f : Fin N → ℤ)
    (hpm : ∀ x, f x = -1 ∨ f x = 1)
    {k D : ℕ}
    (hk : 1 ≤ k)
    (hsmall : ∀ i ∈ Finset.range D, ∀ a : Fin N,
      ¬ wraps (N := N) k a (i + 1) →
        |cyclicAPSum f k a (i + 1)| < 2) :
    (∑ i ∈ Finset.range D, ∑ a : Fin N, (cyclicAPSum f k a (i + 1)) ^ 2)
      ≤ (D : ℤ) * (N : ℤ)
        + (((k : ℤ) ^ 2 - 1) * ((k - 1 : ℕ) : ℤ)
          * ((D * (D + 1) / 2 : ℕ) : ℤ)) := by
  let K : ℤ := (k : ℤ) ^ 2 - 1
  calc
    (∑ i ∈ Finset.range D, ∑ a : Fin N, (cyclicAPSum f k a (i + 1)) ^ 2)
        ≤ ∑ i ∈ Finset.range D,
            ((N : ℤ) + K * ((((k - 1) * (i + 1) : ℕ) : ℤ))) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          simpa [K] using
            fixedD_second_moment_upper (N := N) f hpm (k := k) (d := i + 1) hk
              (hsmall i hi)
    _ = (D : ℤ) * (N : ℤ)
        + K * ((k - 1 : ℕ) : ℤ)
          * (∑ i ∈ Finset.range D, (((i + 1 : ℕ) : ℤ))) := by
          rw [Finset.sum_add_distrib]
          have hNsum :
              (∑ _i ∈ Finset.range D, (N : ℤ)) = (D : ℤ) * (N : ℤ) := by
            simp [Finset.sum_const]
          have hKsum :
              (∑ i ∈ Finset.range D,
                  K * ((((k - 1) * (i + 1) : ℕ) : ℤ)))
                = K * ((k - 1 : ℕ) : ℤ)
                  * (∑ i ∈ Finset.range D, (((i + 1 : ℕ) : ℤ))) := by
            calc
              (∑ i ∈ Finset.range D,
                  K * ((((k - 1) * (i + 1) : ℕ) : ℤ)))
                  = ∑ i ∈ Finset.range D,
                      (K * ((k - 1 : ℕ) : ℤ)) * (((i + 1 : ℕ) : ℤ)) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    norm_num [Nat.cast_mul]
                    ring
              _ = (K * ((k - 1 : ℕ) : ℤ))
                    * (∑ i ∈ Finset.range D, (((i + 1 : ℕ) : ℤ))) := by
                    rw [Finset.mul_sum]
              _ = K * ((k - 1 : ℕ) : ℤ)
                    * (∑ i ∈ Finset.range D, (((i + 1 : ℕ) : ℤ))) := by
                    ring
          rw [hNsum, hKsum]
    _ = (D : ℤ) * (N : ℤ)
        + (((k : ℤ) ^ 2 - 1) * ((k - 1 : ℕ) : ℤ)
          * ((D * (D + 1) / 2 : ℕ) : ℤ)) := by
          rw [sum_range_succ_int]

end CyclicAP

section FourierSetup

variable {N : ℕ}

/-- A cyclic AP sum written on `ZMod N`, the natural domain for finite Fourier analysis. -/
noncomputable def zmodAPSum (f : ZMod N → ℂ) (k : ℕ) (a d : ZMod N) : ℂ :=
  ∑ j ∈ Finset.range k, f (a + j • d)

/-- The scalar geometric power sum that appears after diagonalizing by characters. -/
noncomputable def geomPowerSum (z : ℂ) (k d : ℕ) : ℂ :=
  ∑ j ∈ Finset.range k, z ^ (j * d)

/-- The scalar energy whose lower bound is the Cassels/Turán power-sum input. -/
noncomputable def geomPowerEnergy (z : ℂ) (k D : ℕ) : ℝ :=
  ∑ i ∈ Finset.range D, ‖geomPowerSum z k (i + 1)‖ ^ 2

/-- The right-hand side of the scalar Cassels/Turán power-sum lower bound. -/
noncomputable def casselsRhs (k D : ℕ) : ℝ :=
  ((k : ℝ) * (D + 1 : ℝ) - (k : ℝ) ^ 2) / 2

/--
The Fejér-pair term used in the standard proof of the Cassels/Turán power-sum
inequality.  It is a normalized squared Dirichlet sum, hence nonnegative.
-/
noncomputable def fejerPairTerm (z : ℂ) (D p q : ℕ) : ℝ :=
  (D + 1 : ℝ)⁻¹ *
    ‖∑ r ∈ Finset.range (D + 1), (z ^ p * starRingEnd ℂ (z ^ q)) ^ r‖ ^ 2

/--
The Fejér-pair energy before expanding the square and collecting by
differences.  The diagonal terms alone already give a useful lower bound.
-/
noncomputable def fejerPairEnergy (z : ℂ) (k D : ℕ) : ℝ :=
  ∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k, fejerPairTerm z D p q

theorem fejerPair_diag_base_one {z : ℂ} (hz : ‖z‖ = 1) (p : ℕ) :
    z ^ p * starRingEnd ℂ (z ^ p) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp [norm_pow, hz]

theorem fejerPair_diag_term {z : ℂ} (hz : ‖z‖ = 1) (p D : ℕ) :
    fejerPairTerm z D p p = (D + 1 : ℝ) := by
  unfold fejerPairTerm
  rw [fejerPair_diag_base_one hz p]
  simp only [one_pow, Finset.sum_const, nsmul_eq_mul, Finset.card_range, mul_one]
  rw [norm_natCast]
  have hpos : (0 : ℝ) < D + 1 := by positivity
  field_simp [ne_of_gt hpos]
  norm_num [Nat.cast_add, Nat.cast_one]

theorem fejerPairTerm_nonneg (z : ℂ) (D p q : ℕ) :
    0 ≤ fejerPairTerm z D p q := by
  unfold fejerPairTerm
  positivity

theorem ofReal_norm_sq_eq_mul_conj (w : ℂ) :
    ((‖w‖ ^ 2 : ℝ) : ℂ) = w * starRingEnd ℂ w := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem star_sum_powers (w : ℂ) (D : ℕ) :
    starRingEnd ℂ (∑ r ∈ Finset.range (D + 1), w ^ r) =
      ∑ r ∈ Finset.range (D + 1), starRingEnd ℂ (w ^ r) := by
  simp [map_sum]

theorem ofReal_fejerPairTerm_eq_mul_conj (z : ℂ) (D p q : ℕ) :
    ((fejerPairTerm z D p q : ℝ) : ℂ) =
      ((D + 1 : ℝ)⁻¹ : ℂ) *
        ((∑ r ∈ Finset.range (D + 1), (z ^ p * starRingEnd ℂ (z ^ q)) ^ r) *
          starRingEnd ℂ (∑ r ∈ Finset.range (D + 1),
            (z ^ p * starRingEnd ℂ (z ^ q)) ^ r)) := by
  unfold fejerPairTerm
  rw [Complex.ofReal_mul, Complex.ofReal_inv]
  congr 1
  rw [ofReal_norm_sq_eq_mul_conj]

theorem ofReal_fejerPairTerm_eq_double_sum (z : ℂ) (D p q : ℕ) :
    ((fejerPairTerm z D p q : ℝ) : ℂ) =
      ((D + 1 : ℝ)⁻¹ : ℂ) *
        ∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
          (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
            starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s) := by
  rw [ofReal_fejerPairTerm_eq_mul_conj]
  let w : ℂ := z ^ p * starRingEnd ℂ (z ^ q)
  have hmul :
      (∑ r ∈ Finset.range (D + 1), w ^ r) *
          (∑ s ∈ Finset.range (D + 1), starRingEnd ℂ (w ^ s)) =
        ∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
          w ^ r * starRingEnd ℂ (w ^ s) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro r hr
    rw [Finset.mul_sum]
  change ((D + 1 : ℝ)⁻¹ : ℂ) *
      ((∑ r ∈ Finset.range (D + 1), w ^ r) *
        starRingEnd ℂ (∑ r ∈ Finset.range (D + 1), w ^ r)) =
    ((D + 1 : ℝ)⁻¹ : ℂ) *
      ∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
        w ^ r * starRingEnd ℂ (w ^ s)
  rw [star_sum_powers, hmul]

theorem pow_mul_conj_pow_eq_pow_sub_of_le {z : ℂ} (hz : ‖z‖ = 1)
    {s r : ℕ} (h : s ≤ r) :
    z ^ r * starRingEnd ℂ (z ^ s) = z ^ (r - s) := by
  conv_lhs =>
    rw [← Nat.sub_add_cancel h]
    rw [pow_add]
  calc
    z ^ (r - s) * z ^ s * starRingEnd ℂ (z ^ s)
        = z ^ (r - s) * (z ^ s * starRingEnd ℂ (z ^ s)) := by ring
    _ = z ^ (r - s) := by
          rw [fejerPair_diag_base_one hz s]
          ring

theorem pow_mul_conj_pow_eq_conj_pow_sub_of_le {z : ℂ} (hz : ‖z‖ = 1)
    {r s : ℕ} (h : r ≤ s) :
    z ^ r * starRingEnd ℂ (z ^ s) = starRingEnd ℂ (z ^ (s - r)) := by
  conv_lhs =>
    rw [← Nat.sub_add_cancel h]
    rw [pow_add]
    rw [map_mul]
  calc
    z ^ r * (starRingEnd ℂ (z ^ (s - r)) * starRingEnd ℂ (z ^ r))
        = starRingEnd ℂ (z ^ (s - r)) * (z ^ r * starRingEnd ℂ (z ^ r)) := by ring
    _ = starRingEnd ℂ (z ^ (s - r)) := by
          rw [fejerPair_diag_base_one hz r]
          ring

theorem geomPowerSum_base_sub_of_le {z : ℂ} (hz : ‖z‖ = 1)
    (k : ℕ) {s r : ℕ} (h : s ≤ r) :
    (∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p) =
      geomPowerSum z k (r - s) := by
  unfold geomPowerSum
  rw [pow_mul_conj_pow_eq_pow_sub_of_le hz h]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [← pow_mul]
  ring_nf

theorem norm_geomPowerSum_base_sub_of_le {z : ℂ} (hz : ‖z‖ = 1)
    (k : ℕ) {s r : ℕ} (h : s ≤ r) :
    ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ =
      ‖geomPowerSum z k (r - s)‖ := by
  rw [geomPowerSum_base_sub_of_le hz k h]

theorem geomPowerSum_base_conj_sub_of_le {z : ℂ} (hz : ‖z‖ = 1)
    (k : ℕ) {r s : ℕ} (h : r ≤ s) :
    (∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p) =
      starRingEnd ℂ (geomPowerSum z k (s - r)) := by
  unfold geomPowerSum
  rw [pow_mul_conj_pow_eq_conj_pow_sub_of_le hz h]
  simp_rw [map_sum, map_pow]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [← pow_mul]
  ring_nf

theorem norm_geomPowerSum_base_conj_sub_of_le {z : ℂ} (hz : ‖z‖ = 1)
    (k : ℕ) {r s : ℕ} (h : r ≤ s) :
    ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ =
      ‖geomPowerSum z k (s - r)‖ := by
  rw [geomPowerSum_base_conj_sub_of_le hz k h]
  rw [Complex.norm_conj]

theorem fejer_cross_term_reindex (z : ℂ) (p q r s : ℕ) :
    (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
        starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s) =
      (z ^ r * starRingEnd ℂ (z ^ s)) ^ p *
        starRingEnd ℂ ((z ^ r * starRingEnd ℂ (z ^ s)) ^ q) := by
  simp [map_mul, map_pow]
  ring

theorem fejer_pq_sum_eq_norm_sq (z : ℂ) (k r s : ℕ) :
    (∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k,
      (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
        starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s)) =
      ((‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2 : ℝ) : ℂ) := by
  rw [ofReal_norm_sq_eq_mul_conj]
  simp_rw [map_sum]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro q hq
  rw [fejer_cross_term_reindex]

theorem fejerPairEnergy_eq_average_fejerBaseNormSum (z : ℂ) (k D : ℕ) :
    fejerPairEnergy z k D =
      (D + 1 : ℝ)⁻¹ *
        (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
          ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2) := by
  apply Complex.ofReal_injective
  calc
    ((fejerPairEnergy z k D : ℝ) : ℂ)
        = ∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k,
            ((fejerPairTerm z D p q : ℝ) : ℂ) := by
          unfold fejerPairEnergy
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [Complex.ofReal_sum]
    _ = ∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k,
          ((D + 1 : ℝ)⁻¹ : ℂ) *
            ∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
              (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
                starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          refine Finset.sum_congr rfl ?_
          intro q hq
          rw [ofReal_fejerPairTerm_eq_double_sum]
    _ = ((D + 1 : ℝ)⁻¹ : ℂ) *
          (∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k,
            ∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
              (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
                starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [Finset.mul_sum]
    _ = ((D + 1 : ℝ)⁻¹ : ℂ) *
          (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
            ∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k,
              (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
                starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s)) := by
          congr 1
          calc
            (∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k,
              ∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
                (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
                  starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s))
                = ∑ p ∈ Finset.range k, ∑ r ∈ Finset.range (D + 1),
                    ∑ q ∈ Finset.range k, ∑ s ∈ Finset.range (D + 1),
                      (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
                        starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s) := by
                  refine Finset.sum_congr rfl ?_
                  intro p hp
                  rw [Finset.sum_comm]
            _ = ∑ p ∈ Finset.range k, ∑ r ∈ Finset.range (D + 1),
                  ∑ s ∈ Finset.range (D + 1), ∑ q ∈ Finset.range k,
                    (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
                      starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s) := by
                  refine Finset.sum_congr rfl ?_
                  intro p hp
                  refine Finset.sum_congr rfl ?_
                  intro r hr
                  rw [Finset.sum_comm]
            _ = ∑ r ∈ Finset.range (D + 1), ∑ p ∈ Finset.range k,
                  ∑ s ∈ Finset.range (D + 1), ∑ q ∈ Finset.range k,
                    (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
                      starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s) := by
                  rw [Finset.sum_comm]
            _ = ∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
                  ∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k,
                    (z ^ p * starRingEnd ℂ (z ^ q)) ^ r *
                      starRingEnd ℂ ((z ^ p * starRingEnd ℂ (z ^ q)) ^ s) := by
                  refine Finset.sum_congr rfl ?_
                  intro r hr
                  rw [Finset.sum_comm]
    _ = ((D + 1 : ℝ)⁻¹ : ℂ) *
          (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
            ((‖∑ p ∈ Finset.range k,
              (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2 : ℝ) : ℂ)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro r hr
          refine Finset.sum_congr rfl ?_
          intro s hs
          rw [fejer_pq_sum_eq_norm_sq]
    _ = (((D + 1 : ℝ)⁻¹ *
          (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1),
            ‖∑ p ∈ Finset.range k,
              (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2) : ℝ) : ℂ) := by
          rw [Complex.ofReal_mul, Complex.ofReal_inv]
          congr 1
          rw [Complex.ofReal_sum]
          refine Finset.sum_congr rfl ?_
          intro r hr
          rw [Complex.ofReal_sum]

theorem sum_Ico_one_succ_eq_sum_range_succ (F : ℕ → ℝ) (D : ℕ) :
    (∑ d ∈ Finset.Ico 1 (D + 1), F d) =
      ∑ i ∈ Finset.range D, F (i + 1) := by
  simpa [Nat.Ico_zero_eq_range] using
    (Finset.sum_Ico_add' F 0 D 1).symm

theorem square_sum_eq_lower_diag_upper (F : ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ r ∈ Finset.range n, ∑ s ∈ Finset.range n, F r s) =
      (∑ r ∈ Finset.range n, ∑ s ∈ Finset.range r, F r s)
        + (∑ r ∈ Finset.range n, F r r)
        + (∑ s ∈ Finset.range n, ∑ r ∈ Finset.range s, F r s) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [Finset.sum_range_succ, ih, Finset.sum_add_distrib]
      ring

theorem sum_Ico_one_succ_le_sum_range_succ
    (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) {r D : ℕ} (hr : r ≤ D) :
    (∑ d ∈ Finset.Ico 1 (r + 1), F d) ≤
      ∑ i ∈ Finset.range D, F (i + 1) := by
  calc
    (∑ d ∈ Finset.Ico 1 (r + 1), F d)
        ≤ ∑ d ∈ Finset.Ico 1 (D + 1), F d := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro d hd
            simp only [Finset.mem_Ico] at hd ⊢
            omega
          · intro d hdD hnot
            exact hF d
    _ = ∑ i ∈ Finset.range D, F (i + 1) := by
          rw [sum_Ico_one_succ_eq_sum_range_succ]

theorem lowerTriangle_row_sum_le_sum_range_succ
    (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) {r D : ℕ} (hr : r ≤ D) :
    (∑ s ∈ Finset.range r, F (r - s)) ≤
      ∑ i ∈ Finset.range D, F (i + 1) := by
  have hreflect :
      (∑ s ∈ Finset.range r, F (r - s)) =
        ∑ d ∈ Finset.Ico 1 (r + 1), F d := by
    simpa [Nat.Ico_zero_eq_range] using
      (Finset.sum_Ico_reflect F 0 (m := r) (n := r) (by omega))
  rw [hreflect]
  exact sum_Ico_one_succ_le_sum_range_succ F hF hr

theorem lowerTriangle_sum_le_mul_sum_range_succ
    (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) (D : ℕ) :
    (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range r, F (r - s)) ≤
      (D + 1 : ℝ) * (∑ i ∈ Finset.range D, F (i + 1)) := by
  calc
    (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range r, F (r - s))
        ≤ ∑ _r ∈ Finset.range (D + 1),
            (∑ i ∈ Finset.range D, F (i + 1)) := by
          refine Finset.sum_le_sum ?_
          intro r hr
          exact lowerTriangle_row_sum_le_sum_range_succ F hF (by
            simp only [Finset.mem_range] at hr
            omega)
    _ = (D + 1 : ℝ) * (∑ i ∈ Finset.range D, F (i + 1)) := by
          simp [Finset.sum_const, nsmul_eq_mul]

theorem lowerTriangle_geomPowerEnergy_le_mul
    (z : ℂ) (k D : ℕ) :
    (∑ r ∈ Finset.range (D + 1),
        ∑ s ∈ Finset.range r, ‖geomPowerSum z k (r - s)‖ ^ 2)
      ≤ (D + 1 : ℝ) * geomPowerEnergy z k D := by
  simpa [geomPowerEnergy] using
    lowerTriangle_sum_le_mul_sum_range_succ
      (fun d => ‖geomPowerSum z k d‖ ^ 2)
      (fun d => sq_nonneg ‖geomPowerSum z k d‖) D

theorem lowerTriangle_fejerBaseNorm_le_mul
    {z : ℂ} (hz : ‖z‖ = 1) (k D : ℕ) :
    (∑ r ∈ Finset.range (D + 1),
        ∑ s ∈ Finset.range r,
          ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2)
      ≤ (D + 1 : ℝ) * geomPowerEnergy z k D := by
  calc
    (∑ r ∈ Finset.range (D + 1),
        ∑ s ∈ Finset.range r,
          ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2)
        = ∑ r ∈ Finset.range (D + 1),
            ∑ s ∈ Finset.range r, ‖geomPowerSum z k (r - s)‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          refine Finset.sum_congr rfl ?_
          intro s hs
          have hsr : s ≤ r := by
            simp only [Finset.mem_range] at hs
            omega
          rw [norm_geomPowerSum_base_sub_of_le hz k hsr]
    _ ≤ (D + 1 : ℝ) * geomPowerEnergy z k D :=
          lowerTriangle_geomPowerEnergy_le_mul z k D

theorem upperTriangle_fejerBaseNorm_le_mul
    {z : ℂ} (hz : ‖z‖ = 1) (k D : ℕ) :
    (∑ s ∈ Finset.range (D + 1),
        ∑ r ∈ Finset.range s,
          ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2)
      ≤ (D + 1 : ℝ) * geomPowerEnergy z k D := by
  calc
    (∑ s ∈ Finset.range (D + 1),
        ∑ r ∈ Finset.range s,
          ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2)
        = ∑ s ∈ Finset.range (D + 1),
            ∑ r ∈ Finset.range s, ‖geomPowerSum z k (s - r)‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          refine Finset.sum_congr rfl ?_
          intro r hr
          have hrs : r ≤ s := by
            simp only [Finset.mem_range] at hr
            omega
          rw [norm_geomPowerSum_base_conj_sub_of_le hz k hrs]
    _ ≤ (D + 1 : ℝ) * geomPowerEnergy z k D :=
          lowerTriangle_geomPowerEnergy_le_mul z k D

theorem fejerBase_diag_norm_sq {z : ℂ} (hz : ‖z‖ = 1) (k r : ℕ) :
    ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ r)) ^ p‖ ^ 2 =
      (k : ℝ) ^ 2 := by
  rw [fejerPair_diag_base_one hz r]
  simp

theorem diagonal_fejerBaseNorm_sum {z : ℂ} (hz : ‖z‖ = 1) (k D : ℕ) :
    (∑ r ∈ Finset.range (D + 1),
        ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ r)) ^ p‖ ^ 2)
      = (D + 1 : ℝ) * (k : ℝ) ^ 2 := by
  calc
    (∑ r ∈ Finset.range (D + 1),
        ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ r)) ^ p‖ ^ 2)
        = ∑ _r ∈ Finset.range (D + 1), (k : ℝ) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          exact fejerBase_diag_norm_sq hz k r
    _ = (D + 1 : ℝ) * (k : ℝ) ^ 2 := by
          simp [Finset.sum_const, nsmul_eq_mul]

theorem fejerPairEnergy_le_sq_add_two_energy
    {z : ℂ} (hz : ‖z‖ = 1) (k D : ℕ) :
    fejerPairEnergy z k D ≤ (k : ℝ) ^ 2 + 2 * geomPowerEnergy z k D := by
  let B : ℕ → ℕ → ℝ := fun r s =>
    ‖∑ p ∈ Finset.range k, (z ^ r * starRingEnd ℂ (z ^ s)) ^ p‖ ^ 2
  let S : ℝ := ∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range (D + 1), B r s
  have hsplit :
      S =
        (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range r, B r s)
          + (∑ r ∈ Finset.range (D + 1), B r r)
          + (∑ s ∈ Finset.range (D + 1), ∑ r ∈ Finset.range s, B r s) := by
    simpa [S, B] using square_sum_eq_lower_diag_upper B (D + 1)
  have hlower :
      (∑ r ∈ Finset.range (D + 1), ∑ s ∈ Finset.range r, B r s)
        ≤ (D + 1 : ℝ) * geomPowerEnergy z k D := by
    simpa [B] using lowerTriangle_fejerBaseNorm_le_mul hz k D
  have hupper :
      (∑ s ∈ Finset.range (D + 1), ∑ r ∈ Finset.range s, B r s)
        ≤ (D + 1 : ℝ) * geomPowerEnergy z k D := by
    simpa [B] using upperTriangle_fejerBaseNorm_le_mul hz k D
  have hdiag :
      (∑ r ∈ Finset.range (D + 1), B r r) =
        (D + 1 : ℝ) * (k : ℝ) ^ 2 := by
    simpa [B] using diagonal_fejerBaseNorm_sum hz k D
  have hSle :
      S ≤ (D + 1 : ℝ) * (k : ℝ) ^ 2
          + (D + 1 : ℝ) * geomPowerEnergy z k D
          + (D + 1 : ℝ) * geomPowerEnergy z k D := by
    rw [hsplit, hdiag]
    nlinarith
  rw [fejerPairEnergy_eq_average_fejerBaseNormSum]
  change (D + 1 : ℝ)⁻¹ * S ≤ (k : ℝ) ^ 2 + 2 * geomPowerEnergy z k D
  calc
    (D + 1 : ℝ)⁻¹ * S
        ≤ (D + 1 : ℝ)⁻¹ *
            ((D + 1 : ℝ) * (k : ℝ) ^ 2
              + (D + 1 : ℝ) * geomPowerEnergy z k D
              + (D + 1 : ℝ) * geomPowerEnergy z k D) := by
          exact mul_le_mul_of_nonneg_left hSle (by positivity)
    _ = (k : ℝ) ^ 2 + 2 * geomPowerEnergy z k D := by
          have hpos : (0 : ℝ) < D + 1 := by positivity
          field_simp [ne_of_gt hpos]
          ring

theorem fejerPairEnergy_diag_lower {z : ℂ} (hz : ‖z‖ = 1) (k D : ℕ) :
    (k : ℝ) * (D + 1 : ℝ) ≤ fejerPairEnergy z k D := by
  unfold fejerPairEnergy
  calc
    (k : ℝ) * (D + 1 : ℝ)
        = ∑ p ∈ Finset.range k, (D + 1 : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring
    _ ≤ ∑ p ∈ Finset.range k, ∑ q ∈ Finset.range k, fejerPairTerm z D p q := by
          refine Finset.sum_le_sum ?_
          intro p hp
          rw [← fejerPair_diag_term hz p D]
          exact Finset.single_le_sum (fun q hq => fejerPairTerm_nonneg z D p q) hp

/--
The remaining scalar power-sum claim behind the report's Fejér lower bound.

For `D = 2*k`, this says `geomPowerEnergy z k (2*k) >= k*(k+1)/2` for every
unit complex number `z`.
-/
def casselsGeomLowerClaim (k D : ℕ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → casselsRhs k D ≤ geomPowerEnergy z k D

theorem casselsGeomLowerClaim_true (k D : ℕ) :
    casselsGeomLowerClaim k D := by
  intro z hz
  have hlo := fejerPairEnergy_diag_lower (z := z) hz k D
  have hhi := fejerPairEnergy_le_sq_add_two_energy (z := z) hz k D
  unfold casselsRhs
  nlinarith

/--
For a character, the cyclic AP sum factors into the starting phase times a power sum.
This is the Fourier-side form of the AP sum.
-/
theorem zmodAPSum_addChar_factor
    (ψ : AddChar (ZMod N) ℂ) (k : ℕ) (a d : ZMod N) :
    zmodAPSum (fun x => ψ x) k a d =
      ψ a * ∑ j ∈ Finset.range k, ψ (j • d) := by
  unfold zmodAPSum
  calc
    (∑ j ∈ Finset.range k, ψ (a + j • d))
        = ∑ j ∈ Finset.range k, ψ a * ψ (j • d) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [AddChar.map_add_eq_mul]
    _ = ψ a * ∑ j ∈ Finset.range k, ψ (j • d) := by
          rw [Finset.mul_sum]

/-- The character power sum can be written using powers of the single phase `ψ d`. -/
theorem addChar_power_sum_eq
    (ψ : AddChar (ZMod N) ℂ) (k : ℕ) (d : ZMod N) :
    (∑ j ∈ Finset.range k, ψ (j • d)) =
      ∑ j ∈ Finset.range k, (ψ d) ^ j := by
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [AddChar.map_nsmul_eq_pow]

theorem addChar_zmod_power_sum_eq
    (ψ : AddChar (ZMod N) ℂ) (k d : ℕ) :
    (∑ j ∈ Finset.range k, ψ (j • (d : ZMod N))) =
      geomPowerSum (ψ (1 : ZMod N)) k d := by
  unfold geomPowerSum
  refine Finset.sum_congr rfl ?_
  intro j hj
  calc
    ψ (j • (d : ZMod N)) = ψ (((j * d : ℕ) : ZMod N)) := by
      congr 1
      simp [nsmul_eq_mul, Nat.cast_mul, mul_comm]
    _ = ψ ((j * d) • (1 : ZMod N)) := by
      simp
    _ = (ψ (1 : ZMod N)) ^ (j * d) := by
      rw [AddChar.map_nsmul_eq_pow]

theorem addChar_power_energy_eq
    (ψ : AddChar (ZMod N) ℂ) (k D : ℕ) :
    (∑ i ∈ Finset.range D,
        ‖∑ j ∈ Finset.range k, ψ (j • ((i + 1 : ℕ) : ZMod N))‖ ^ 2)
      = geomPowerEnergy (ψ (1 : ZMod N)) k D := by
  unfold geomPowerEnergy
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [addChar_zmod_power_sum_eq]

variable [NeZero N]

/-- Fourier coefficient with respect to Mathlib's character basis on `ZMod N`. -/
noncomputable def fourierCoeff
    (f : ZMod N → ℂ) (ψ : AddChar (ZMod N) ℂ) : ℂ :=
  (AddChar.complexBasis (ZMod N)).repr f ψ

/-- Pointwise expansion of a function in the character basis. -/
theorem fourier_expansion
    (f : ZMod N → ℂ) (x : ZMod N) :
    f x = ∑ ψ : AddChar (ZMod N) ℂ, fourierCoeff f ψ * ψ x := by
  have h := congrFun ((AddChar.complexBasis (ZMod N)).sum_repr f) x
  simpa [fourierCoeff, AddChar.complexBasis_apply] using h.symm

/-- The character expansion may be passed through a cyclic AP sum. -/
theorem zmodAPSum_fourier_expansion
    (f : ZMod N → ℂ) (k : ℕ) (a d : ZMod N) :
    zmodAPSum f k a d =
      ∑ ψ : AddChar (ZMod N) ℂ,
        fourierCoeff f ψ * zmodAPSum (fun x => ψ x) k a d := by
  unfold zmodAPSum
  calc
    (∑ j ∈ Finset.range k, f (a + j • d))
        = ∑ j ∈ Finset.range k,
            ∑ ψ : AddChar (ZMod N) ℂ,
              fourierCoeff f ψ * ψ (a + j • d) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact fourier_expansion f (a + j • d)
    _ = ∑ ψ : AddChar (ZMod N) ℂ,
        fourierCoeff f ψ * ∑ j ∈ Finset.range k, ψ (a + j • d) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro ψ hψ
          rw [Finset.mul_sum]

/-- Orthogonality of characters, unfolded as a normalized finite sum. -/
theorem addChar_expect_mul_conj_eq_boole
    (ψ χ : AddChar (ZMod N) ℂ) :
    (Finset.univ.expect fun a : ZMod N => ψ a * starRingEnd ℂ (χ a))
      = if χ = ψ then 1 else 0 := by
  have h := AddChar.wInner_cWeight_eq_boole χ ψ
  rw [RCLike.wInner_cWeight_eq_expect] at h
  simpa [RCLike.inner_apply] using h

/-- A finite linear combination of characters. -/
noncomputable def charCombination
    (c : AddChar (ZMod N) ℂ → ℂ) (a : ZMod N) : ℂ :=
  ∑ ψ : AddChar (ZMod N) ℂ, c ψ * ψ a

/--
Normalized Parseval for finite character combinations.

This is the algebraic core needed to pass from a general coloring to its character
components in the Fejér lower-bound argument.
-/
theorem expect_charCombination_mul_conj
    (c b : AddChar (ZMod N) ℂ → ℂ) :
    (Finset.univ.expect fun a : ZMod N =>
        charCombination c a * starRingEnd ℂ (charCombination b a))
      = ∑ ψ : AddChar (ZMod N) ℂ, c ψ * starRingEnd ℂ (b ψ) := by
  classical
  unfold charCombination
  simp_rw [map_sum, map_mul]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  refine Finset.sum_congr rfl ?_
  intro ψ hψ
  rw [Finset.expect_sum_comm]
  calc
    (∑ χ : AddChar (ZMod N) ℂ,
        Finset.univ.expect fun a : ZMod N =>
          c ψ * ψ a * (starRingEnd ℂ (b χ) * starRingEnd ℂ (χ a)))
        = ∑ χ : AddChar (ZMod N) ℂ,
            c ψ * starRingEnd ℂ (b χ) *
              (Finset.univ.expect fun a : ZMod N => ψ a * starRingEnd ℂ (χ a)) := by
          refine Finset.sum_congr rfl ?_
          intro χ hχ
          calc
            (Finset.univ.expect fun a : ZMod N =>
                c ψ * ψ a * (starRingEnd ℂ (b χ) * starRingEnd ℂ (χ a)))
                = Finset.univ.expect fun a : ZMod N =>
                    (c ψ * starRingEnd ℂ (b χ)) * (ψ a * starRingEnd ℂ (χ a)) := by
                    refine Finset.expect_congr rfl ?_
                    intro a ha
                    ring
            _ = c ψ * starRingEnd ℂ (b χ) *
                  (Finset.univ.expect fun a : ZMod N => ψ a * starRingEnd ℂ (χ a)) := by
                    rw [← Finset.mul_expect]
    _ = c ψ * starRingEnd ℂ (b ψ) := by
          simp_rw [addChar_expect_mul_conj_eq_boole]
          simp

/-- The Fourier expansion restated using `charCombination`. -/
theorem charCombination_fourierCoeff
    (f : ZMod N → ℂ) (a : ZMod N) :
    charCombination (fourierCoeff f) a = f a := by
  simpa [charCombination] using (fourier_expansion f a).symm

/-- The Fourier coefficient of the AP-sum function for a fixed difference. -/
noncomputable def apFourierCoeff
    (f : ZMod N → ℂ) (k : ℕ) (d : ZMod N)
    (ψ : AddChar (ZMod N) ℂ) : ℂ :=
  fourierCoeff f ψ * ∑ j ∈ Finset.range k, ψ (j • d)

/--
For fixed `d`, the AP-sum function is a character combination with coefficients
`apFourierCoeff`.
-/
theorem zmodAPSum_eq_charCombination
    (f : ZMod N → ℂ) (k : ℕ) (a d : ZMod N) :
    zmodAPSum f k a d = charCombination (apFourierCoeff f k d) a := by
  rw [zmodAPSum_fourier_expansion]
  unfold charCombination apFourierCoeff
  refine Finset.sum_congr rfl ?_
  intro ψ hψ
  rw [zmodAPSum_addChar_factor]
  ring

/-- Parseval applied to the AP-sum function for a fixed difference. -/
theorem expect_zmodAPSum_mul_conj
    (f g : ZMod N → ℂ) (k : ℕ) (d : ZMod N) :
    (Finset.univ.expect fun a : ZMod N =>
        zmodAPSum f k a d * starRingEnd ℂ (zmodAPSum g k a d))
      = ∑ ψ : AddChar (ZMod N) ℂ,
          apFourierCoeff f k d ψ * starRingEnd ℂ (apFourierCoeff g k d ψ) := by
  simp_rw [zmodAPSum_eq_charCombination]
  exact expect_charCombination_mul_conj (apFourierCoeff f k d) (apFourierCoeff g k d)

/-- Real-valued normalized Parseval for finite character combinations. -/
theorem expect_normSq_charCombination
    (c : AddChar (ZMod N) ℂ → ℂ) :
    (Finset.univ.expect fun a : ZMod N => ‖charCombination c a‖ ^ 2)
      = ∑ ψ : AddChar (ZMod N) ℂ, ‖c ψ‖ ^ 2 := by
  apply Complex.ofReal_injective
  calc
    ((Finset.univ.expect fun a : ZMod N => ‖charCombination c a‖ ^ 2 : ℝ) : ℂ)
        = Finset.univ.expect fun a : ZMod N =>
            ((‖charCombination c a‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.ofReal_expect]
    _ = Finset.univ.expect fun a : ZMod N =>
          charCombination c a * starRingEnd ℂ (charCombination c a) := by
          refine Finset.expect_congr rfl ?_
          intro a ha
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    _ = ∑ ψ : AddChar (ZMod N) ℂ, c ψ * starRingEnd ℂ (c ψ) := by
          rw [expect_charCombination_mul_conj]
    _ = ∑ ψ : AddChar (ZMod N) ℂ, ((‖c ψ‖ ^ 2 : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro ψ hψ
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    _ = ((∑ ψ : AddChar (ZMod N) ℂ, ‖c ψ‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum]

/-- Real-valued normalized Parseval for the AP-sum function at a fixed difference. -/
theorem expect_normSq_zmodAPSum
    (f : ZMod N → ℂ) (k : ℕ) (d : ZMod N) :
    (Finset.univ.expect fun a : ZMod N => ‖zmodAPSum f k a d‖ ^ 2)
      = ∑ ψ : AddChar (ZMod N) ℂ, ‖apFourierCoeff f k d ψ‖ ^ 2 := by
  simp_rw [zmodAPSum_eq_charCombination]
  exact expect_normSq_charCombination (apFourierCoeff f k d)

/-- The AP Fourier coefficient norm factors into the coloring coefficient and the kernel. -/
theorem normSq_apFourierCoeff
    (f : ZMod N → ℂ) (k : ℕ) (d : ZMod N)
    (ψ : AddChar (ZMod N) ℂ) :
    ‖apFourierCoeff f k d ψ‖ ^ 2 =
      ‖fourierCoeff f ψ‖ ^ 2 * ‖∑ j ∈ Finset.range k, ψ (j • d)‖ ^ 2 := by
  unfold apFourierCoeff
  rw [norm_mul]
  ring

/--
The full Fourier-side decomposition of the AP second moment over `d = 1, ..., D`.
The only remaining lower-bound input is now `geomPowerEnergy`.
-/
theorem sum_expect_normSq_zmodAPSum
    (f : ZMod N → ℂ) (k D : ℕ) :
    (∑ i ∈ Finset.range D,
        Finset.univ.expect fun a : ZMod N =>
          ‖zmodAPSum f k a ((i + 1 : ℕ) : ZMod N)‖ ^ 2)
      = ∑ ψ : AddChar (ZMod N) ℂ,
          ‖fourierCoeff f ψ‖ ^ 2 * geomPowerEnergy (ψ (1 : ZMod N)) k D := by
  calc
    (∑ i ∈ Finset.range D,
        Finset.univ.expect fun a : ZMod N =>
          ‖zmodAPSum f k a ((i + 1 : ℕ) : ZMod N)‖ ^ 2)
        = ∑ i ∈ Finset.range D,
            ∑ ψ : AddChar (ZMod N) ℂ,
              ‖apFourierCoeff f k ((i + 1 : ℕ) : ZMod N) ψ‖ ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [expect_normSq_zmodAPSum]
    _ = ∑ i ∈ Finset.range D,
          ∑ ψ : AddChar (ZMod N) ℂ,
            ‖fourierCoeff f ψ‖ ^ 2 *
              ‖∑ j ∈ Finset.range k, ψ (j • ((i + 1 : ℕ) : ZMod N))‖ ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro ψ hψ
            rw [normSq_apFourierCoeff]
    _ = ∑ ψ : AddChar (ZMod N) ℂ,
          ∑ i ∈ Finset.range D,
            ‖fourierCoeff f ψ‖ ^ 2 *
              ‖∑ j ∈ Finset.range k, ψ (j • ((i + 1 : ℕ) : ZMod N))‖ ^ 2 := by
            rw [Finset.sum_comm]
    _ = ∑ ψ : AddChar (ZMod N) ℂ,
          ‖fourierCoeff f ψ‖ ^ 2 * geomPowerEnergy (ψ (1 : ZMod N)) k D := by
            refine Finset.sum_congr rfl ?_
            intro ψ hψ
            rw [← Finset.mul_sum]
            rw [addChar_power_energy_eq]

/-- For unit-valued functions, the squared norms of the Fourier coefficients sum to `1`. -/
theorem sum_normSq_fourierCoeff_of_unit
    (f : ZMod N → ℂ)
    (hunit : ∀ a : ZMod N, ‖f a‖ = 1) :
    (∑ ψ : AddChar (ZMod N) ℂ, ‖fourierCoeff f ψ‖ ^ 2) = 1 := by
  have h := expect_normSq_charCombination (fourierCoeff f)
  simp_rw [charCombination_fourierCoeff] at h
  rw [← h]
  simp [hunit]

/--
Conditional Fejér lower bound.

Everything in the Fourier/Parseval reduction is now verified in Lean: once the scalar
power-sum claim `casselsGeomLowerClaim` is proved, the reported Fejér lower bound follows.
-/
theorem sum_expect_normSq_zmodAPSum_lower_of_cassels
    (f : ZMod N → ℂ) (k D : ℕ)
    (hCassels : casselsGeomLowerClaim k D)
    (hunit : ∀ a : ZMod N, ‖f a‖ = 1) :
    casselsRhs k D ≤
      ∑ i ∈ Finset.range D,
        Finset.univ.expect fun a : ZMod N =>
          ‖zmodAPSum f k a ((i + 1 : ℕ) : ZMod N)‖ ^ 2 := by
  rw [sum_expect_normSq_zmodAPSum]
  have hcoeff := sum_normSq_fourierCoeff_of_unit f hunit
  calc
    casselsRhs k D = (1 : ℝ) * casselsRhs k D := by ring
    _ = (∑ ψ : AddChar (ZMod N) ℂ, ‖fourierCoeff f ψ‖ ^ 2) * casselsRhs k D := by
          rw [hcoeff]
    _ = ∑ ψ : AddChar (ZMod N) ℂ, ‖fourierCoeff f ψ‖ ^ 2 * casselsRhs k D := by
          rw [Finset.sum_mul]
    _ ≤ ∑ ψ : AddChar (ZMod N) ℂ,
          ‖fourierCoeff f ψ‖ ^ 2 * geomPowerEnergy (ψ (1 : ZMod N)) k D := by
          refine Finset.sum_le_sum ?_
          intro ψ hψ
          exact mul_le_mul_of_nonneg_left
            (hCassels (ψ (1 : ZMod N)) (AddChar.norm_apply ψ (1 : ZMod N)))
            (sq_nonneg ‖fourierCoeff f ψ‖)

theorem sum_expect_normSq_zmodAPSum_lower
    (f : ZMod N → ℂ) (k D : ℕ)
    (hunit : ∀ a : ZMod N, ‖f a‖ = 1) :
    casselsRhs k D ≤
      ∑ i ∈ Finset.range D,
        Finset.univ.expect fun a : ZMod N =>
          ‖zmodAPSum f k a ((i + 1 : ℕ) : ZMod N)‖ ^ 2 :=
  sum_expect_normSq_zmodAPSum_lower_of_cassels
    (N := N) f k D (casselsGeomLowerClaim_true k D) hunit

theorem casselsRhs_two_mul (k : ℕ) :
    casselsRhs k (2 * k) = ((k : ℝ) * (k + 1 : ℝ)) / 2 := by
  unfold casselsRhs
  norm_num [Nat.cast_mul]
  ring

/--
The exact lower-bound shape used in the HTML report, conditional on the scalar
Cassels/Turán power-sum inequality.
-/
theorem average_normSq_zmodAPSum_lower_dTwoK_of_cassels
    (f : ZMod N → ℂ) {k : ℕ}
    (hk : 0 < k)
    (hCassels : casselsGeomLowerClaim k (2 * k))
    (hunit : ∀ a : ZMod N, ‖f a‖ = 1) :
    ((k : ℝ) + 1) / 4 ≤
      ((2 * k : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (2 * k),
          Finset.univ.expect fun a : ZMod N =>
            ‖zmodAPSum f k a ((i + 1 : ℕ) : ZMod N)‖ ^ 2) := by
  have hsum := sum_expect_normSq_zmodAPSum_lower_of_cassels
    (N := N) f k (2 * k) hCassels hunit
  rw [casselsRhs_two_mul] at hsum
  have hpos : 0 < (2 * k : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hpos.le)
  have heq :
      (2 * k : ℝ)⁻¹ * (((k : ℝ) * (k + 1 : ℝ)) / 2) =
        ((k : ℝ) + 1) / 4 := by
    field_simp [ne_of_gt hpos]
    ring
  rw [← heq]
  exact hmul

theorem average_normSq_zmodAPSum_lower_dTwoK
    (f : ZMod N → ℂ) {k : ℕ}
    (hk : 0 < k)
    (hunit : ∀ a : ZMod N, ‖f a‖ = 1) :
    ((k : ℝ) + 1) / 4 ≤
      ((2 * k : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (2 * k),
          Finset.univ.expect fun a : ZMod N =>
            ‖zmodAPSum f k a ((i + 1 : ℕ) : ZMod N)‖ ^ 2) :=
  average_normSq_zmodAPSum_lower_dTwoK_of_cassels
    (N := N) f hk (casselsGeomLowerClaim_true k (2 * k)) hunit

/-- The factorization also removes the starting point from the norm. -/
theorem norm_zmodAPSum_addChar
    (ψ : AddChar (ZMod N) ℂ) (k : ℕ) (a d : ZMod N) :
    ‖zmodAPSum (fun x => ψ x) k a d‖ =
      ‖∑ j ∈ Finset.range k, ψ (j • d)‖ := by
  rw [zmodAPSum_addChar_factor]
  rw [norm_mul, AddChar.norm_apply]
  simp

end FourierSetup

section FinZModBridge

variable {N : ℕ} [NeZero N]

/-- The canonical equivalence between residues represented as `Fin N` and `ZMod N`. -/
def finZModEquiv (N : ℕ) [NeZero N] : Fin N ≃ ZMod N where
  toFun a := (a.val : ZMod N)
  invFun x := ⟨x.val, x.val_lt⟩
  left_inv a := by
    apply Fin.ext
    simp [ZMod.val_natCast_of_lt a.isLt]
  right_inv x := by
    exact ZMod.natCast_zmod_val x

/-- Move an integer `±1` coloring on `Fin N` to a complex-valued coloring on `ZMod N`. -/
noncomputable def zmodColoringOfFin (f : Fin N → ℤ) (x : ZMod N) : ℂ :=
  ((f ((finZModEquiv N).symm x) : ℤ) : ℂ)

theorem zmodColoringOfFin_unit
    (f : Fin N → ℤ) (hpm : ∀ x, f x = -1 ∨ f x = 1) :
    ∀ x : ZMod N, ‖zmodColoringOfFin f x‖ = 1 := by
  intro x
  unfold zmodColoringOfFin
  rcases hpm ((finZModEquiv N).symm x) with h | h <;> simp [h]

theorem finZModEquiv_cyclicIndex (a : Fin N) (j d : ℕ) :
    finZModEquiv N (cyclicIndex a j d) =
      (finZModEquiv N a) + j • (d : ZMod N) := by
  apply ZMod.val_injective N
  simp [finZModEquiv, cyclicIndex, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul]

theorem zmodAPSum_zmodColoringOfFin
    (f : Fin N → ℤ) (k : ℕ) (a : Fin N) (d : ℕ) :
    zmodAPSum (zmodColoringOfFin f) k (finZModEquiv N a) (d : ZMod N) =
      ((cyclicAPSum f k a d : ℤ) : ℂ) := by
  unfold zmodAPSum cyclicAPSum zmodColoringOfFin
  change
    (∑ j ∈ Finset.range k,
      ((f ((finZModEquiv N).symm ((finZModEquiv N a) + j • (d : ZMod N))) : ℤ) : ℂ)) =
        (Int.castRingHom ℂ) (∑ j ∈ Finset.range k, f (cyclicIndex a j d))
  have hcast :
      (Int.castRingHom ℂ) (∑ j ∈ Finset.range k, f (cyclicIndex a j d)) =
        ∑ j ∈ Finset.range k, (Int.castRingHom ℂ) (f (cyclicIndex a j d)) :=
    map_sum (Int.castRingHom ℂ) (fun j => f (cyclicIndex a j d)) (Finset.range k)
  rw [hcast]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hidx := finZModEquiv_cyclicIndex (N := N) a j d
  rw [← hidx]
  simp

theorem normSq_intCast_complex (z : ℤ) :
    ‖((z : ℤ) : ℂ)‖ ^ 2 = ((z ^ 2 : ℤ) : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_intCast]
  norm_num [pow_two]

theorem expect_normSq_zmodAPSum_zmodColoringOfFin
    (f : Fin N → ℤ) (k d : ℕ) :
    (Finset.univ.expect fun x : ZMod N =>
        ‖zmodAPSum (zmodColoringOfFin f) k x (d : ZMod N)‖ ^ 2)
      =
    (Finset.univ.expect fun a : Fin N =>
        (((cyclicAPSum f k a d) ^ 2 : ℤ) : ℝ)) := by
  symm
  exact Fintype.expect_equiv (finZModEquiv N)
    (fun a : Fin N => (((cyclicAPSum f k a d) ^ 2 : ℤ) : ℝ))
    (fun x : ZMod N => ‖zmodAPSum (zmodColoringOfFin f) k x (d : ZMod N)‖ ^ 2)
    (by
      intro a
      rw [zmodAPSum_zmodColoringOfFin]
      exact (normSq_intCast_complex (cyclicAPSum f k a d)).symm)

theorem sum_expect_normSq_zmodAPSum_zmodColoringOfFin
    (f : Fin N → ℤ) (k D : ℕ) :
    (∑ i ∈ Finset.range D,
        Finset.univ.expect fun x : ZMod N =>
          ‖zmodAPSum (zmodColoringOfFin f) k x ((i + 1 : ℕ) : ZMod N)‖ ^ 2)
      =
    (∑ i ∈ Finset.range D,
        Finset.univ.expect fun a : Fin N =>
          (((cyclicAPSum f k a (i + 1)) ^ 2 : ℤ) : ℝ)) := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact expect_normSq_zmodAPSum_zmodColoringOfFin f k (i + 1)

theorem average_cyclicAPSum_lower_dTwoK
    (f : Fin N → ℤ)
    (hpm : ∀ x, f x = -1 ∨ f x = 1)
    {k : ℕ} (hk : 0 < k) :
    ((k : ℝ) + 1) / 4 ≤
      ((2 * k : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (2 * k),
          Finset.univ.expect fun a : Fin N =>
            (((cyclicAPSum f k a (i + 1)) ^ 2 : ℤ) : ℝ)) := by
  have hlo := average_normSq_zmodAPSum_lower_dTwoK
    (N := N) (zmodColoringOfFin f) hk (zmodColoringOfFin_unit f hpm)
  rw [sum_expect_normSq_zmodAPSum_zmodColoringOfFin] at hlo
  exact hlo

theorem sum_expect_cyclicAPSum_eq_inv_card_mul_sum
    (f : Fin N → ℤ) (k D : ℕ) :
    (∑ i ∈ Finset.range D,
        Finset.univ.expect fun a : Fin N =>
          (((cyclicAPSum f k a (i + 1)) ^ 2 : ℤ) : ℝ))
      =
    (N : ℝ)⁻¹ *
      (∑ i ∈ Finset.range D, ∑ a : Fin N,
        (((cyclicAPSum f k a (i + 1)) ^ 2 : ℤ) : ℝ)) := by
  calc
    (∑ i ∈ Finset.range D,
        Finset.univ.expect fun a : Fin N =>
          (((cyclicAPSum f k a (i + 1)) ^ 2 : ℤ) : ℝ))
        = ∑ i ∈ Finset.range D,
            ((∑ a : Fin N, (((cyclicAPSum f k a (i + 1)) ^ 2 : ℤ) : ℝ))
              / (N : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Fintype.expect_eq_sum_div_card]
          simp [Fintype.card_fin]
    _ = (N : ℝ)⁻¹ *
          (∑ i ∈ Finset.range D, ∑ a : Fin N,
            (((cyclicAPSum f k a (i + 1)) ^ 2 : ℤ) : ℝ)) := by
          simp only [div_eq_mul_inv]
          rw [← Finset.sum_mul]
          ring

theorem real_sum_cyclicAPSum_sq_eq_intCast_sum
    (f : Fin N → ℤ) (k D : ℕ) :
    (∑ i ∈ Finset.range D, ∑ a : Fin N,
        (((cyclicAPSum f k a (i + 1)) ^ 2 : ℤ) : ℝ))
      =
    (((∑ i ∈ Finset.range D, ∑ a : Fin N,
        (cyclicAPSum f k a (i + 1)) ^ 2 : ℤ)) : ℝ) := by
  have houter :
      (Int.castRingHom ℝ)
        (∑ i ∈ Finset.range D, ∑ a : Fin N,
          (cyclicAPSum f k a (i + 1)) ^ 2)
        =
      ∑ i ∈ Finset.range D,
        (Int.castRingHom ℝ)
          (∑ a : Fin N, (cyclicAPSum f k a (i + 1)) ^ 2) :=
    map_sum (Int.castRingHom ℝ)
      (fun i => ∑ a : Fin N, (cyclicAPSum f k a (i + 1)) ^ 2)
      (Finset.range D)
  symm
  change
    (Int.castRingHom ℝ)
      (∑ i ∈ Finset.range D, ∑ a : Fin N,
        (cyclicAPSum f k a (i + 1)) ^ 2)
      =
    ∑ i ∈ Finset.range D, ∑ a : Fin N,
      (Int.castRingHom ℝ) ((cyclicAPSum f k a (i + 1)) ^ 2)
  rw [houter]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hinner :
      (Int.castRingHom ℝ)
        (∑ a : Fin N, (cyclicAPSum f k a (i + 1)) ^ 2)
        =
      ∑ a : Fin N,
        (Int.castRingHom ℝ) ((cyclicAPSum f k a (i + 1)) ^ 2) :=
    map_sum (Int.castRingHom ℝ)
      (fun a : Fin N => (cyclicAPSum f k a (i + 1)) ^ 2)
      Finset.univ
  rw [hinner]

theorem sum_expect_cyclicAPSum_upper_range
    (f : Fin N → ℤ)
    (hpm : ∀ x, f x = -1 ∨ f x = 1)
    {k D : ℕ}
    (hk : 1 ≤ k)
    (hsmall : ∀ i ∈ Finset.range D, ∀ a : Fin N,
      ¬ wraps (N := N) k a (i + 1) →
        |cyclicAPSum f k a (i + 1)| < 2) :
    (∑ i ∈ Finset.range D,
        Finset.univ.expect fun a : Fin N =>
          (((cyclicAPSum f k a (i + 1)) ^ 2 : ℤ) : ℝ))
      ≤ (D : ℝ)
        + (((k : ℝ) ^ 2 - 1) * ((k - 1 : ℕ) : ℝ)
          * ((((D : ℤ) * (D + 1 : ℤ) / 2 : ℤ) : ℝ))) / (N : ℝ) := by
  have hZ := second_moment_upper_range (N := N) f hpm (k := k) (D := D) hk hsmall
  have hR :
      (∑ i ∈ Finset.range D, ∑ a : Fin N,
        (((cyclicAPSum f k a (i + 1)) ^ 2 : ℤ) : ℝ))
      ≤ (D : ℝ) * (N : ℝ)
        + (((k : ℝ) ^ 2 - 1) * ((k - 1 : ℕ) : ℝ)
          * ((((D : ℤ) * (D + 1 : ℤ) / 2 : ℤ) : ℝ))) := by
    rw [real_sum_cyclicAPSum_sq_eq_intCast_sum]
    have hZcast :
        (((∑ i ∈ Finset.range D, ∑ a : Fin N,
          (cyclicAPSum f k a (i + 1)) ^ 2 : ℤ)) : ℝ)
          ≤
        (((D : ℤ) * (N : ℤ)
          + (((k : ℤ) ^ 2 - 1) * ((k - 1 : ℕ) : ℤ)
            * ((D * (D + 1) / 2 : ℕ) : ℤ))) : ℝ) := by
      exact_mod_cast hZ
    simpa using hZcast
  rw [sum_expect_cyclicAPSum_eq_inv_card_mul_sum]
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (Nat.pos_of_neZero N)
  calc
    (N : ℝ)⁻¹ *
      (∑ i ∈ Finset.range D, ∑ a : Fin N,
        (((cyclicAPSum f k a (i + 1)) ^ 2 : ℤ) : ℝ))
        ≤ (N : ℝ)⁻¹ *
          ((D : ℝ) * (N : ℝ)
            + (((k : ℝ) ^ 2 - 1) * ((k - 1 : ℕ) : ℝ)
              * ((((D : ℤ) * (D + 1 : ℤ) / 2 : ℤ) : ℝ)))) := by
          exact mul_le_mul_of_nonneg_left hR (by positivity)
    _ = (D : ℝ)
        + (((k : ℝ) ^ 2 - 1) * ((k - 1 : ℕ) : ℝ)
          * ((((D : ℤ) * (D + 1 : ℤ) / 2 : ℤ) : ℝ))) / (N : ℝ) := by
          field_simp [ne_of_gt hNpos]

end FinZModBridge

/-- Real-valued version of the report's wrap-error term after setting `D = 2*k`. -/
noncomputable def wrapUpperReal (k N : ℝ) : ℝ :=
  1 + ((k ^ 2 - 1) * (k - 1) * (2 * k + 1)) / (2 * N)

/-- Real-valued Fejér lower bound after setting `D = 2*k`. -/
noncomputable def fejerLowerDTwoKReal (k : ℝ) : ℝ :=
  (k + 1) / 4

theorem upper_lt_lower_of_threshold_real
    {k N : ℝ}
    (hk : 3 < k)
    (hNpos : 0 < N)
    (hN :
      2 * ((k ^ 2 - 1) * (k - 1) * (2 * k + 1)) / (k - 3) < N) :
    wrapUpperReal k N < fejerLowerDTwoKReal k := by
  have hkden : 0 < k - 3 := by linarith
  have hN_ne : N ≠ 0 := ne_of_gt hNpos
  have hmain :
      2 * ((k ^ 2 - 1) * (k - 1) * (2 * k + 1)) < N * (k - 3) := by
    rw [div_lt_iff₀ hkden] at hN
    simpa [mul_comm, mul_left_comm, mul_assoc] using hN
  unfold wrapUpperReal fejerLowerDTwoKReal
  field_simp [hN_ne]
  nlinarith [hmain]

theorem average_bounds_incompatible_real
    {k N A : ℝ}
    (hk : 3 < k)
    (hNpos : 0 < N)
    (hN :
      2 * ((k ^ 2 - 1) * (k - 1) * (2 * k + 1)) / (k - 3) < N)
    (hlo : fejerLowerDTwoKReal k ≤ A)
    (hhi : A ≤ wrapUpperReal k N) :
    False := by
  have hlt := upper_lt_lower_of_threshold_real (k := k) (N := N) hk hNpos hN
  linarith

section FinalSynthesis

variable {N : ℕ} [NeZero N]

theorem int_two_mul_succ_div_two_real (k : ℕ) :
    ((((2 * k : ℤ) * (2 * k + 1 : ℤ)) / 2 : ℤ) : ℝ)
      = (k : ℝ) * (2 * k + 1 : ℝ) := by
  have hZ :
      (((2 * k : ℤ) * (2 * k + 1 : ℤ)) / 2 : ℤ)
        = (k : ℤ) * (2 * k + 1 : ℤ) := by
    rw [show (2 * k : ℤ) * (2 * k + 1 : ℤ) =
        ((k : ℤ) * (2 * k + 1 : ℤ)) * 2 by ring]
    exact Int.mul_ediv_cancel ((k : ℤ) * (2 * k + 1 : ℤ)) (by norm_num : (2 : ℤ) ≠ 0)
  rw [hZ]
  norm_num

theorem average_cyclicAPSum_upper_dTwoK_natSub
    (f : Fin N → ℤ)
    (hpm : ∀ x, f x = -1 ∨ f x = 1)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hsmall : ∀ i ∈ Finset.range (2 * k), ∀ a : Fin N,
      ¬ wraps (N := N) k a (i + 1) →
        |cyclicAPSum f k a (i + 1)| < 2) :
    ((2 * k : ℝ)⁻¹ *
      ∑ i ∈ Finset.range (2 * k),
        Finset.univ.expect fun a : Fin N =>
          (((cyclicAPSum f k a (i + 1)) ^ 2 : ℤ) : ℝ))
      ≤ 1 + (((k : ℝ) ^ 2 - 1) * ((k - 1 : ℕ) : ℝ)
        * (2 * (k : ℝ) + 1)) / (2 * (N : ℝ)) := by
  have hupper := sum_expect_cyclicAPSum_upper_range
    (N := N) f hpm (k := k) (D := 2 * k) hk hsmall
  have hpos : 0 < (2 * k : ℝ) := by
    exact_mod_cast (Nat.mul_pos (by decide : 0 < 2) (lt_of_lt_of_le (by decide : 0 < 1) hk))
  have hmul := mul_le_mul_of_nonneg_left hupper (inv_nonneg.mpr hpos.le)
  calc
    ((2 * k : ℝ)⁻¹ *
      ∑ i ∈ Finset.range (2 * k),
        Finset.univ.expect fun a : Fin N =>
          (((cyclicAPSum f k a (i + 1)) ^ 2 : ℤ) : ℝ))
        ≤ (2 * k : ℝ)⁻¹ *
            (((2 * k : ℕ) : ℝ)
              + ((((k : ℝ) ^ 2 - 1) * ((k - 1 : ℕ) : ℝ)
                * ((((((2 * k : ℕ) : ℤ) * (((2 * k : ℕ) : ℤ) + 1))
                  / 2 : ℤ) : ℝ))) / (N : ℝ))) := hmul
    _ = 1 + (((k : ℝ) ^ 2 - 1) * ((k - 1 : ℕ) : ℝ)
        * (2 * (k : ℝ) + 1)) / (2 * (N : ℝ)) := by
          have htri :
              ((((((2 * k : ℕ) : ℤ) * (((2 * k : ℕ) : ℤ) + 1)) / 2 : ℤ) : ℝ))
                = (k : ℝ) * (2 * k + 1 : ℝ) := by
            simpa using int_two_mul_succ_div_two_real k
          have htwok : (((2 * k : ℕ) : ℝ)) = 2 * (k : ℝ) := by norm_num
          rw [htri, htwok]
          have hNpos : 0 < (N : ℝ) := by
            exact_mod_cast (Nat.pos_of_neZero N)
          field_simp [ne_of_gt hpos, ne_of_gt hNpos]

theorem average_cyclicAPSum_upper_dTwoK
    (f : Fin N → ℤ)
    (hpm : ∀ x, f x = -1 ∨ f x = 1)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hsmall : ∀ i ∈ Finset.range (2 * k), ∀ a : Fin N,
      ¬ wraps (N := N) k a (i + 1) →
        |cyclicAPSum f k a (i + 1)| < 2) :
    ((2 * k : ℝ)⁻¹ *
      ∑ i ∈ Finset.range (2 * k),
        Finset.univ.expect fun a : Fin N =>
          (((cyclicAPSum f k a (i + 1)) ^ 2 : ℤ) : ℝ))
      ≤ wrapUpperReal (k : ℝ) (N : ℝ) := by
  have h := average_cyclicAPSum_upper_dTwoK_natSub
    (N := N) f hpm (k := k) hk hsmall
  have hsub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk]
    norm_num
  simpa [wrapUpperReal, hsub, mul_comm, mul_left_comm, mul_assoc] using h

theorem no_small_nonwrapping_ap_of_threshold
    (f : Fin N → ℤ)
    (hpm : ∀ x, f x = -1 ∨ f x = 1)
    {k : ℕ}
    (hk : (3 : ℝ) < (k : ℝ))
    (hN :
      2 * (((k : ℝ) ^ 2 - 1) * ((k : ℝ) - 1) * (2 * (k : ℝ) + 1))
        / ((k : ℝ) - 3) < (N : ℝ))
    (hsmall : ∀ i ∈ Finset.range (2 * k), ∀ a : Fin N,
      ¬ wraps (N := N) k a (i + 1) →
        |cyclicAPSum f k a (i + 1)| < 2) :
    False := by
  have hkNat : 3 < k := by exact_mod_cast hk
  have hkpos : 0 < k := by omega
  have hkone : 1 ≤ k := by omega
  let A : ℝ :=
    (2 * k : ℝ)⁻¹ *
      ∑ i ∈ Finset.range (2 * k),
        Finset.univ.expect fun a : Fin N =>
          (((cyclicAPSum f k a (i + 1)) ^ 2 : ℤ) : ℝ)
  have hlo : fejerLowerDTwoKReal (k : ℝ) ≤ A := by
    simpa [A, fejerLowerDTwoKReal] using
      average_cyclicAPSum_lower_dTwoK (N := N) f hpm hkpos
  have hhi : A ≤ wrapUpperReal (k : ℝ) (N : ℝ) := by
    simpa [A] using
      average_cyclicAPSum_upper_dTwoK (N := N) f hpm (k := k) hkone hsmall
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (Nat.pos_of_neZero N)
  exact average_bounds_incompatible_real
    (k := (k : ℝ)) (N := (N : ℝ)) hk hNpos hN hlo hhi

theorem exists_nonwrap_cyclicAPSum_abs_ge_two_of_threshold
    (f : Fin N → ℤ)
    (hpm : ∀ x, f x = -1 ∨ f x = 1)
    {k : ℕ}
    (hk : (3 : ℝ) < (k : ℝ))
    (hN :
      2 * (((k : ℝ) ^ 2 - 1) * ((k : ℝ) - 1) * (2 * (k : ℝ) + 1))
        / ((k : ℝ) - 3) < (N : ℝ)) :
    ∃ i ∈ Finset.range (2 * k), ∃ a : Fin N,
      ¬ wraps (N := N) k a (i + 1) ∧
        2 ≤ |cyclicAPSum f k a (i + 1)| := by
  by_contra hnone
  have hsmall : ∀ i ∈ Finset.range (2 * k), ∀ a : Fin N,
      ¬ wraps (N := N) k a (i + 1) →
        |cyclicAPSum f k a (i + 1)| < 2 := by
    intro i hi a hnowrap
    have hnot : ¬ 2 ≤ |cyclicAPSum f k a (i + 1)| := by
      intro hge
      exact hnone ⟨i, hi, a, hnowrap, hge⟩
    omega
  exact no_small_nonwrapping_ap_of_threshold
    (N := N) f hpm (k := k) hk hN hsmall

theorem exists_ordinaryAPSum_abs_ge_two_of_threshold
    (f : Fin N → ℤ)
    (hpm : ∀ x, f x = -1 ∨ f x = 1)
    {k : ℕ}
    (hk : (3 : ℝ) < (k : ℝ))
    (hN :
      2 * (((k : ℝ) ^ 2 - 1) * ((k : ℝ) - 1) * (2 * (k : ℝ) + 1))
        / ((k : ℝ) - 3) < (N : ℝ)) :
    ∃ i ∈ Finset.range (2 * k), ∃ a : Fin N,
      ∃ hnowrap : ¬ wraps (N := N) k a (i + 1),
        2 ≤ |ordinaryAPSum f k a (i + 1) hnowrap| := by
  rcases exists_nonwrap_cyclicAPSum_abs_ge_two_of_threshold
      (N := N) f hpm (k := k) hk hN with
    ⟨i, hi, a, hnowrap, hge⟩
  refine ⟨i, hi, a, hnowrap, ?_⟩
  have heq := cyclicAPSum_eq_ordinaryAPSum (N := N) f k a (i + 1) hnowrap
  simpa [heq] using hge

end FinalSynthesis

/-- The real threshold appearing in the HTML report. -/
noncomputable def htmlThresholdReal (k : ℕ) : ℝ :=
  2 * (((k : ℝ) ^ 2 - 1) * ((k : ℝ) - 1) * (2 * (k : ℝ) + 1))
    / ((k : ℝ) - 3)

/-- The report's displayed integer upper bound, `floor(threshold) + 1`. -/
noncomputable def htmlBoundNat (k : ℕ) : ℕ :=
  Nat.floor (htmlThresholdReal k) + 1

theorem htmlBoundNat_pos (k : ℕ) :
    0 < htmlBoundNat k := by
  simp [htmlBoundNat]

theorem htmlThresholdReal_lt_htmlBoundNat (k : ℕ) :
    htmlThresholdReal k < (htmlBoundNat k : ℝ) := by
  simpa [htmlBoundNat, Nat.cast_add, Nat.cast_one]
    using Nat.lt_floor_add_one (htmlThresholdReal k)

theorem htmlThresholdReal_lt_of_htmlBoundNat_le
    {k N : ℕ}
    (hN : htmlBoundNat k ≤ N) :
    htmlThresholdReal k < (N : ℝ) := by
  have hfloor := htmlThresholdReal_lt_htmlBoundNat k
  have hNreal : (htmlBoundNat k : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  exact lt_of_lt_of_le hfloor hNreal

theorem exists_ordinaryAPSum_abs_ge_two_of_htmlBoundNat_le
    {N : ℕ} [NeZero N]
    (f : Fin N → ℤ)
    (hpm : ∀ x, f x = -1 ∨ f x = 1)
    {k : ℕ}
    (hk : 5 ≤ k)
    (hN : htmlBoundNat k ≤ N) :
    ∃ i ∈ Finset.range (2 * k), ∃ a : Fin N,
      ∃ hnowrap : ¬ wraps (N := N) k a (i + 1),
        2 ≤ |ordinaryAPSum f k a (i + 1) hnowrap| := by
  have hkReal : (3 : ℝ) < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 3 < 5) hk)
  have hThreshold :
      2 * (((k : ℝ) ^ 2 - 1) * ((k : ℝ) - 1) * (2 * (k : ℝ) + 1))
        / ((k : ℝ) - 3) < (N : ℝ) := by
    simpa [htmlThresholdReal] using
      htmlThresholdReal_lt_of_htmlBoundNat_le (k := k) (N := N) hN
  exact exists_ordinaryAPSum_abs_ge_two_of_threshold
    (N := N) f hpm (k := k) hkReal hThreshold

/--
For a fixed coloring on `[0, N)`, there is a non-wrapping ordinary `k`-term
AP with discrepancy at least `2`.
-/
def hasLargeOrdinaryAPAt
    (k N : ℕ) (hNpos : 0 < N) (f : Fin N → ℤ) : Prop :=
  letI : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  ∃ d : ℕ, 0 < d ∧ ∃ a : Fin N,
    ∃ hnowrap : ¬ wraps (N := N) k a d,
      2 ≤ |ordinaryAPSum f k a d hnowrap|

/--
The formalized `N(k,2)` property used here: every `±1` coloring of `[0, N)`
has a non-wrapping ordinary `k`-term AP whose sum has absolute value at least
`2`.
-/
def erdos176Good (k N : ℕ) : Prop :=
  ∃ hNpos : 0 < N,
    ∀ f : Fin N → ℤ,
      (∀ x, f x = -1 ∨ f x = 1) →
        hasLargeOrdinaryAPAt k N hNpos f

theorem erdos176Good_of_htmlBoundNat_le
    {k N : ℕ}
    (hk : 5 ≤ k)
    (hN : htmlBoundNat k ≤ N) :
    erdos176Good k N := by
  have hNpos : 0 < N := lt_of_lt_of_le (htmlBoundNat_pos k) hN
  refine ⟨hNpos, ?_⟩
  intro f hpm
  haveI : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  rcases
    exists_ordinaryAPSum_abs_ge_two_of_htmlBoundNat_le
      (N := N) f hpm (k := k) hk hN with
    ⟨i, _hi, a, hnowrap, hge⟩
  refine ⟨i + 1, Nat.succ_pos i, a, hnowrap, ?_⟩
  exact hge

theorem exists_erdos176Good (k : ℕ) (hk : 5 ≤ k) :
    ∃ N : ℕ, erdos176Good k N :=
  ⟨htmlBoundNat k, erdos176Good_of_htmlBoundNat_le (k := k) hk le_rfl⟩

/-- The formal `N(k,2)` value for the property above, for `k >= 5`. -/
noncomputable def erdos176Number (k : ℕ) (hk : 5 ≤ k) : ℕ := by
  classical
  exact Nat.find (exists_erdos176Good k hk)

theorem erdos176Number_spec (k : ℕ) (hk : 5 ≤ k) :
    erdos176Good k (erdos176Number k hk) := by
  classical
  unfold erdos176Number
  exact Nat.find_spec (exists_erdos176Good k hk)

theorem erdos176Number_le_htmlBoundNat (k : ℕ) (hk : 5 ≤ k) :
    erdos176Number k hk ≤ htmlBoundNat k := by
  classical
  unfold erdos176Number
  exact Nat.find_min' (exists_erdos176Good k hk)
    (erdos176Good_of_htmlBoundNat_le (k := k) (N := htmlBoundNat k) hk le_rfl)

theorem erdos176Number_le_report_bound (k : ℕ) (hk : 5 ≤ k) :
    erdos176Number k hk
      ≤ Nat.floor
        (2 * (((k : ℝ) ^ 2 - 1) * ((k : ℝ) - 1) * (2 * (k : ℝ) + 1))
          / ((k : ℝ) - 3)) + 1 := by
  simpa [htmlBoundNat, htmlThresholdReal] using
    erdos176Number_le_htmlBoundNat k hk

theorem erdos176Number_le_report_bound_expanded
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
          / ((k : ℝ) - 3)) + 1 := by
  classical
  let M := erdos176Number k hk
  refine ⟨M, ?_, ?_, ?_⟩
  · simpa [M, erdos176Good, hasLargeOrdinaryAPAt, wraps, ordinaryAPSum]
      using erdos176Number_spec k hk
  · intro N hN
    have hGood : erdos176Good k N := by
      simpa [erdos176Good, hasLargeOrdinaryAPAt, wraps, ordinaryAPSum] using hN
    simpa [M, erdos176Number] using
      (Nat.find_min' (exists_erdos176Good k hk) hGood)
  · simpa [M] using erdos176Number_le_report_bound k hk

/-- Public-facing name for the report's displayed bound. -/
noncomputable abbrev reportBound (k : ℕ) : ℕ :=
  htmlBoundNat k

/--
Public-facing name for the formalized `N(k,2)` quantity.

The theorem below only uses this for `k >= 5`.  For smaller `k`, this harmlessly
defaults to `0` so that the notation does not need to carry a proof argument.
-/
noncomputable def N176 (k : ℕ) : ℕ :=
  if hk : 5 ≤ k then erdos176Number k hk else 0

theorem N176_eq_erdos176Number (k : ℕ) (hk : 5 ≤ k) :
    N176 k = erdos176Number k hk := by
  simp [N176, hk]

/-- Public-facing final theorem: `N176(k)` is at most the report's bound. -/
theorem N176_le_report_bound (k : ℕ) (hk : 5 ≤ k) :
    N176 k ≤ reportBound k := by
  rw [N176_eq_erdos176Number k hk]
  exact erdos176Number_le_htmlBoundNat k hk

theorem N176_le_report_bound_explicit (k : ℕ) (hk : 5 ≤ k) :
    N176 k
      ≤ Nat.floor
        (2 * (((k : ℝ) ^ 2 - 1) * ((k : ℝ) - 1) * (2 * (k : ℝ) + 1))
          / ((k : ℝ) - 3)) + 1 := by
  simpa [reportBound, htmlBoundNat, htmlThresholdReal] using
    N176_le_report_bound k hk

/-- The report's wrap-error term after setting `D = 2*k`. -/
noncomputable def wrapUpper (k N : ℚ) : ℚ :=
  1 + ((k ^ 2 - 1) * (k - 1) * (2 * k + 1)) / (2 * N)

/-- The Fejér lower bound from the report after setting `D = 2*k`. -/
noncomputable def fejerLowerDTwoK (k : ℚ) : ℚ :=
  (k + 1) / 4

/--
The purely algebraic part of the HTML proof attempt is correct.

If the cyclic AP second moment has lower bound `(k+1)/4` and the ordinary-AP
avoidance argument gives upper bound `wrapUpper k N`, then the report's
threshold makes the two bounds incompatible.
-/
theorem upper_lt_lower_of_threshold
    {k N : ℚ}
    (hk : 3 < k)
    (hNpos : 0 < N)
    (hN :
      2 * ((k ^ 2 - 1) * (k - 1) * (2 * k + 1)) / (k - 3) < N) :
    wrapUpper k N < fejerLowerDTwoK k := by
  have hkden : 0 < k - 3 := by linarith
  have hN_ne : N ≠ 0 := ne_of_gt hNpos
  have hkden_ne : k - 3 ≠ 0 := ne_of_gt hkden
  have hmain :
      2 * ((k ^ 2 - 1) * (k - 1) * (2 * k + 1)) < N * (k - 3) := by
    rw [div_lt_iff₀ hkden] at hN
    simpa [mul_comm, mul_left_comm, mul_assoc] using hN
  unfold wrapUpper fejerLowerDTwoK
  field_simp [hN_ne]
  nlinarith [hmain]

theorem average_bounds_incompatible
    {k N A : ℚ}
    (hk : 3 < k)
    (hNpos : 0 < N)
    (hN :
      2 * ((k ^ 2 - 1) * (k - 1) * (2 * k + 1)) / (k - 3) < N)
    (hlo : fejerLowerDTwoK k ≤ A)
    (hhi : A ≤ wrapUpper k N) :
    False := by
  have hlt := upper_lt_lower_of_threshold (k := k) (N := N) hk hNpos hN
  linarith

end Erdos176Lean
