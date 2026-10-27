/-
# Euclid's theorem: there are arbitrarily large primes

For every natural number `n` we produce a prime `p` with `n < p`.
Following Euclid, take `N = n! + 1` and a prime divisor `p` of `N`.
If `p ≤ n`, then `p ∣ n!`, hence `p ∣ N - n! = 1`, impossible.

This file is self-contained: it only uses Lean 4's core library, and
therefore does not require Mathlib.  The predicate `Prime` below is the
standard definition of primality (Mathlib calls it `Nat.Prime`).
-/

namespace Euclid

/-- The standard predicate "`p` is prime". -/
def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

/-- A prime is not equal to `1`. -/
theorem Prime.ne_one {p : Nat} (hp : Prime p) : p ≠ 1 := by
  intro h
  have h2 : 2 ≤ 1 := by simpa [h] using hp.1
  exact absurd h2 (by decide : ¬ 2 ≤ 1)

/-- The factorial function, defined locally so that no imports are needed. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- The factorial is positive. -/
theorem fact_pos (n : Nat) : 0 < fact n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih => exact Nat.mul_pos (Nat.succ_pos n) ih

/-- If `0 < m ≤ n`, then `m` divides `n!`. -/
theorem dvd_fact_of_le {m n : Nat} (hm : 0 < m) (h : m ≤ n) : m ∣ fact n := by
  induction n with
  | zero =>
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero h
    exact absurd hm0 (Nat.ne_of_gt hm)
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · have hmn : m ≤ n := Nat.le_of_lt_succ hlt
      have hd : m ∣ fact n := ih hmn
      exact Nat.dvd_trans hd (Nat.dvd_mul_left (fact n) (n + 1))
    · have hm_eq : m = n + 1 := Nat.le_antisymm h hge
      rw [hm_eq]
      exact Nat.dvd_mul_right (n + 1) (fact n)

/-- Every natural number at least `2` has a prime divisor.

Proved by strong induction: a number which is not prime has a proper
divisor `m ≥ 2`; by the induction hypothesis `m` has a prime divisor,
which also divides the original number. -/
theorem exists_prime_dvd : ∀ N, 2 ≤ N → ∃ p, Prime p ∧ p ∣ N := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro hN
    by_cases hprime : Prime N
    · exact ⟨N, hprime, Nat.dvd_refl N⟩
    · have hproper : ∃ m, m ∣ N ∧ m ≠ 1 ∧ m ≠ N := by
        by_cases h : ∃ m, m ∣ N ∧ m ≠ 1 ∧ m ≠ N
        · exact h
        · apply False.elim
          apply hprime
          constructor
          · exact hN
          · intro m hm
            by_cases hm1 : m = 1
            · exact Or.inl hm1
            · right
              by_cases hmN : m = N
              · exact hmN
              · exact False.elim (h ⟨m, hm, hm1, hmN⟩)
      obtain ⟨m, hmdvd, hm1, hmN⟩ := hproper
      have hNpos : 0 < N := Nat.lt_of_lt_of_le (by decide : 0 < 2) hN
      have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hmdvd hNpos
      have hm2 : 2 ≤ m := by
        cases m with
        | zero => exact absurd hmpos (Nat.lt_irrefl 0)
        | succ m' =>
          cases m' with
          | zero => exact absurd rfl hm1
          | succ m'' => exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m''))
      have hle : m ≤ N := Nat.le_of_dvd hNpos hmdvd
      have hlt : m < N := Nat.lt_of_le_of_ne hle hmN
      obtain ⟨p, hp, hpdvd⟩ := ih m hlt hm2
      exact ⟨p, hp, Nat.dvd_trans hpdvd hmdvd⟩

/-- **Euclid's theorem**: for every `n` there is a prime `p > n`. -/
theorem exists_prime_gt (n : Nat) : ∃ p, Prime p ∧ n < p := by
  let N := fact n + 1
  have hN : 2 ≤ N := by
    dsimp [N]
    exact Nat.succ_le_succ (fact_pos n)
  obtain ⟨p, hp, hpdvd⟩ := exists_prime_dvd N hN
  refine ⟨p, hp, ?_⟩
  by_cases hnp : n < p
  · exact hnp
  · have hle : p ≤ n := Nat.le_of_not_gt hnp
    have hp_pos : 0 < p := Nat.lt_of_lt_of_le (by decide : 0 < 2) hp.1
    have hpn : p ∣ fact n := dvd_fact_of_le hp_pos hle
    have hsub : p ∣ N - fact n := Nat.dvd_sub hpdvd hpn
    have hsub' : p ∣ (fact n + 1) - fact n := by simpa [N] using hsub
    have hone : (fact n + 1) - fact n = 1 := Nat.add_sub_cancel_left (fact n) 1
    have h1 : p ∣ 1 := by simpa [hone] using hsub'
    exact False.elim (hp.ne_one (Nat.dvd_one.mp h1))

/-- The primes are unbounded: no natural number bounds all primes. -/
theorem primes_unbounded (B : Nat) : ∃ p, Prime p ∧ B < p :=
  exists_prime_gt B

/-- There is no upper bound for the set of primes. -/
theorem no_upper_bound : ¬ ∃ B, ∀ p, Prime p → p ≤ B := by
  intro h
  obtain ⟨B, hB⟩ := h
  obtain ⟨p, hp, hpB⟩ := exists_prime_gt B
  exact (Nat.not_le_of_gt hpB) (hB p hp)

end Euclid
