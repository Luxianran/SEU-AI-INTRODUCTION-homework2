# Euclid 定理：素数没有上界（Lean 4 形式化）

主文件：[`Euclid.lean`](Euclid.lean)

## 定理

```lean
theorem exists_prime_gt (n : Nat) : ∃ p, Prime p ∧ n < p
theorem primes_unbounded (B : Nat) : ∃ p, Prime p ∧ B < p
theorem no_upper_bound : ¬ ∃ B, ∀ p, Prime p → p ≤ B
```

也就是说：对任意自然数 `n`，都存在大于 `n` 的素数；素数集合没有上界。

## 证明思路

采用 Euclid 的经典构造：

1. 令 `N = n! + 1`。
2. 证明每个 `N ≥ 2` 都有素因子 `p`（对 `N` 做强归纳）。
3. 若 `p ≤ n`，则 `p ∣ n!`；又 `p ∣ N`，所以
   `p ∣ N - n! = 1`，这与 `p` 是素数矛盾。
4. 因此 `n < p`。

## 验证

本文件只依赖 Lean 4 核心库，不需要 Mathlib。已用 Lean 4.35.0 验证：

```bash
./.lean-download/lean-4.35.0-linux/bin/lean Euclid.lean
```

若本机已安装 Lean，也可以直接：

```bash
lean Euclid.lean
```

编译无错误、无 `sorry`。`#print axioms` 显示只依赖 Lean 的标准经典公理
`propext`、`Classical.choice`、`Quot.sound`。

## 关于 `Prime`

Lean 4 核心库不含数论中的 `Nat.Prime` 和阶乘，因此文件在 `Euclid` 命名空间中
给出了标准定义：

```lean
def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p
```

这与 Mathlib 中 `Nat.Prime` 的定义一致。若在 Mathlib 环境下使用，可直接把
`Euclid.Prime` 视为 `Nat.Prime`。
