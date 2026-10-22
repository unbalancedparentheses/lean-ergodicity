# lean-ergodicity

Machine-checked proofs, in Lean 4 with Mathlib, of the mathematics behind ergodicity economics,
the Kelly criterion and volatility drag. It backs two essays on
[federicocarrone.com](https://federicocarrone.com): *Ergodicity, Explained* and *Volatility Drag*,
and the longer [Finance Is Geometry](https://federicocarrone.com/series/leptokurtic/at-the-core-of-finance-lies-geometry-in-the-end-its-all-jensens-inequality/).

Every result is proved. There are no `sorry`s, and each theorem depends only on Lean's standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).

## What is proved

Distributions are finite: a set of outcomes with nonnegative weights that sum to one.

| File | Result |
|---|---|
| `Jensen.lean` | `expected_log_le_log_expected`: E[log X] ≤ log E[X] for X > 0, strict exactly when X varies (`expected_log_lt_log_expected_iff`). |
| `Jensen.lean` | `volatility_drag`: for \|R\| < 1, E[log(1 + R)] = μ − σ²/2 − μ²/2 up to an error of at most E[\|R\|³ / (1 − \|R\|)]. |
| `Ergodicity.lean` | Over n independent rounds, expected wealth is (E[X])ⁿ (`expected_wealth_eq`) while the expected log of wealth is n · E[log X] (`expected_log_wealth_eq`). |
| `Ergodicity.lean` | `time_average_lt_ensemble`: if a bet can return two different factors, E[log X] < log E[X]. The growth rate one person lives is below the growth rate of the average. |
| `TimeAverage.lean` | `time_average_growth_ae`: along almost every trajectory, (1/n) log W_n → E[log G], by the strong law of large numbers (pairwise independent, identically distributed factors). Increments of log wealth are the ergodic observable for multiplicative growth. |
| `TimeAverage.lean` | `ae_wealth_tendsto_zero`: if E[log G] < 0, almost every trajectory goes to zero, however large E[G] is. `ae_wealth_tendsto_atTop`: if E[log G] > 0, almost every trajectory grows without bound. |
| `Coin.lean` | The ×1.5 / ×0.6 coin: the expected factor is 21/20 and expected wealth (21/20)ⁿ grows without bound, while the time-average rate ½ log 1.5 + ½ log 0.6 is negative and a path with as many heads as tails shrinks as (9/10)ⁿ → 0. |
| `Coin.lean` | `additive_time_average_eq_ensemble`: for a bet that adds instead of multiplies, the two averages agree. |
| `Kelly.lean` | `kelly_optimal`: for a bet that returns 1 + u with probability p and 1 − d otherwise, the fraction f* = (pu − (1 − p)d) / (ud) maximizes p log(1 + uf) + (1 − p) log(1 − df). `kelly_growth_pos`: with an edge, the optimal growth is positive. |
| `Kelly.lean` | For the coin, f* = 1/4, betting a quarter grows at ½ log(81/80) > 0, and betting everything shrinks wealth. |
| `Recovery.lean` | A loss L needs a gain of exactly L / (1 − L) to recover, always more than L. A gain of x followed by a loss of x loses money. |
| `Ruin.lean` | As the worst outcome approaches zero, the expected log growth goes to −∞, whatever the other outcomes are. |

## Faithfulness notes

- **The time average is the almost-sure limit.** Ergodicity economics defines the time-average
  growth rate as the limit of (1/T) log(x(T)/x(0)) along a single trajectory. `TimeAverage.lean`
  proves that limit, almost surely, from Mathlib's strong law of large numbers. The finite results in
  `Ergodicity.lean` compute the matching expectations.
- **`Real.log 0 = 0`.** Lean gives the logarithm a junk value at zero, so ruin is stated as a limit
  (`Ruin.lean`) rather than by evaluating log 0.
- **Discrete time.** The continuous-time results (geometric Brownian motion, g = μ − σ²/2 exactly)
  need Itô calculus, which Mathlib does not have yet. `volatility_drag` is the discrete-time
  statement with an explicit error bound.

## Build

```
lake exe cache get
lake build
```

Lean `v4.35.0`, Mathlib `v4.35.0`.

## License

Apache 2.0.
