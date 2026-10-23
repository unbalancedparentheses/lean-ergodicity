# lean-ergodicity

Machine-checked proofs, in Lean 4 with Mathlib, of the mathematics behind ergodicity economics,
the Kelly criterion, volatility drag and insurance. It backs the
[One Path](https://federicocarrone.com/series/one-path/) series on federicocarrone.com:

- [Ergodicity, Explained](https://federicocarrone.com/series/one-path/ergodicity-explained/): `TimeAverage.lean`, `Ergodicity.lean`, `Coin.lean`
- [Volatility Drag](https://federicocarrone.com/series/one-path/volatility-drag/): `Jensen.lean`, `Recovery.lean`
- [The Kelly Criterion](https://federicocarrone.com/series/one-path/kelly-criterion/): `Kelly.lean`
- [Why Insurance Makes Both Sides Richer](https://federicocarrone.com/series/one-path/insurance/): `Insurance.lean`

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
| `CoinAlmostSure.lean` | The coin on an actual probability space of infinite fair coin flips (Mathlib's `Measure.infinitePi`): `coin_ae_wealth_tendsto_zero` proves that with probability one a player who bets everything every round ends with nothing, while expected wealth (21/20)ⁿ grows without bound. |
| `Leverage.lean` | Optimal leverage for geometric Brownian motion, from Peters' growth rate g(l) = r + l(μ − r) − l²σ²/2: the Kelly leverage (μ − r)/σ² maximizes it (`leverage_optimal`), twice Kelly earns exactly r (`growth_at_twice_kelly`), a fraction c of Kelly keeps c(2 − c) of the excess growth so half Kelly keeps three quarters (`growth_half_kelly`), and leverage beyond twice Kelly grows slower than cash. |
| `StPetersburg.lean` | Peters and Gell-Mann's St Petersburg game: the expected payout diverges (`stPetersburg_expected_payout_not_summable`), but for any fee below the player's wealth the expected change in log wealth is a convergent series (`stPetersburg_growth_summable`). |
| `Coin.lean` | The ×1.5 / ×0.6 coin: the expected factor is 21/20 and expected wealth (21/20)ⁿ grows without bound, while the time-average rate ½ log 1.5 + ½ log 0.6 is negative and a path with as many heads as tails shrinks as (9/10)ⁿ → 0. |
| `Coin.lean` | `additive_time_average_eq_ensemble`: for a bet that adds instead of multiplies, the two averages agree. |
| `Kelly.lean` | `kelly_optimal`: for a bet that returns 1 + u with probability p and 1 − d otherwise, the fraction f* = (pu − (1 − p)d) / (ud) maximizes p log(1 + uf) + (1 − p) log(1 − df). `kelly_growth_pos`: with an edge, the optimal growth is positive. |
| `Kelly.lean` | For the coin, f* = 1/4, betting a quarter grows at ½ log(81/80) > 0, and betting everything shrinks wealth. |
| `Insurance.lean` | Peters and Adamou's insurance result in its smallest form: an owner with wealth 2 facing a loss of 1 with probability ½, and an insurer with wealth 10. In expected wealth the contract is zero-sum for every fee, but every fee from 0.513 to 0.585 raises the time-average growth rate of both sides (`insurance_win_win`), and every such fee is above the expected loss. |
| `Recovery.lean` | A loss L needs a gain of exactly L / (1 − L) to recover, always more than L. A gain of x followed by a loss of x loses money. |
| `Ruin.lean` | As the worst outcome approaches zero, the expected log growth goes to −∞, whatever the other outcomes are. |

## Faithfulness notes

- **The time average is the almost-sure limit.** Ergodicity economics defines the time-average
  growth rate as the limit of (1/T) log(x(T)/x(0)) along a single trajectory. `TimeAverage.lean`
  proves that limit, almost surely, from Mathlib's strong law of large numbers. The finite results in
  `Ergodicity.lean` compute the matching expectations.
- **`Real.log 0 = 0`.** Lean gives the logarithm a junk value at zero, so ruin is stated as a limit
  (`Ruin.lean`) rather than by evaluating log 0.
- **Discrete time, and one continuous-time formula taken as given.** Deriving the growth rate of
  geometric Brownian motion (g = μ − σ²/2) needs Itô calculus, which Mathlib does not have yet.
  `volatility_drag` is the discrete-time statement with an explicit error bound. `Leverage.lean`
  takes Peters' continuous-time growth rate as its definition and proves everything else from it.

## Build

```
lake exe cache get
lake build
```

Lean `v4.35.0`, Mathlib `v4.35.0`.

## License

Apache 2.0.
