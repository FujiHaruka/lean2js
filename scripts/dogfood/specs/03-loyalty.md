# Spec: A loyalty balance that expires

Customers earn points on purchases, and the points expire. A balance is a list of *lots*; each lot records when it was earned (epoch milliseconds), when it expires (epoch milliseconds), and how many points are left in it.

1. **Earning.** A purchase of N yen earns floor(N / 100) points at the standard tier. A gold-tier customer earns 50% more: floor(N x 15 / 1000). A purchase that earns zero points adds no lot at all. A new lot expires 365 days after it is earned (a day is 86,400,000 ms).
2. **Usable balance** at an instant `now` is the sum of the points left in every lot whose expiry is strictly after `now`.
3. **Redeeming** n points at instant `now` consumes lots **earliest expiry first**; where two lots expire at the same instant, the one earned earlier goes first. A lot may be partly consumed. Expired lots are never consumed, and are dropped from the result.
4. If the usable balance is less than n, the redemption is refused and the balance is unchanged. Redeeming zero or fewer points is refused too.
5. A successful redemption returns how many points were actually taken from each lot — so the caller can show "500 from the lot expiring 2026-04-01" — together with the balance that remains.
6. **Expiry sweep**: given `now`, return the balance with expired lots removed, and a total of how many points were lost.

Time is always passed in by the caller as epoch milliseconds.

Ship at least: earning, the usable balance, the sweep, and the redemption. Prove claims a business person would recognise — for example that redeeming more than the usable balance changes nothing, that a sweep never increases the usable balance, that a 99 yen purchase earns nothing.
