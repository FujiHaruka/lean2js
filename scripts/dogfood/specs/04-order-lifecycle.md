# Spec: The lifecycle of an order

An order is in exactly one state:

- **draft** — being assembled
- **placed** at an instant
- **paid** — placed at one instant, paid at another
- **shipped** — paid at an instant, shipped at another, carrying a tracking number
- **delivered** — shipped at an instant, delivered at another, carrying a tracking number
- **cancelled** — with a reason and the instant it happened
- **refunded** — delivered at an instant, refunded at another, for an amount in yen

Every instant is epoch milliseconds, passed in by the caller.

The events are: place, pay, ship (carries a tracking number), deliver, cancel (carries a reason), refund (carries an amount).

1. Only these transitions are legal: draft to placed, placed to paid, paid to shipped, shipped to delivered, delivered to refunded, and cancel from draft, placed or paid.
2. Anything else is rejected with a message that names the state it was in and the event it got — "an order that has shipped cannot be cancelled".
3. **An instant may never go backwards.** An event whose instant is earlier than the latest instant recorded in the current state is rejected.
4. **Shipping needs a tracking number** that is not blank after trimming.
5. **A refund** is allowed only within 14 days of delivery, and the amount must be greater than zero and at most the order total, which is passed in.
6. There is a query side too: given a state, is the order still cancellable? Is it refundable at instant `now`, given the order total? What tracking number does it carry, if any?

Ship at least: the transition function, and the three queries. Prove claims a business person would recognise — for example that a shipped order can never be cancelled whatever the instant, that a refund above the order total is refused, that an event going back in time is refused.
