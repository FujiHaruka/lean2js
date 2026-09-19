# Spec: Shipping and handling for a consumer web shop

An order is a list of items. Each item has a product name, a unit price in yen, a quantity, and a unit weight in grams.

1. **Item subtotal** is unit price x quantity. **Order subtotal** is the sum over items.
2. **Shipping weight** is the sum of (unit weight x quantity) over all items.
3. **Base shipping fee**, by total weight:
   - up to and including 2,000 g -> 500 yen
   - up to and including 5,000 g -> 800 yen
   - up to and including 10,000 g -> 1,200 yen
   - above 10,000 g -> 1,200 yen, plus 300 yen for every additional 5,000 g or part thereof
     (so 10,001 g -> 1,500; 15,000 g -> 1,500; 15,001 g -> 1,800)
4. **Regional surcharge.** Some prefectures cost more to reach. The caller passes the surcharge table (prefecture name -> surcharge in yen) together with the destination prefecture. A prefecture that is not in the table carries no surcharge.
5. **Free shipping.** If the order subtotal is 10,000 yen or more, the base shipping fee is waived. The regional surcharge is still charged.
6. **Cash on delivery.** If the customer pays on delivery, add a handling fee of 1% of (order subtotal + shipping + surcharge), rounded **up** to the next 10 yen, capped at 660 yen.
7. The whole thing returns the breakdown — subtotal, shipping, surcharge, COD fee, total — or refuses with a message when: the order has no items; any quantity is less than 1; any unit price is negative; any unit weight is negative.

Ship at least: the order subtotal, the shipping weight, the base fee, the surcharge lookup, the COD fee, and the whole breakdown. Prove claims a business person would recognise — for example that free shipping really does zero the base fee, that the COD fee never exceeds 660 yen, that an empty order is refused.
