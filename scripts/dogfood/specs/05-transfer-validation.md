# Spec: Validating a domestic bank transfer before it is sent

A transfer instruction carries: a bank code, a branch code, an account number, an account holder name, an amount, and a three-letter currency code.

1. **Bank code**: exactly 4 characters, all digits.
2. **Branch code**: exactly 3 characters, all digits.
3. **Account number**: exactly 7 characters, all digits, and not all zeros.
4. **Account holder name**: after trimming, between 1 and 30 characters. Upper-case it for transmission. An empty name after trimming is an error.
5. **Currency code**: exactly 3 characters, all A-Z upper case.
6. **Amount** is given in the currency's minor units, together with how many minor digits that currency has (0 for JPY, 2 for USD). It must be greater than zero, and at most 10,000,000 yen worth — for JPY that is 10,000,000 minor units, for a 2-digit currency 1,000,000,000.
7. **Report every problem, not just the first.** The caller shows the whole list beside the form.
8. On success, return the normalised instruction, plus a display string for the destination written `1234-567-8901234` (bank, branch and account joined with hyphens), and the amount formatted for a human: 10000 in JPY becomes `"10,000"`; 123456 in a 2-minor-digit currency becomes `"1,234.56"`.

There are no regular expressions available here.

Ship at least: each field check, the whole-instruction validation that collects every error, and the display string. Prove claims a business person would recognise — for example that a valid instruction produces no errors at all, that an amount of zero is always rejected, that the destination display string always carries exactly two hyphens.
