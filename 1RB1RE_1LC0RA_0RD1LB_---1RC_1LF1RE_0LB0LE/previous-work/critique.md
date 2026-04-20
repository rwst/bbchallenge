# Critique of BMO1 prior analyses

Assuming the macro rules at the top of `machine.wiki`
```
A(a,b) → A(a-b, 4b+2)   if a > b
A(a,b) → A(2a+1, b-a)   if a < b
A(a,b) → Halt           if a = b
Start  A(1, 2)
```
are a faithful model of the TM, I review the rest of `machine.wiki` and of
`BMO1-Bard.pdf`. The two write-ups attack the same iteration from dual sides:
the wiki iterates a *backward* map in (slope, intercept) space, Bard
homogenises and reduces to a *forward* 1D map on the interval.

## 1. Dynamical reduction: ln(a/b) chaotic map (wiki §1)

Dropping the +1/+2 constants is a heuristic only; the simplified model is even
trivially non-halting (wiki §"Simplified Model" correctly notes that it is
trapped in (a,b) ≡ (0,4), (4,0) mod 8 after two steps). So the chaotic F(x)
map, and the invariant density used to get the growth rate ≈ 0.15097694, are
evidence but not a proof.

## 2. Backward (m,b) approach (wiki §2)

### Algebra
The backward map
```
(m,b) → (m/(m+4), (b-2)/(m+4))   from the x>y branch
(m,b) → (2m+1, b+m)               from the x<y branch
```
checks out: substitute `y_{n+1} = m x_{n+1} + b` into the forward map and
solve. The halting condition "(1,2) lies on line" becomes
**m + b = 2** in (m,b) space, and the seed is (m,b)=(1,0) (the line y=x).

### Location 1 (limit (1,1))

Andrew's closed form for `(<^n, >)` is
`((2^{n+1}-1)/(2^{n+1}+3), (2^{n+1}-n-4)/(2^{n+1}+3))`. I verified this by
induction. Its limit is (1,1), exactly on m+b=2, and the finite values never
equal (1,1). ✓

Racheline's elementary argument "m>b is invariant" is correct:
- Under the x>y branch: m'−b' = (m−b+2)/(m+4) > 0 whenever m > b.
- Under the x<y branch: m'−b' = m−b+1 > 0 whenever m > b.
Starting from (1,0) with m>b, the invariant holds, so the limit (m,b)=(1,1)
is never reached in finite time.

**Gap.** m>b alone does not prove the trajectory never meets m+b=2 anywhere
near (1,1); it only prevents m=b=1 itself. The closed form handles the
specific path `(<^n,>)` but other paths could in principle approach (1,1).
The wiki does not quite prove Location 1 is safe for *all* approach paths —
only for the specific path shown to approach (1,1).

### Location 2 (limit (13/7, 4/21))

Racheline's propagation of the invariants m>0, b>−2/3 through `(<,<,>,<)` is
correct and I reproduced each step. The endpoint bound
m₄+b₄ > 13/7 + 4/21 = 43/21 ≈ 2.048 > 2 is robust: it holds for *any* path
that ends in `(<,<,>,<)`, not just the asserted `(>^n, <^2, >, <)`. Since
m>0, b>−2/3 is itself an invariant (verified for both branches starting from
(1,0)), this yields a genuine lemma:

> Any generated (m,b) whose last four operations are (<,<,>,<) lies above
> m+b=43/21 > 2.

What is *not* proved is that all (m,b) near (13/7, 4/21) arise from such a
suffix. The wiki acknowledges this is empirical. For a full argument one
would need either a structural lemma on which suffixes can appear near that
limit, or a covering argument.

### Location 3 (fractal near m ≈ 1.76)

The wiki honestly reports this is a fractal-looking set where the closest
above/below points alternate erratically with n. The candidate closed form
for the family `(<^4,>,<,>,<)` is
```
(m_f,b_f) = ((104 m_n + 119)/(56 m_n + 69),
             (23 m_n + b_n + 12)/(56 m_n + 69))
```
I did not re-derive this but the form (Möbius in m_n, affine in b_n) is
consistent with an iterated composition of the two branches. The essential
claim — that this set has a full-measure cluster on both sides of m+b=2 —
is empirical and unresolved. This is the real open door.

## 3. Bard PDF

### Homogenisation (p.1)
`(x_n+y_n+z_n)=1` rescaling. I verified each form:
- x>y branch: divisor 3−2x (= sum of (x−y)+(4y+2z)+z, using 1−x−y=z).
- x<y branch: divisor 1+z.
- 2-variable form after z=1−x−y substitution matches.

Start (1,2) with common factor 4 gives (1/4, 1/2, 1/4). ✓

### 1D limit z=0 (p.1–2)
At z=0, y=1−x, so
- x > y ⇔ x > 1/2, giving `x' = (2x−1)/(3−2x)`;
- x < y ⇔ x < 1/2, giving `x' = 2x`.

**z_n → 0 is asserted but not fully argued.** I checked: z' = z/(3−2x) (≤1,
strict <1 since x<1) on one branch, z' = z/(1+z) (<1 when z>0) on the other.
So {z_n} is strictly decreasing and positive, hence convergent; if the limit
were L>0, the contraction factor on the left branch tends to 1/(1+L)<1, so
infinitely many left-branch steps force z_n→0. Finitely many left-branch
steps is easy to rule out from the original (a,b) iteration (y grows without
bound), so z_n→0 holds. This should be spelt out.

### Density of halting points (p.2–3)
"Derivative > 1 everywhere" is *almost* right:
- Left branch `2x`: derivative 2.
- Right branch: derivative `4/(3−2x)²`. At x=1/2 this equals 1, not >1; it
  is >1 strictly for x>1/2.

This boundary case does not break the density argument because a single
point has zero length. The `L_{n+2} ≥ 2 L_n` claim I checked by cases
(LL, LR, RL, RR) for compositions; it holds.

### Fraction iteration & odd-denominator lemma (p.3)
`(u,v) → (2u−v, −2u+3v)` (right) or `(2u,v)` (left). Lemma: v odd ⇒ next v
odd.
- Right: −2u + 3v ≡ 0 + v ≡ 1 (mod 2). ✓
- Left: v unchanged. ✓

And halt needs 2u=v, so v even; so odd v ⇒ never halts. Elegant and
correct.

The cycle caveat (what if a rational orbit with even v loops forever without
halting?) is real but, as Bard notes, tangential to BMO1.

### Same-trajectory lemma (p.4)
> For any (x,y) there is α ∈ [0,1] in the 1D system taking the same branch
> sequence, and halting iff (x,y) halts.

The branch-matching half is fine: each finite branch sequence prescribes a
nested interval I_n ⊂ (0,1); the sequence of I_n has lengths → 0 (from the
uniform expansion), so ∩I_n is a single point α, and this α reproduces the
sequence.

The **halting** half is stated but not argued. It is morally correct:
- If (x,y) halts at step k, the 2D branches through k−1 determine an
  interval I_{k−1}; the map f^{k−1} on I_{k−1} is a continuous bijection
  onto (0,1), so there is a unique α ∈ I_{k−1} with f^{k−1}(α)=1/2, i.e.
  α halts at step k.
- If (x,y) never halts, the infinite branch sequence selects a unique α by
  nested intervals, and α then has an infinite branch sequence (no halt).

But the PDF's one-paragraph proof covers only branch matching and glosses
over the halt case. It should construct α differently in the two cases or
argue continuity, as above.

### Reduction of BMO1 (p.4–5)
The Stern–Brocot search between bounds yields an α_∞ ≈ 0.3621250257705563
matching (1/4, 1/2)'s trajectory, with no rational of denominator ≤ 10⁵⁰
found. Bard conjectures α_∞ irrational.

**This reduces BMO1 to an irrationality statement about a specific
fixed-point of an explicit dynamical system, but gives no route to prove
it.** There is no visible structural reason (as there would be for e.g. a
value defined by continued-fraction-like algebraic identities) to expect
the irrationality proof to be tractable.

## 4. Summary

| Claim | Status |
|-------|--------|
| Backward (m,b) algebra | correct |
| Location 1 closed form + m>b invariant | correct but only rules out one approach path to (1,1) |
| Location 2, Racheline's suffix bound | proved rigorously as a suffix-lemma |
| Location 2, "all nearby (m,b) come from this suffix" | empirical, unproved |
| Location 3 | unresolved; the real obstacle |
| Bard homogenisation and 1D limit | correct, modulo z_n→0 which needs a short argument |
| 1D density of halting points | correct |
| Odd-denominator halting test | correct |
| Same-trajectory lemma | correct idea, halt case needs the nested-intervals argument made explicit |
| BMO1 reduction to irrationality of α_∞ | correct reduction, but α_∞ is defined only implicitly |

Neither write-up proves BMO1 loops. The wiki analysis localises the
difficulty to a fractal region near m ≈ 1.76; Bard transports it to the
irrationality of a single implicit constant. The two formulations are dual
views of the same obstacle: a single bit of information (halt vs loop) sits
behind a dense, fractal-like set of rational witnesses on one side and an
unidentified real number on the other. Any further progress likely needs a
*structural* argument — perhaps an invariant measure / entropy / ergodic
bound for the 1D map that forces the orbit of 1/4 to avoid {1/2} — rather
than more backward enumeration or Stern–Brocot search.
