# A residue obstruction to larger-meld Nine Gates variants

Consider one suit with consecutive ranks `0, ..., R-1`. Fix a meld size
`k >= 2`. A meld is either `k` identical tiles or one tile of each of `k`
consecutive ranks. A winning hand consists of melds and one **eye** of `p`
identical tiles. Tile multiplicities are unrestricted.

A full-sided wait is a hand for which drawing any rank gives a winning
hand. The number of melds is fixed automatically by the hand size.

This experiment was motivated by the residue-count viewpoint in
[Xue and Zhong, *Beyond Nine Gates*](https://arxiv.org/abs/2611.06944).
Their paper concerns three-tile melds and a two-tile eye; the variant here
changes those sizes.

## Obstruction theorem

**If `k >= 4` and `R >= k`, a full-sided wait requires `p = 1 (mod k)`.
Its tile counts in the `k` rank-residue classes must also be equal modulo `k`.**

Consequently, neither an ordinary two-tile eye nor a `(k-1)`-tile eye permits
a full-sided wait for any `k >= 4`, regardless of how many melds are used.
The three-tile game escapes this obstruction.

### Proof

Work in `(Z/kZ)^k`. Let `e_i` denote the standard basis vectors and `1`
the vector with every coordinate equal to one. Let `C_i` count the tiles
whose ranks are `i (mod k)` in the waiting hand.

Each consecutive meld contributes `1` to this count vector, and each
identical meld contributes zero modulo `k`. Since every residue occurs
among the ranks, full-sidedness gives, for each draw residue `i`, an eye
residue `f(i)` and a scalar `a_i` satisfying

```math
C + e_i - p e_{f(i)} = a_i \mathbf{1}.
```

The function `f` is injective. Otherwise subtracting the equations for
distinct draws `i, j` with `f(i)=f(j)` gives
`e_i-e_j = (a_i-a_j) 1`. A coordinate outside `{i,j}` forces the scalar
to be zero; the `i` coordinate then says `1=0`, a contradiction.

Now subtract the equations for any distinct `i,j`:

```math
e_i-e_j-p(e_{f(i)}-e_{f(j)})=(a_i-a_j)\mathbf{1}.
```

Choose distinct coordinates `r,s` outside `{f(i),f(j)}`; this is possible
because `k >= 4`. At those coordinates, the left side is respectively
`(e_i-e_j)_r` and `(e_i-e_j)_s`. If their common value were nonzero,
`r,s` would have to be `i,j` in some order, forcing that common value to
be both `1` and `-1`. This is impossible modulo `k >= 4`.
Thus `a_i=a_j` always, and

```math
e_i-e_j=p(e_{f(i)}-e_{f(j)}).
```

The nonzero `i` and `j` coordinates on the left force
`{f(i),f(j)}={i,j}`. For fixed `i`, choose two distinct other indices
`j,l`. Then `f(i)` belongs to both `{i,j}` and `{i,l}`, so `f(i)=i`.
The `i` coordinate of the displayed equality now gives `p=1 (mod k)`.
Substituting into the original equation gives `C=a_i 1`, as claimed.

### Sharpness and scope

For any positive `p=1 (mod k)`, full-sided waits do exist for suitable
meld counts. Take `p-1` tiles of every rank and add one identical meld at
rank zero. After any draw, use the drawn tile and `p-1` tiles of the same
rank as the eye. Every remaining multiplicity is a nonnegative multiple
of `k`, so the remainder decomposes into identical melds.

This proves existence for some meld count, not for every prescribed
meld count. The assumptions that the meld and sequence lengths agree
and that all `k` residue classes can be drawn are essential to the proof.

### A construction with a fixed meld count

If `k >= 2` is even, `R >= k`, and `p = 1 + k*q` with `q >= 0`, there
is a full-sided wait whose winning decompositions use exactly

```math
m = q(k-1) + \left\lceil\frac{R-k}{2}\right\rceil
```

melds. This is an existence bound; optimality is not claimed. For example,
four-tile melds and a five-tile eye admit the six-rank waiting hand
`(0,5,5,5,5,0)`, with four melds after every draw. More generally, for
`k=4` and `p=5`, the construction uses `ceil(R/2)+1` winning melds.

Here is the construction for even `R`, with ranks numbered from zero.
Choose the `k` possible eye ranks

```math
E = \{1,3,\ldots,k-1\}\;\cup\;\{R-k,R-k+2,\ldots,R-2\}.
```

They contain one representative of every residue modulo `k`. Put `k*q`
identical tiles at every rank in `E`, then add one consecutive meld at
each odd start `1,3,...,R-k-1`. Write `D_s` for the consecutive meld
starting at `s`. The identity

```math
D_{s+1}-D_s = e_{s+k}-e_s
```

lets a chain of shifts transfer the drawn tile to an eye rank in the same
residue class. For an odd draw, right-shift a chain connecting the left
eye to the draw; for an even draw, left-shift a chain connecting the draw
to the right eye.
Combining the transferred tile with the eye's `k*q` tiles leaves
`q*(k-1)` identical melds and `(R-k)/2` consecutive melds. The Lean proof
uses exact multiset equalities, with nonnegative tiles throughout.

For odd `R`, use the even construction on `R+1` ranks. Its extra last rank
has zero waiting tiles, and every certificate for a draw below `R` stays
inside the original suit. This gives the ceiling in the formula above.

The same endpoint-transfer argument extends to **every `k >= 2`**, including
odd meld sizes. Set `L = R-k`. Choose the leftmost rank in each odd residue
class as an eye and the rightmost rank in each even residue class. Add a
consecutive meld at start `s=t+1` whenever `0 <= t < L` and `(t mod k)` is
even. The exact winning meld count is

```math
m = q(k-1)
  + \left\lfloor\frac{L}{k}\right\rfloor\left\lceil\frac{k}{2}\right\rceil
  + \left\lceil\frac{L\bmod k}{2}\right\rceil.
```

For even `k` this reduces to the earlier formula. For example, five-tile
melds with a six-tile eye admit a full-sided wait on sixteen ranks with
eleven winning melds. This construction also does not claim optimality.
In particular, when `q=0` the eye is a single tile, so the empty hand
already gives a zero-meld full-sided wait for any number of ranks.

[`constructions.py`](constructions.py) returns the hand and an explicit
winning certificate for each draw. Tests reconstruct all 280,560 draw
certificates for `k=2,...,15`, `k <= R <= 100`, and `q=0,...,3`.
The unbounded result is proved in Lean below. Tile multiplicities remain
unrestricted; this is not a result about live waits under a four-copy rule.

### Lower bounds and exact minima for short suits

For `k >= 4`, `R >= k`, and `p = 1+k*q` with `q > 0`, let
`d = min(R-k, k)` be the number of residue classes with at least two
drawable ranks. Every full-sided wait needs at least

```math
q(k-1) + \left\lceil\frac{d}{2}\right\rceil
```

winning melds. The periodic construction attains the bound for every
`k <= R <= 2*k`. For example, seven-tile melds and an eight-tile eye on
fourteen ranks require exactly ten melds. With `q=0`, the empty hand
attains the minimum of zero for every suit length.

The winning eye uses the draw's residue, so every class needs at least
`p-1` waiting tiles. With `s` melds above the resulting capacity bound
`q*(k-1)`, the class excesses over `p-1` sum to `k*s`. If their
common remainder is `t` modulo `k`, then `t <= s`, and at most `s-t`
classes have excess greater than `t`.

Suppose `2*s < d`. More than `2*t` repeated classes then have exactly
`p-1+t` tiles. A repeated class must already contain a whole eye.
Otherwise two distinct draws would each need to complete their own eye,
requiring `2*(p-1)` waiting tiles in the class. This already rules out
`t=0`. With fewer than `2*(p-1)` tiles, the existing eye is also the only
possible eye in that class after a draw. Removing it leaves `t < k`
tiles in the draw class.
Therefore the winning decomposition uses exactly `t` consecutive melds.

Call ranks at least `k` high. A consecutive meld contributes a high
tile in an initial segment of the residue classes, so the high counts
from the consecutive melds decrease weakly across residues. In a
repeated class `i` with excess `t`, let `l_i` count the high tiles
left after removing its eye. A low draw in class `i` leaves `l_i`
high tiles and a high draw leaves `l_i+1`. A draw in a different
class leaves a baseline count `b_i` equal to the number of high
tiles after removing `p-1` copies of the eye rank. In all three
cases, reducing the high count modulo `k` discards any identical
melds.

For `i < j`, a low draw in `i` gives `b_j <= l_i`, and a high
draw in `j` gives `l_j+1 <= b_i`. Thus `l_i+b_i` strictly decreases
and lies between 0 and `2*t-1`, so there can be at most `2*t` such
classes. This contradicts the count from the excesses.

[`LowerBounds.lean`](MeldSizeObstruction/LowerBounds.lean) proves the
general bound as `FullWait.meld_count_lower_with_repeated_residues`.
The theorem `minimum_meld_count_of_le_twice` also supplies the attaining
hand for `k <= R <= 2*k`.

For even `k`, the first extra rank beyond `2*k` forces one more meld.
At the previous minimum, the excess budget and the count bound force
all `k` classes to have the same excess `t = k/2`. Their strictly
decreasing values `l_i+b_i` then fill exactly the integers from
`k-1` down to 0. Drawing rank `2*k` leaves that tile in the melds,
in a class with fewer than `k` tiles. It must be in a consecutive
meld whose start is above `k`. This meld gives a high tile to the
last class, contradicting its zero baseline count.

For even `k` and `R >= 2*k+1`, the lower bound is therefore
`q*(k-1)+k/2+1`. The periodic construction attains it at both
`R = 2*k+1` and `R = 2*k+2`, as proved by
`minimum_meld_count_even_beyond_twice`.

## Computational checks

Python 3.10 or later; no third-party dependencies:

```sh
python3 -m unittest -v
python3 explore.py --max-meld-size 12
```

`residue_candidates` computes the **necessary modular condition**, not a
classification of actual waits. Tests compare it with direct exhaustive
quantification for `k=2,...,5`, and check the theorem's predicted residue
candidates through `k=24`. The argument above, rather than the finite
checks, covers unbounded `k`.

The code also searches exact winning decompositions. A separate checker
reconstructs the tile counts from each returned certificate. Tests include
ordinary Nine Gates, positive examples with `p=1 (mod k)`, and the failed
four-tile analogue `(4,1,1,1,1,1,1,4)` with a three-tile eye. That analogue
wins only on ranks `1,4,5,8` (written here with one-based ranks).

## Lean verification

[MeldSizeObstruction.lean](MeldSizeObstruction.lean) formalizes the algebraic
core in Lean 4.35.0 with Mathlib:

- `draw_eye_rigidity` works over any nontrivial commutative ring with
  `1 != -1`, with at least four coordinates.
- `residue_compatible_iff` classifies the necessary modular condition:
  it holds exactly when `p=1` and all class counts agree modulo `k`.

[MeldSizeObstruction/Hands.lean](MeldSizeObstruction/Hands.lean) connects
the equations to literal finite multisets of tiles. `Melds` builds identical
and consecutive melds, `WinningHand` requires an exact decomposition into
melds and an eye, and `FullWait` requires a win after every draw in the suit.
The hand and its draws have ranks below `R`; exact multiset equality keeps
every tile in a winning decomposition within that same range.

- `FullWait.obstruction` and `FullWait.eye_mod_one` prove the obstruction
  for actual hands, including equality of the residue-class counts.
- `not_fullWait_pair` and `not_fullWait_pred` rule out two-tile and
  `(k-1)`-tile eyes.
- `fullWait_uniform` verifies the explicit construction for every eye size
  `p = 1 + k*q`.
- `exists_fullWait_iff` proves that, for `k >= 4` and `R >= k`, full-sided
  waits exist exactly when `p = 1 (mod k)`. This allows the meld count to
  vary; particular hands and prescribed meld counts still require their
  own decompositions.

Tile multiplicities are unrestricted in both the Lean model and Python
search. Mathlib's `Nat.multiset_Ico_map_mod` supplies the counting fact for
consecutive melds: every rank residue occurs exactly once.

[`Construction.lean`](MeldSizeObstruction/Construction.lean) proves the
multiset identity for shifting a sequence, telescopes it along a chain,
and gives `fullWait_of_transfers`: endpoint transfers plus a finite set
of eye blocks suffice to construct a full-sided wait.
[`EvenConstruction.lean`](MeldSizeObstruction/EvenConstruction.lean)
instantiates that argument with alternating sequence starts:

- `fullWait_sparse` proves full-sidedness for every even `k >= 2`,
  every `R >= k`, and every `q >= 0`, with eye size `1+k*q`.
- `sparseHand_card` computes the exact hand size, hence fixes the winning
  meld count to the displayed formula.
- `exists_fullWait_even` packages the actual hand, full-sidedness, and
  exact size in one existence theorem.

[`SparseEyes.lean`](MeldSizeObstruction/SparseEyes.lean) supplies the shared
eye ranks and their residue and boundary properties.
[`PeriodicConstruction.lean`](MeldSizeObstruction/PeriodicConstruction.lean)
extends the construction to arbitrary meld sizes:

- `fullWait_periodic` proves the actual hand wins after every draw.
- `card_periodicStarts` proves the closed count of selected sequences.
- `periodicMeldCount_even` proves the even-size simplification.
- `periodicHand_card` and `exists_fullWait_periodic` give the exact hand
  size and the corresponding existence theorem.

With the pinned Lean toolchain installed:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`
for the algebraic core, the hand-level obstruction, the constructive
existence theorems, and the existence converse. `Audit.lean` checks forbidden-eye
cases, a five-tile eye with four-tile melds, and all nine draws of ordinary
Nine Gates through explicit winning decompositions. It also checks that
the three-coordinate, characteristic-two, and short-suit exceptions are
real, as well as odd suit lengths, the zero-meld boundary, the smallest
even meld size, and the periodic construction for odd meld sizes.

## Continuous verification

GitHub Actions builds the pinned Lean library, checks `Audit.lean` with
warnings treated as errors, enforces the axiom allowlist over the whole
library, and runs the Python certificate checks. The workflow runs on
pushes to `main`, pull requests, and manual dispatches.

To run the enforcing axiom audit locally after installing the pinned Lean
toolchain:

```sh
bash scripts/audit-axioms.sh
```

This builds a pinned version of
[`axiom-audit`](https://github.com/leanprover-community/axiom-audit) using
the project's toolchain. It imports every module under
`MeldSizeObstruction/`, including modules outside the root file's import
closure, and fails if a declaration uses any axiom beyond `propext`,
`Classical.choice`, and `Quot.sound`. The audit complements the Lean build;
it checks axiom dependencies in the compiled environment.
