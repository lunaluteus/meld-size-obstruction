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

The Lean portion covers the residue equations. The reduction from tile
hands is the counting argument above; exact winning decompositions are
checked by Python.

With the pinned Lean toolchain installed:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The axiom audit reports `propext`, `Classical.choice`, and `Quot.sound`.
`Audit.lean` also checks concrete forbidden-eye cases and witnesses that
the three-coordinate and characteristic-two exceptions are real.
