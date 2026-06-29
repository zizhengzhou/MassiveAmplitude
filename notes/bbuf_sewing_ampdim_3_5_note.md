<!-- markdownlint-disable MD013 MD052 -->

# BBuf u f+ Sewing Note for the \bar B B u f_+ Sector

This note records the corrected sewing calculation for the sector
\[
(\bar B,B,u,f_+)=(1,2,3,4).
\]
The scan uses `QReplacement -> 2` internally.  The displayed formulas below
restore the physical labels after reduction, while keeping the right residual
amplitude \(A_R\) free of the formal \(Q\) label.

## Sector and Conventions

The heavy pair has spin \(1/2\).  The \(u_\mu\) leg is the massive spin-one leg
at position \(3\), and \(f_+\) is the positive-helicity massless vector at
position \(4\).

\[
\text{leftSpin}=\frac12,\qquad
\text{rightSpins}=\{1,1\},\qquad
\text{rightMass}=\{3\},\qquad
\text{rightPolarization}=\{1,0\}.
\]

The hard relative momentum is
\[
Q=p_1-p_2,
\]
the \(p_-\)-type combination in Eq.~\eqref{eq:momentum_decompose}.  It is
treated as the hard heavy-pair vector in the sewing construction.

The package output also uses reflected square labels.  In the paper-level
display we undo this bookkeeping by
\[
8\mapsto 1,\qquad 7\mapsto 2,\qquad 6\mapsto 3 .
\]

In these displays \(A_R\) denotes only the right residual structure.  It may
contain the right physical legs \(3,4\) and, in open channels, the formal
\(J\)-slot.  It must not contain formal \(Q\), nor the auxiliary labels
\(1,2\).  The formal \(Q\)-raising factor appears only when the transmitted
current has \(J_{12}>2s\).  For this spin-\(1/2\) sector, closed \(J_{12}=0\)
`Xhard`/`Xsoft` left rows therefore do not acquire
\(\langle QJ\rangle[QJ]\).

## Chiral Sorting Rule

The maintained code uses
\[
\nu_{\rm rel}=d_{\rm amp}-n_{\rm Xhard}-J_{12},
\]
where \(n_{\rm Xhard}\) is read from `SortData["Xhard"]`.

The current projected filtered call is

```wl
ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1},
  {3},
  4,
  {},
  su3ShapeList -> {},
  RightPolarizationFilter -> <|3 -> 1|>,
  ReturnProjectionData -> True,
  ReplaceQInFinalSymbolForm -> False
]["BasisByRelativeChiralOrder"]
```

and returns

```wl
<|
  2 -> {
    ab[3, Q]*sb[4, 7]*sb[4, 8]*sb[6, Q]
  },
  3 -> {
    ab[3, 4]*sb[4, 6]*sb[4, 7]*sb[4, 8],
    ab[1, 3]*ab[2, 3]*sb[3, 4]*sb[4, 6]
  }
|>
```

The two relative-order-3 rows are open \(J_{12}=1\) rows.  They are not
closed \(J_{12}=0\) `Xhard`/`Xsoft` rows.

The fixed-dimension rank checks are
\[
\operatorname{rank}M_{\rm CF}
\!=\!\operatorname{rank}M_{\rm sew}
\!=\!\operatorname{rank}M_{\rm joined}
\!=\!
\begin{cases}
2,& d_{\rm amp}=3,\\
3,& d_{\rm amp}=4,\\
4,& d_{\rm amp}=5,\\
5,& d_{\rm amp}=6.
\end{cases}
\]

## Fixed-Dimension Checks

The fixed-dimension span checks remain complete:

\[
\operatorname{rank}M_{\rm CF}
\!=\!\operatorname{rank}M_{\rm sew}
\!=\!\operatorname{rank}M_{\rm joined}
\!=\!
\begin{cases}
2,& d_{\rm amp}=3,\\
3,& d_{\rm amp}=4,\\
4,& d_{\rm amp}=5,\\
5,& d_{\rm amp}=6.
\end{cases}
\]

The corresponding `section_5_2` chiral-order witness, using dimensions
\(3,4,5,6\) together, gives the maintained grouping:

| relative order | count | sources |
| --- | ---: | --- |
| 2 | 4 | two `ampDim=3,J=1` rows and two split `ampDim=4,J=2` rows |
| 3 | 6 | one `ampDim=4,J=1` row, three `ampDim=5,J=2` rows, and two `ampDim=6,J=3` rows |
| 4 | 3 | one `ampDim=5,J=1` row and two `ampDim=6,J=2` rows |

## Raw Verification Data

The relevant scripts and logs are:

* `tests/section_5_2_bbuf_reproduce.wls`
* `tests/section_5_2_chiral_order_reproduce.wls`
* `tests/bbuf_right_residual_no_q_regression.wls`
* `logs/section_5_2_relative_chiral_orders.log`
